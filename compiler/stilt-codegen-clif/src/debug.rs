//! What debuggers need of compiled code (goal debuggable-builds): for each function, where in the
//! source each stretch of its machine code comes from, and where each named local lives while
//! it is live. [`piece`] writes that as the function's DWARF once it is compiled, and
//! [`assemble`] puts the pieces of a program's functions together, which `stilt build` puts in
//! its object ([`sections`]) and the JIT in an image it gives debuggers through the GDB JIT
//! interface ([`jit`]).

mod assemble;
mod encode;
pub(crate) mod jit;
pub(crate) mod piece;
pub(crate) mod sections;
#[cfg(test)]
mod tests;
mod types;

use std::collections::HashMap;
use std::sync::Arc;

use cranelift_codegen::ir::{
    Block, BlockArg, Function as ClifFunction, RelSourceLoc, SourceLoc, StackSlot, Value, ValueDef,
    ValueLabel, ValueLabelAssignments, ValueLabelStart,
};
use cranelift_codegen::isa::TargetIsa;
use cranelift_codegen::isa::unwind::{UnwindInfo, systemv};
use cranelift_codegen::{CompiledCode, LabelValueLoc};
use cranelift_module::{DataId, FuncId};
use stilt_mir::mir::{Const, Function, Local, Operand, Rvalue, Shown, Stmt, Terminator};

/// What debuggers need of one compiled function, which its DWARF piece is written from.
#[derive(Clone, Debug)]
pub(crate) struct Facts {
    pub(crate) id: FuncId,
    /// The function's name, as `stilt_mir` prints it, such as `main.fib`.
    pub(crate) name: String,
    /// The size of its machine code, in bytes.
    pub(crate) size: u32,
    /// Where each stretch of its code comes from, in the order of the code.
    pub(crate) rows: Vec<Row>,
    pub(crate) vars: Vec<Var>,
    /// Where the function saves the registers it changes, which a debugger reads to find the
    /// caller's registers.
    pub(crate) unwind: Option<systemv::UnwindInfo>,
}

/// The start of a stretch of code that comes from one place in the source.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Row {
    /// The offset in the function's code.
    pub(crate) offset: u32,
    /// The index of the file among the program's files.
    pub(crate) file: u32,
    pub(crate) line: u32,
    pub(crate) col: u32,
}

/// A local the source names, with where it lives.
#[derive(Clone, Debug)]
pub(crate) struct Var {
    pub(crate) name: Arc<str>,
    pub(crate) shown: Shown,
    pub(crate) param: bool,
    /// Where it lives, for each stretch of code that it is live in, by offsets in the code.
    pub(crate) ranges: Vec<(u32, u32, Place)>,
    /// Its value, for a local that only ever holds a constant, which Cranelift makes again at
    /// each use rather than keeping it anywhere.
    pub(crate) constant: Option<Constant>,
}

/// The value of a local that only ever holds a constant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Constant {
    Word(u64),
    /// The address of an object of static data, such as a string literal.
    Data(DataId),
}

/// The constant each named local of `f` holds, for those that only ever hold one, `data`
/// giving the static data of a constant object.
pub(crate) fn constants(
    f: &Function,
    mut data: impl FnMut(&Const) -> Result<DataId, String>,
) -> Result<Vec<Option<Constant>>, String> {
    let mut defs: Vec<(usize, Option<&Const>)> = vec![(0, None); f.locals.len()];
    for p in &f.params {
        defs[p.local.0 as usize].0 += 1;
    }
    for block in &f.blocks {
        for stmt in &block.stmts {
            if let Stmt::Assign(l, r) = stmt {
                let d = &mut defs[l.0 as usize];
                d.0 += 1;
                d.1 = match r {
                    Rvalue::Use(Operand::Const(c)) => Some(c),
                    _ => None,
                };
            }
        }
        if let Terminator::Call { dest, raised, .. } = &block.term {
            for l in dest
                .iter()
                .chain(raised.iter().flat_map(|(error, _)| error))
            {
                defs[l.0 as usize].0 += 2;
            }
        }
    }
    let mut out = Vec::with_capacity(f.locals.len());
    for (decl, &(count, c)) in f.locals.iter().zip(&defs) {
        let constant = match (decl.shown.is_some(), count, c) {
            (true, 1, Some(Const::Word(w))) => Some(Constant::Word(*w)),
            (true, 1, Some(c @ (Const::Str(_) | Const::Data(..)))) => {
                Some(Constant::Data(data(c)?))
            }
            _ => None,
        };
        out.push(constant);
    }
    Ok(out)
}

/// Where a word lives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Place {
    /// A register, by its DWARF number.
    Reg(u16),
    /// A word of the frame, at this offset from the canonical frame address: the stack
    /// pointer before the call.
    Frame(i64),
}

/// Gives each value its label, once the function is built. A label given while it is built
/// can land on a block parameter that building then makes an alias of another value, and
/// Cranelift drops the labels of aliases, so each goes to the value its alias stands for.
///
/// Cranelift gives no location to a label on a block parameter either, which a local's value
/// is when code branches between the value's definition and the local's, as the release of a
/// call's argument does after the call. So each value that flows into such a parameter takes
/// the label too.
pub(crate) fn label(func: &mut ClifFunction, labels: &[(Value, ValueLabel)]) {
    let incoming = incoming(func);
    let mut labelled = Vec::with_capacity(labels.len());
    for &(value, label) in labels {
        let value = func.dfg.resolve_aliases(value);
        labelled.push((value, label));
        let mut work = vec![value];
        let mut seen = vec![value];
        while let Some(v) = work.pop() {
            let ValueDef::Param(block, index) = func.dfg.value_def(v) else {
                continue;
            };
            for args in incoming.get(&block).into_iter().flatten() {
                let Some(&Some(a)) = args.get(index) else {
                    continue;
                };
                let a = func.dfg.resolve_aliases(a);
                if !seen.contains(&a) {
                    seen.push(a);
                    work.push(a);
                    labelled.push((a, label));
                }
            }
        }
    }
    let Some(all) = func.dfg.values_labels.as_mut() else {
        return;
    };
    for (value, label) in labelled {
        let start = ValueLabelStart {
            from: RelSourceLoc::default(),
            label,
        };
        match all
            .entry(value)
            .or_insert_with(|| ValueLabelAssignments::Starts(Vec::new()))
        {
            ValueLabelAssignments::Starts(starts) => starts.push(start),
            ValueLabelAssignments::Alias { .. } => {}
        }
    }
}

/// The values each branch passes to each block's parameters, by the block, with `None` for an
/// argument that isn't a value, such as the result of a `try_call`.
fn incoming(func: &ClifFunction) -> HashMap<Block, Vec<Vec<Option<Value>>>> {
    let mut out: HashMap<Block, Vec<Vec<Option<Value>>>> = HashMap::new();
    let dfg = &func.dfg;
    for block in func.layout.blocks() {
        let Some(inst) = func.layout.last_inst(block) else {
            continue;
        };
        for call in dfg.insts[inst].branch_destination(&dfg.jump_tables, &dfg.exception_tables) {
            let args = call
                .args(&dfg.value_lists)
                .map(|a| match a {
                    BlockArg::Value(v) => Some(v),
                    _ => None,
                })
                .collect();
            out.entry(call.block(&dfg.value_lists))
                .or_default()
                .push(args);
        }
    }
    out
}

/// What the translation of a function marked, which its facts read: the location words its
/// source locations index, its first source location, the constant each named local holds, if
/// it only ever holds one, and the slot of each named array held in memory, with its offset.
pub(crate) struct Marks<'a> {
    pub(crate) locs: &'a [u64],
    pub(crate) base: SourceLoc,
    pub(crate) constants: &'a [Option<Constant>],
    pub(crate) arrays: &'a [(Local, StackSlot, i32)],
}

/// The DWARF number of the frame pointer of `isa`'s target: x29 on aarch64, rbp on x86-64.
pub(crate) fn frame_pointer(isa: &dyn TargetIsa) -> u16 {
    if isa.name() == "aarch64" { 29 } else { 6 }
}

/// The facts of a function that `code` holds, `f` being its MIR.
pub(crate) fn facts(
    isa: &dyn TargetIsa,
    id: FuncId,
    f: &Function,
    code: &CompiledCode,
    marks: &Marks<'_>,
) -> Facts {
    let mut rows: Vec<Row> = Vec::new();
    for s in code.buffer.get_srclocs_sorted() {
        let loc = if s.loc.is_rel() {
            s.loc.as_rel().expand(marks.base)
        } else {
            s.loc.as_abs()
        };
        let Some(&word) = usize::try_from(loc.bits())
            .ok()
            .and_then(|i| marks.locs.get(i))
        else {
            continue;
        };
        let row = Row {
            offset: s.start,
            file: u32::try_from(word >> 44).unwrap_or(0),
            line: u32::try_from(word >> 20 & 0xff_ffff).unwrap_or(0),
            col: u32::try_from(word & 0xf_ffff).unwrap_or(0),
        };
        if rows
            .last()
            .is_none_or(|r| (r.file, r.line, r.col) != (row.file, row.line, row.col))
        {
            rows.push(row);
        }
    }
    Facts {
        id,
        name: f.name.to_string(),
        size: code.buffer.total_size(),
        rows,
        vars: vars(isa, f, code, marks),
        unwind: match code.create_unwind_info(isa) {
            Ok(Some(UnwindInfo::SystemV(info))) => Some(info),
            _ => None,
        },
    }
}

/// The label of the words that hold the bits of the local `l`'s floats ([`crate::floats`]): a
/// label of its own, since the range of a label's value ends where the next value given that
/// label starts, and a float and its word are live at once. Where both are, the location list
/// gives both places, which hold the same bits.
pub(crate) fn word_label(f: &Function, l: Local) -> ValueLabel {
    ValueLabel::from_u32(u32::try_from(f.locals.len() + l.0 as usize).unwrap_or(u32::MAX))
}

/// Where the values given `label` live, by ranges of offsets in the code.
fn places(isa: &dyn TargetIsa, code: &CompiledCode, label: ValueLabel) -> Vec<(u32, u32, Place)> {
    let Some(ranges) = code.value_labels_ranges.get(&label) else {
        return Vec::new();
    };
    ranges
        .iter()
        .filter_map(|r| {
            let place = match r.loc {
                LabelValueLoc::Reg(reg) => Place::Reg(isa.map_regalloc_reg_to_dwarf(reg).ok()?),
                LabelValueLoc::CFAOffset(offset) => Place::Frame(offset),
            };
            (r.start < r.end).then_some((r.start, r.end, place))
        })
        .collect()
}

/// Where an array held in memory lives, in its slot at `offset`: in the frame, throughout the
/// function's code.
fn in_frame(code: &CompiledCode, slot: StackSlot, offset: i32) -> Vec<(u32, u32, Place)> {
    let Some(frame) = code.buffer.frame_layout() else {
        return Vec::new();
    };
    // The slot's offset counts from the bottom of the frame, which lies `frame_to_fp_offset`
    // below the frame pointer, and the frame pointer 16 bytes below the canonical frame
    // address.
    let from_fp = i64::from(frame.stackslots[slot].offset) + i64::from(offset)
        - i64::from(frame.frame_to_fp_offset);
    vec![(0, code.buffer.total_size(), Place::Frame(from_fp - 16))]
}

/// The named locals of `f`, each with where it lives.
fn vars(isa: &dyn TargetIsa, f: &Function, code: &CompiledCode, marks: &Marks<'_>) -> Vec<Var> {
    let mut vars = Vec::new();
    for (i, decl) in f.locals.iter().enumerate() {
        let (Some(name), Some(shown)) = (&decl.name, &decl.shown) else {
            continue;
        };
        let local = Local(u32::try_from(i).unwrap_or(u32::MAX));
        let mut ranges = places(isa, code, ValueLabel::from_u32(local.0));
        ranges.extend(places(isa, code, word_label(f, local)));
        if let Some(&(_, slot, offset)) = marks.arrays.iter().find(|(l, ..)| *l == local) {
            ranges.extend(in_frame(code, slot, offset));
        }
        ranges.sort_by_key(|&(start, end, _)| (start, end));
        let param = f.params.iter().any(|p| p.local.0 as usize == i);
        vars.push(Var {
            name: (*name).into(),
            shown: shown.clone(),
            param,
            ranges,
            constant: marks.constants.get(i).copied().flatten(),
        });
    }
    vars
}
