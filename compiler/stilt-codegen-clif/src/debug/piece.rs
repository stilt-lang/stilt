//! The DWARF of one function, written once, when it is compiled, and kept with its code
//! ([`crate::reuse`]): its subprogram and its named locals, their location lists, its rows of
//! the line table and its call frame. A build puts the pieces of its functions side by side in
//! one unit ([`super::assemble`]), and fills in what each piece leaves open
//! ([`super::encode::Patch`]): the function's address, those of the data its constants point
//! to, and the offsets of its types and its location lists. The locations of each local are
//! offsets from the function's address, which a base address entry gives each list, so only
//! that entry depends on where the code is.

use std::sync::Arc;

use cranelift_codegen::isa::unwind::systemv::UnwindInfo;
use cranelift_module::{DataId, FuncId};
use gimli::constants as dw;
use gimli::write::{Address, CommonInformationEntry, DebugFrame, FrameTable};
use stilt_mir::mir::Shown;

use super::encode::{self, Bytes, Chunk, Patch, Writing};
use super::sections::{Relocating, Target};
use super::{Constant, Facts, Place, Var};

/// The DWARF of one function.
#[derive(Clone, Debug)]
pub(crate) struct Piece {
    pub(crate) id: FuncId,
    /// The size of its code, in bytes.
    pub(crate) size: u32,
    pub(crate) info: Chunk,
    pub(crate) loc: Chunk,
    pub(crate) line: Chunk,
    pub(crate) frame: Chunk,
    /// The types of its locals, each once, which its patches index.
    pub(crate) types: Arc<[Shown]>,
    /// The data its locals' constants point to, which its patches index.
    pub(crate) data: Vec<DataId>,
}

/// The line table's encoding: the default of DWARF's producers.
pub(crate) const LINE_BASE: i8 = -5;
pub(crate) const LINE_RANGE: u8 = 14;
pub(crate) const OPCODE_BASE: u8 = 13;

impl Piece {
    /// The DWARF of the function of `facts`, `fp` being the DWARF number of the frame
    /// pointer, which sits 16 bytes below the canonical frame address in every function, and
    /// `cie` the common information of the target's call frames.
    pub(crate) fn new(facts: &Facts, fp: u16, cie: Option<&CommonInformationEntry>) -> Self {
        let mut types: Vec<Shown> = Vec::new();
        let mut data = Vec::new();
        let mut loc = Writing::default();
        let info = info(facts, fp, &mut loc, (&mut types, &mut data));
        let frame = match (&facts.unwind, cie) {
            (Some(unwind), Some(cie)) => frame(unwind, cie),
            _ => Chunk::default(),
        };
        Self {
            id: facts.id,
            size: facts.size,
            info,
            loc: loc.finish(),
            line: line(facts),
            frame,
            types: types.into(),
            data,
        }
    }
}

/// The subprogram of the function and its locals, whose location lists go to `loc`, and whose
/// types and data go to `seen`.
fn info(f: &Facts, fp: u16, loc: &mut Writing, seen: (&mut Vec<Shown>, &mut Vec<DataId>)) -> Chunk {
    let (types, data) = seen;
    let mut w = Writing::default();
    let declared = f.rows.first();
    let codes = encode::SUBPROGRAM[usize::from(declared.is_some())];
    w.out.uleb(codes[usize::from(!f.vars.is_empty())]);
    w.out.string(&f.name);
    w.patch(Patch::Code(0));
    w.out.u32(f.size);
    let mut frame_base = Bytes::default();
    breg(&mut frame_base, fp, 16);
    exprloc(&mut w.out, &frame_base);
    if let Some(row) = declared {
        w.out.uleb(u64::from(row.file) + 1);
        w.out.uleb(u64::from(row.line));
    }
    let mut lists = Vec::new();
    for var in &f.vars {
        let ty = index_of(types, &var.shown);
        local(&mut w, var, ty, fp, (loc, &mut lists), data);
    }
    if !f.vars.is_empty() {
        w.out.u8(0);
    }
    w.finish()
}

/// The index of `item` in `list`, where it is added if it isn't there yet.
fn index_of<T: PartialEq + Clone>(list: &mut Vec<T>, item: &T) -> u32 {
    let k = list.iter().position(|x| x == item).unwrap_or_else(|| {
        list.push(item.clone());
        list.len() - 1
    });
    u32::try_from(k).unwrap_or(u32::MAX)
}

/// The location lists written so far, each with its offset, which a local whose list is the
/// same shares.
type Lists<'f> = Vec<(&'f [(u32, u32, Place)], u32)>;

/// A local of type `ty`: where it lives, by an expression that computes its value, if it only
/// ever holds a constant, or by a location list.
fn local<'f>(
    w: &mut Writing,
    var: &'f Var,
    ty: u32,
    fp: u16,
    (loc, lists): (&mut Writing, &mut Lists<'f>),
    data: &mut Vec<DataId>,
) {
    let codes = encode::LOCAL[usize::from(var.param)];
    let code = match (var.constant, var.ranges.is_empty()) {
        (Some(_), _) => codes[0],
        (None, false) => codes[1],
        (None, true) => codes[2],
    };
    w.out.uleb(code);
    w.out.string(&var.name);
    w.patch(Patch::Type(ty));
    match var.constant {
        // A location that computes the value, rather than a constant attribute, which gdb
        // leaves out of `info locals`.
        Some(Constant::Word(word)) => {
            let mut value = Bytes::default();
            value.u8(dw::DW_OP_constu.0);
            value.uleb(word);
            value.u8(dw::DW_OP_stack_value.0);
            exprloc(&mut w.out, &value);
        }
        Some(Constant::Data(d)) => {
            let k = index_of(data, &d);
            // DW_OP_addr, the address, DW_OP_stack_value.
            w.out.uleb(10);
            w.out.u8(dw::DW_OP_addr.0);
            w.patch(Patch::Data(k));
            w.out.u8(dw::DW_OP_stack_value.0);
        }
        None if !var.ranges.is_empty() => {
            let shared = lists.iter().find(|(l, _)| *l == &*var.ranges);
            let at = if let Some(&(_, at)) = shared {
                at
            } else {
                let at = u32::try_from(loc.out.len()).unwrap_or(u32::MAX);
                list(loc, &var.ranges, fp);
                lists.push((&var.ranges, at));
                at
            };
            w.patch(Patch::Loc(at));
        }
        None => {}
    }
}

/// A location list: a base address entry, which gives the function's address, then each
/// stretch of code the local lives somewhere in, by offsets from it.
fn list(loc: &mut Writing, ranges: &[(u32, u32, Place)], fp: u16) {
    loc.out.u64(u64::MAX);
    loc.patch(Patch::Code(0));
    for &(from, to, place) in ranges {
        loc.out.u64(u64::from(from));
        loc.out.u64(u64::from(to));
        let mut expr = Bytes::default();
        match place {
            Place::Reg(r) if r < 32 => expr.u8(dw::DW_OP_reg0.0 + u8::try_from(r).unwrap_or(0)),
            Place::Reg(r) => {
                expr.u8(dw::DW_OP_regx.0);
                expr.uleb(u64::from(r));
            }
            Place::Frame(offset) => breg(&mut expr, fp, offset + 16),
        }
        loc.out.u16(u16::try_from(expr.len()).unwrap_or(0));
        loc.out.0.extend_from_slice(&expr.0);
    }
    loc.out.u64(0);
    loc.out.u64(0);
}

/// `DW_OP_breg` of the register `r` and `offset`.
fn breg(out: &mut Bytes, r: u16, offset: i64) {
    if r < 32 {
        out.u8(dw::DW_OP_breg0.0 + u8::try_from(r).unwrap_or(0));
    } else {
        out.u8(dw::DW_OP_bregx.0);
        out.uleb(u64::from(r));
    }
    out.sleb(offset);
}

/// An expression as `DW_FORM_exprloc` writes it: its length, then its bytes.
fn exprloc(out: &mut Bytes, expr: &Bytes) {
    out.uleb(expr.len() as u64);
    out.0.extend_from_slice(&expr.0);
}

/// The function's sequence of the line table: its address, then a row for each stretch of its
/// code that comes from one place, each file by its number in the unit's table, which lists the
/// program's files from 1. Each sequence starts from the table's first state.
fn line(f: &Facts) -> Chunk {
    let mut w = Writing::default();
    if f.rows.is_empty() {
        return w.finish();
    }
    // DW_LNE_set_address.
    w.out.u8(0);
    w.out.uleb(9);
    w.out.u8(dw::DW_LNE_set_address.0);
    w.patch(Patch::Code(0));
    let (mut file, mut line, mut col, mut address) = (1, 1, 0, 0);
    for row in &f.rows {
        if u64::from(row.file) + 1 != file {
            file = u64::from(row.file) + 1;
            w.out.u8(dw::DW_LNS_set_file.0);
            w.out.uleb(file);
        }
        if u64::from(row.col) != col {
            col = u64::from(row.col);
            w.out.u8(dw::DW_LNS_set_column.0);
            w.out.uleb(col);
        }
        let lines = i64::from(row.line) - line;
        row_at(&mut w.out, lines, u64::from(row.offset - address));
        (line, address) = (i64::from(row.line), row.offset);
    }
    w.out.u8(dw::DW_LNS_advance_pc.0);
    w.out.uleb(u64::from(f.size - address));
    w.out.u8(0);
    w.out.uleb(1);
    w.out.u8(dw::DW_LNE_end_sequence.0);
    w.finish()
}

/// A row `lines` lines and `bytes` bytes after the last: a special opcode where one encodes
/// both, and otherwise standard ones.
fn row_at(out: &mut Bytes, lines: i64, bytes: u64) {
    let special = |bytes: u64| {
        let adjusted = u64::try_from(lines - i64::from(LINE_BASE)).ok()?;
        if adjusted >= u64::from(LINE_RANGE) {
            return None;
        }
        let advance = u64::from(LINE_RANGE).checked_mul(bytes)?;
        let opcode = adjusted.checked_add(advance)? + u64::from(OPCODE_BASE);
        u8::try_from(opcode).ok()
    };
    if let Some(opcode) = special(bytes) {
        out.u8(opcode);
        return;
    }
    if bytes > 0 {
        out.u8(dw::DW_LNS_advance_pc.0);
        out.uleb(bytes);
    }
    if let Some(opcode) = special(0) {
        out.u8(opcode);
    } else {
        out.u8(dw::DW_LNS_advance_line.0);
        out.sleb(lines);
        out.u8(dw::DW_LNS_copy.0);
    }
}

/// The function's frame description entry, as `.debug_frame` holds it after `cie`.
fn frame(unwind: &UnwindInfo, cie: &CommonInformationEntry) -> Chunk {
    let mut table = FrameTable::default();
    let id = table.add_cie(cie.clone());
    table.add_fde(
        id,
        unwind.to_fde(Address::Symbol {
            symbol: 0,
            addend: 0,
        }),
    );
    let mut out = DebugFrame(Relocating::new(false));
    if table.write_debug_frame(&mut out).is_err() {
        return Chunk::default();
    }
    let written = out.0;
    let all = written.data.slice();
    let Some(length) = all.get(..4).and_then(|b| b.try_into().ok()) else {
        return Chunk::default();
    };
    let start = 4 + u32::from_le_bytes(length) as usize;
    let patches: Vec<(u32, Patch)> = (written.relocations.iter())
        .filter_map(|&(offset, _, target, addend)| {
            let at = u32::try_from(offset.checked_sub(start)?).ok()?;
            match target {
                Target::Function(_) => Some((at, Patch::Code(addend))),
                Target::Section(_) => Some((at, Patch::Cie)),
            }
        })
        .collect();
    Chunk {
        bytes: all.get(start..).unwrap_or_default().into(),
        patches: patches.into(),
    }
}
