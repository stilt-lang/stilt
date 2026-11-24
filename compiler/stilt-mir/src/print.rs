//! The MIR as text, for reading it and for tests.

use std::fmt::{self, Write};

use crate::mir::{Arg, BlockId, Callee, Const, Function, Local, Operand, Rvalue, Stmt, Terminator};

/// A function's MIR, one statement per line.
#[must_use]
pub fn print(f: &Function) -> String {
    let mut out = format!("fn {}(", f.name);
    let params: Vec<String> = f
        .params
        .iter()
        .map(|p| {
            format!(
                "{}: {:?} {:?}",
                p.local, p.mode, f.locals[p.local.0 as usize].repr
            )
        })
        .collect();
    out.push_str(&params.join(", "));
    out.push_str(") {\n");
    for (i, block) in f.blocks.iter().enumerate() {
        let _ = writeln!(out, "  bb{i}:");
        for stmt in &block.stmts {
            let _ = writeln!(out, "    {}", stmt_text(stmt));
        }
        let _ = writeln!(out, "    {}", term_text(&block.term));
    }
    out.push('}');
    out
}

fn op(o: &Operand) -> String {
    match o {
        Operand::Local(l) => l.to_string(),
        Operand::Const(c) => const_text(c),
    }
}

fn const_text(c: &Const) -> String {
    match c {
        Const::Word(w) => w.to_string(),
        Const::Str(s) => format!("{s:?}"),
        Const::Data(tag, fields) => {
            let fields: Vec<String> = fields.iter().map(|(c, _)| const_text(c)).collect();
            format!("data{tag}[{}]", fields.join(", "))
        }
        Const::Code(f) => format!("&{f}"),
    }
}

fn locals(ls: &[crate::mir::Local]) -> String {
    ls.iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

fn ops(os: &[Operand]) -> String {
    os.iter().map(op).collect::<Vec<_>>().join(", ")
}

fn rvalue_text(r: &Rvalue) -> String {
    match r {
        Rvalue::Use(o) => op(o),
        Rvalue::Prim(p, args, _) => format!("{p:?}({})", ops(args)),
        Rvalue::Alloc(tag, fields) => {
            let fields: Vec<Operand> = fields.iter().map(|(o, _)| o.clone()).collect();
            if *tag == crate::mir::BOX {
                format!("box[{}]", ops(&fields))
            } else {
                format!("alloc{tag}[{}]", ops(&fields))
            }
        }
        Rvalue::AllocIn(memory, tag, fields, _) => {
            let fields: Vec<Operand> = fields.iter().map(|(o, _)| o.clone()).collect();
            format!("alloc{tag} in {}[{}]", op(memory), ops(&fields))
        }
        Rvalue::Field {
            base, len, index, ..
        } => format!("{}.{index}/{len}", op(base)),
        Rvalue::Tag(o) => format!("tag {}", op(o)),
        Rvalue::Load(o) => format!("*{}", op(o)),
        Rvalue::SlotOf(l) => format!("&{l}"),
        Rvalue::Offset(o, words) => format!("{} + {words}", op(o)),
        Rvalue::FieldSlot { slot, len, index } => format!("&unique({}).{index}/{len}", op(slot)),
        Rvalue::Runtime(f, args) => format!("{}({})", f.symbol(), ops(args)),
        Rvalue::Constant(f, _, 0, words, _) if words.len() == 1 => format!("const {f}"),
        Rvalue::Constant(f, _, k, ..) => format!("const {f}.{k}"),
    }
}

fn stmt_text(s: &Stmt) -> String {
    match s {
        Stmt::Assign(l, r) => format!("{l} = {}", rvalue_text(r)),
        Stmt::Store { slot, value, .. } => format!("*{} = {}", op(slot), op(value)),
        Stmt::Effect(f, args) => format!("{}({})", f.symbol(), ops(args)),
        Stmt::ReleaseConstants => "release constants".to_owned(),
        Stmt::Dup(l) => format!("dup {l}"),
        Stmt::Drop(l) => format!("drop {l}"),
        Stmt::At(word) => format!(
            "at {}:{}:{}",
            word >> 44,
            word >> 20 & 0xff_ffff,
            word & 0xf_ffff
        ),
        Stmt::Count(counted, word) => format!(
            "count {counted:?} {}:{}:{}",
            word >> 44,
            word >> 20 & 0xff_ffff,
            word & 0xf_ffff
        ),
    }
}

fn term_text(t: &Terminator) -> String {
    match t {
        Terminator::Goto(b) => format!("goto {b}"),
        Terminator::Branch {
            cond,
            then,
            otherwise,
        } => format!("if {} {then} else {otherwise}", op(cond)),
        Terminator::Switch {
            value,
            cases,
            otherwise,
        } => {
            let cases: Vec<String> = cases.iter().map(|(v, b)| format!("{v} => {b}")).collect();
            format!(
                "switch {} [{}] else {otherwise}",
                op(value),
                cases.join(", ")
            )
        }
        Terminator::Call {
            callee,
            args,
            dest,
            next,
            raised,
        } => {
            let callee = match callee {
                Callee::Direct(f) => f.to_string(),
                Callee::Value(o) => format!("({})", op(o)),
                Callee::Method(d, i) => format!("{}#{i}", op(d)),
            };
            let args: Vec<String> = args
                .iter()
                .map(|a| match a {
                    Arg::Borrow(o) => op(o),
                    Arg::Own(o) => format!("own {}", op(o)),
                    Arg::Ref(o) => format!("ref {}", op(o)),
                    Arg::Lend(words) => {
                        let words: Vec<Operand> = words.iter().map(|(o, _)| o.clone()).collect();
                        format!("lend[{}]", ops(&words))
                    }
                })
                .collect();
            let raised = raised.as_ref().map_or(String::new(), |(e, b)| {
                format!(" raise {} -> {b}", locals(e))
            });
            format!(
                "{} = call {callee}({}) -> {next}{raised}",
                locals(dest),
                args.join(", ")
            )
        }
        Terminator::Return(os) => format!("return {}", ops(os)),
        Terminator::Raise(os) => format!("raise {}", ops(os)),
        Terminator::Panic { kind, .. } => format!("panic {kind}"),
        Terminator::Unreachable => "unreachable".to_owned(),
    }
}

impl fmt::Display for Local {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_{}", self.0)
    }
}

impl fmt::Display for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bb{}", self.0)
    }
}
