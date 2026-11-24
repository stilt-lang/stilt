//! Renaming a callee's locals and blocks as its body is spliced into a caller.

use std::sync::Arc;

use crate::mir::{Arg, BlockId, Callee, Heapness, Local, Operand, Repr, Rvalue, Stmt, Terminator};

/// What each local of a callee becomes in its caller, and where its blocks go.
pub(crate) struct Renaming {
    /// By the callee's local: the operand that stands for it, the argument of a parameter that
    /// the argument binds, or else a local of the caller's own.
    pub(crate) locals: Vec<Operand>,
    /// The place among the caller's blocks of the callee's first block.
    pub(crate) blocks: u32,
}

impl Renaming {
    pub(crate) fn operand(&self, o: &Operand) -> Operand {
        match o {
            Operand::Local(l) => self.locals[l.0 as usize].clone(),
            Operand::Const(_) => o.clone(),
        }
    }

    fn operands(&self, os: &[Operand]) -> Vec<Operand> {
        os.iter().map(|o| self.operand(o)).collect()
    }

    /// The caller's local that a local becomes where only a local can stand, as the one an
    /// assignment defines: `None` if an argument that is a constant stands for it.
    pub(crate) fn local(&self, l: Local) -> Option<Local> {
        self.locals[l.0 as usize].local()
    }

    fn locals_of(&self, ls: &[Local]) -> Option<Vec<Local>> {
        ls.iter().map(|&l| self.local(l)).collect()
    }

    pub(crate) fn block(&self, b: BlockId) -> BlockId {
        BlockId(b.0 + self.blocks)
    }

    pub(crate) fn repr(&self, r: Repr) -> Option<Repr> {
        r.map_witnesses(&|w| self.local(w).map(Repr::Generic))
    }

    fn heapness(&self, h: Heapness) -> Option<Heapness> {
        match h {
            Heapness::Witness(w) => match self.operand(&Operand::Local(w)) {
                Operand::Local(l) => Some(Heapness::Witness(l)),
                Operand::Const(crate::mir::Const::Word(shape)) => {
                    Some(Heapness::Static(shape & crate::shape::HEAP != 0))
                }
                Operand::Const(_) => None,
            },
            Heapness::Static(_) => Some(h),
            Heapness::Array(e) => {
                let word = |w| match self.operand(&Operand::Local(w)) {
                    Operand::Local(l) => Some(Repr::Generic(l)),
                    Operand::Const(crate::mir::Const::Word(shape)) => {
                        Some(if shape & crate::shape::HEAP == 0 {
                            Repr::Scalar
                        } else {
                            Repr::Heap
                        })
                    }
                    Operand::Const(_) => None,
                };
                match Repr::Array(e).map_witnesses(&word)? {
                    Repr::Array(e) => Some(Heapness::Array(e)),
                    _ => None,
                }
            }
        }
    }

    /// The fields of a data object, renamed.
    fn fields(&self, fields: &[(Operand, Heapness)]) -> Option<Vec<(Operand, Heapness)>> {
        fields
            .iter()
            .map(|(o, h)| Some((self.operand(o), self.heapness(*h)?)))
            .collect()
    }

    pub(crate) fn rvalue(&self, r: &Rvalue) -> Option<Rvalue> {
        Some(match r {
            Rvalue::Use(o) => Rvalue::Use(self.operand(o)),
            Rvalue::Prim(p, args, loc) => Rvalue::Prim(*p, self.operands(args), self.operand(loc)),
            Rvalue::Alloc(tag, fields) => Rvalue::Alloc(*tag, self.fields(fields)?),
            Rvalue::AllocIn(memory, tag, fields, kept) => {
                Rvalue::AllocIn(self.operand(memory), *tag, self.fields(fields)?, *kept)
            }
            Rvalue::Field {
                base,
                len,
                index,
                variant,
            } => Rvalue::Field {
                base: self.operand(base),
                len: *len,
                index: *index,
                variant: *variant,
            },
            Rvalue::Tag(o) => Rvalue::Tag(self.operand(o)),
            Rvalue::Load(o) => Rvalue::Load(self.operand(o)),
            Rvalue::SlotOf(l) => Rvalue::SlotOf(self.local(*l)?),
            Rvalue::Offset(o, words) => Rvalue::Offset(self.operand(o), *words),
            Rvalue::FieldSlot { slot, len, index } => Rvalue::FieldSlot {
                slot: self.operand(slot),
                len: *len,
                index: *index,
            },
            Rvalue::Runtime(f, args) => Rvalue::Runtime(*f, self.operands(args)),
            Rvalue::Constant(f, loc, k, words, safe) => {
                Rvalue::Constant(f.clone(), self.operand(loc), *k, Arc::clone(words), *safe)
            }
        })
    }

    pub(crate) fn stmt(&self, s: &Stmt) -> Option<Stmt> {
        Some(match s {
            Stmt::Assign(d, r) => Stmt::Assign(self.local(*d)?, self.rvalue(r)?),
            Stmt::Store { slot, value, repr } => Stmt::Store {
                slot: self.operand(slot),
                value: self.operand(value),
                repr: self.repr(*repr)?,
            },
            Stmt::Effect(f, args) => Stmt::Effect(*f, self.operands(args)),
            Stmt::Dup(l) => Stmt::Dup(self.local(*l)?),
            Stmt::Drop(l) => Stmt::Drop(self.local(*l)?),
            Stmt::ReleaseConstants | Stmt::At(_) | Stmt::Count(..) => s.clone(),
        })
    }

    /// A terminator other than a return or a raise, renamed.
    pub(crate) fn term(&self, t: &Terminator) -> Option<Terminator> {
        Some(match t {
            Terminator::Goto(b) => Terminator::Goto(self.block(*b)),
            Terminator::Branch {
                cond,
                then,
                otherwise,
            } => Terminator::Branch {
                cond: self.operand(cond),
                then: self.block(*then),
                otherwise: self.block(*otherwise),
            },
            Terminator::Switch {
                value,
                cases,
                otherwise,
            } => Terminator::Switch {
                value: self.operand(value),
                cases: cases.iter().map(|&(v, b)| (v, self.block(b))).collect(),
                otherwise: self.block(*otherwise),
            },
            Terminator::Call {
                callee,
                args,
                dest,
                next,
                raised,
            } => Terminator::Call {
                callee: self.callee(callee),
                args: args.iter().map(|a| self.arg(a)).collect(),
                dest: self.locals_of(dest)?,
                next: self.block(*next),
                raised: match raised {
                    Some((error, b)) => Some((self.locals_of(error)?, self.block(*b))),
                    None => None,
                },
            },
            Terminator::Panic { kind, detail, loc } => Terminator::Panic {
                kind: *kind,
                detail: detail.as_ref().map(|d| self.operand(d)),
                loc: self.operand(loc),
            },
            Terminator::Return(os) => Terminator::Return(self.operands(os)),
            Terminator::Raise(os) => Terminator::Raise(self.operands(os)),
            Terminator::Unreachable => Terminator::Unreachable,
        })
    }

    fn callee(&self, c: &Callee) -> Callee {
        match c {
            Callee::Direct(f) => Callee::Direct(f.clone()),
            Callee::Value(o) => Callee::Value(self.operand(o)),
            Callee::Method(o, i) => Callee::Method(self.operand(o), *i),
        }
    }

    fn arg(&self, a: &Arg) -> Arg {
        match a {
            Arg::Borrow(o) => Arg::Borrow(self.operand(o)),
            Arg::Own(o) => Arg::Own(self.operand(o)),
            Arg::Ref(o) => Arg::Ref(self.operand(o)),
            Arg::Lend(words) => Arg::Lend(
                words
                    .iter()
                    .map(|(o, h)| (self.operand(o), self.heapness(*h).unwrap_or(*h)))
                    .collect(),
            ),
        }
    }
}
