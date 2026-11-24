//! Scalar replacement of objects ([Values and costs](../../../../docs/design/values-and-costs.md),
//! "A cheap optimizer before Cranelift"): a data object that a function makes and only ever
//! reads field by field, itself or through copies, never needs to exist. A closure whose call
//! inlined code of the standard library has inlined is such an object. Each field that is read is moved into a local of its own where the object would
//! have been made, and each read of the field copies that local, so the function allocates
//! nothing for them.
//!
//! The words keep their references: the object would have taken each field's, and released
//! them when it died; each local now holds it until its last use, as reference counting decides.

use crate::mir::{Function, Heapness, Local, LocalDecl, Operand, Repr, Rvalue, Stmt};
use crate::opt::defs::definitions;

/// Replaces each object of `f` that is only read field by field by the words of the fields it
/// reads, and returns whether it replaced one.
pub(crate) fn unbox(f: &mut Function) -> bool {
    let mut any = false;
    // The field of a replaced object that holds another object is now a copy of it, which the
    // next round sees.
    while unbox_once(f) {
        any = true;
    }
    any
}

/// The objects of a function: for each local, the object it holds, if it holds one that the
/// function makes, defined once by an allocation of `len[object]` words, its fields at the
/// word offsets `starts[object]`, or by a copy of a local that holds one; neither a parameter
/// nor in memory.
struct Objects {
    of: Vec<Option<Local>>,
    len: Vec<usize>,
    starts: Vec<Vec<usize>>,
}

impl Objects {
    fn of(&self, o: &Operand) -> Option<Local> {
        o.local().and_then(|l| self.of[l.0 as usize])
    }

    /// The field of `object` that a read of word `index` of `len` words reads whole, if one is.
    fn field(&self, object: Local, len: u32, index: u32) -> Option<usize> {
        let o = object.0 as usize;
        if self.len[o] != len as usize {
            return None;
        }
        self.starts[o].iter().position(|&s| s == index as usize)
    }
}

fn unbox_once(f: &mut Function) -> bool {
    let objects = objects(f);
    let escapes = escapes(f, &objects);
    let replaced: Vec<bool> = (0..f.locals.len())
        .map(|l| objects.of[l] == Some(local(l)) && !escapes[l])
        .collect();
    if !replaced.contains(&true) {
        return false;
    }
    let fields = fields(f, &objects, &replaced);
    rewrite(f, &objects, &replaced, &fields);
    true
}

fn local(l: usize) -> Local {
    Local(u32::try_from(l).expect("under 4G locals"))
}

fn objects(f: &Function) -> Objects {
    let defs = definitions(f);
    let mut objects = Objects {
        of: vec![None; f.locals.len()],
        len: vec![0; f.locals.len()],
        starts: vec![Vec::new(); f.locals.len()],
    };
    let once = |l: &Local| {
        defs[l.0 as usize] == 1
            && !f.locals[l.0 as usize].slot
            && !f.params.iter().any(|p| p.local == *l)
    };
    let mut copies = Vec::new();
    for s in f.blocks.iter().flat_map(|b| &b.stmts) {
        match s {
            Stmt::Assign(d, Rvalue::Alloc(_, fields)) if once(d) => {
                let (starts, len) = crate::mir::offsets(fields.iter().map(|(_, h)| match h {
                    Heapness::Array(e) => Repr::Array(*e),
                    Heapness::Static(_) | Heapness::Witness(_) => Repr::Scalar,
                }));
                objects.of[d.0 as usize] = Some(*d);
                objects.len[d.0 as usize] = len;
                objects.starts[d.0 as usize] = starts;
            }
            Stmt::Assign(d, Rvalue::Use(Operand::Local(s))) if once(d) => copies.push((*d, *s)),
            _ => {}
        }
    }
    let mut changed = true;
    while changed {
        changed = false;
        for &(d, s) in &copies {
            if objects.of[d.0 as usize].is_none() && objects.of[s.0 as usize].is_some() {
                objects.of[d.0 as usize] = objects.of[s.0 as usize];
                changed = true;
            }
        }
    }
    objects
}

/// Which objects a use lets escape: any use but a read of one of its fields, or a copy into a
/// local that holds it, from a call's argument to a return.
fn escapes(f: &Function, objects: &Objects) -> Vec<bool> {
    let mut escapes = vec![false; f.locals.len()];
    let mut escape = |o: &Operand| {
        if let Some(object) = objects.of(o) {
            escapes[object.0 as usize] = true;
        }
    };
    for block in &f.blocks {
        for s in &block.stmts {
            match s {
                Stmt::Assign(
                    _,
                    Rvalue::Field {
                        base, len, index, ..
                    },
                ) => {
                    let fits = |o: Local| objects.field(o, *len, *index).is_some();
                    if objects.of(base).is_some_and(|o| !fits(o)) {
                        escape(base);
                    }
                }
                Stmt::Assign(d, Rvalue::Use(s))
                    if objects.of[d.0 as usize].is_some()
                        && objects.of[d.0 as usize] == objects.of(s) => {}
                Stmt::Assign(_, r) => r.operands().into_iter().for_each(&mut escape),
                Stmt::Store { slot, value, .. } => {
                    escape(slot);
                    escape(value);
                }
                Stmt::Effect(_, args) => args.iter().for_each(&mut escape),
                Stmt::ReleaseConstants
                | Stmt::Dup(_)
                | Stmt::Drop(_)
                | Stmt::At(_)
                | Stmt::Count(..) => {}
            }
        }
        block.term.operands().into_iter().for_each(&mut escape);
    }
    escapes
}

/// For each replaced object, by its local, a new local for each of its fields that is read.
fn fields(f: &mut Function, objects: &Objects, replaced: &[bool]) -> Vec<Vec<Option<Local>>> {
    let mut read: Vec<Vec<bool>> = objects
        .starts
        .iter()
        .map(|s| vec![false; s.len()])
        .collect();
    let mut heapness: Vec<Vec<Heapness>> = vec![Vec::new(); f.locals.len()];
    for s in f.blocks.iter().flat_map(|b| &b.stmts) {
        match s {
            Stmt::Assign(d, Rvalue::Alloc(_, fields)) if replaced[d.0 as usize] => {
                heapness[d.0 as usize] = fields.iter().map(|(_, h)| *h).collect();
            }
            Stmt::Assign(
                _,
                Rvalue::Field {
                    base, len, index, ..
                },
            ) => {
                if let Some(object) = objects.of(base).filter(|o| replaced[o.0 as usize])
                    && let Some(j) = objects.field(object, *len, *index)
                {
                    read[object.0 as usize][j] = true;
                }
            }
            _ => {}
        }
    }
    let mut fields = vec![Vec::new(); f.locals.len()];
    for (o, kept) in replaced.iter().enumerate() {
        if *kept {
            fields[o] = read[o]
                .iter()
                .zip(&heapness[o])
                .map(|(&read, &h)| read.then(|| new_local(f, h)))
                .collect();
        }
    }
    fields
}

fn new_local(f: &mut Function, h: Heapness) -> Local {
    let repr = match h {
        Heapness::Static(false) => Repr::Scalar,
        Heapness::Static(true) => Repr::Heap,
        Heapness::Witness(w) => Repr::Generic(w),
        Heapness::Array(e) => Repr::Array(e),
    };
    let l = local(f.locals.len());
    f.locals.push(LocalDecl {
        repr,
        slot: false,
        grouped: false,
        borrowed: false,
        var: false,
        name: None,
        shown: None,
    });
    l
}

/// Moves each replaced object's read fields into their locals where it was made, drops the
/// copies of it, and makes each read of a field a copy of the field's local.
fn rewrite(f: &mut Function, objects: &Objects, replaced: &[bool], fields: &[Vec<Option<Local>>]) {
    let of = |l: Local| objects.of[l.0 as usize].filter(|o| replaced[o.0 as usize]);
    for block in &mut f.blocks {
        let stmts = std::mem::take(&mut block.stmts);
        for s in stmts {
            let Stmt::Assign(d, r) = s else {
                block.stmts.push(s);
                continue;
            };
            match (of(d), r) {
                (Some(_), Rvalue::Alloc(_, words)) => {
                    let moved = words.into_iter().zip(&fields[d.0 as usize]);
                    for ((w, _), l) in moved {
                        if let Some(l) = l {
                            block.stmts.push(Stmt::Assign(*l, Rvalue::Use(w)));
                        }
                    }
                }
                (Some(_), Rvalue::Use(_)) => {}
                (
                    _,
                    Rvalue::Field {
                        base,
                        len,
                        index,
                        variant,
                    },
                ) => {
                    let field = base.local().and_then(of).and_then(|o| {
                        let j = objects.field(o, len, index)?;
                        fields[o.0 as usize][j]
                    });
                    let r = match field {
                        Some(field) => Rvalue::Use(Operand::Local(field)),
                        None => Rvalue::Field {
                            base,
                            len,
                            index,
                            variant,
                        },
                    };
                    block.stmts.push(Stmt::Assign(d, r));
                }
                (_, r) => block.stmts.push(Stmt::Assign(d, r)),
            }
        }
    }
}
