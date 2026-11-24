//! Lists that nothing else can reference: a local that `ListNew` gives a new list, whose only
//! uses are the appends that fill it, as a list literal's do, and one assignment that puts it
//! in a place, such as a `var`'s. Once there, the place's list is unique, as if a write had
//! made it so: no copy of the list exists, since every copy is a statement that reads the
//! local, and the runtime keeps no reference to a list it appends to.

use crate::mir::{Function, Operand, Runtime, Rvalue, Stmt, Terminator};

/// Whether each local of `f` holds such a list.
pub(super) fn fresh(f: &Function, slot: &[bool]) -> Vec<bool> {
    let n = f.locals.len();
    let (mut made, mut placed, mut other) = (vec![0u32; n], vec![0u32; n], vec![0u32; n]);
    for block in &f.blocks {
        for s in &block.stmts {
            match s {
                Stmt::Assign(d, Rvalue::Runtime(Runtime::ListNew, args)) => {
                    made[d.0 as usize] += 1;
                    count(&mut other, args);
                }
                Stmt::Assign(d, Rvalue::Use(o)) if slot[d.0 as usize] => {
                    count(&mut placed, [o]);
                    other[d.0 as usize] += 1;
                }
                Stmt::Assign(d, r) => {
                    other[d.0 as usize] += 1;
                    count(&mut other, r.operands());
                }
                // The target is filled, and an element that is the target is read.
                Stmt::Effect(Runtime::ListPush, args) => count(&mut other, &args[1..]),
                Stmt::Effect(_, args) => count(&mut other, args),
                Stmt::Store { slot, value, .. } => count(&mut other, [slot, value]),
                Stmt::Dup(l) | Stmt::Drop(l) => other[l.0 as usize] += 1,
                Stmt::ReleaseConstants | Stmt::At(_) | Stmt::Count(..) => {}
            }
        }
        count(&mut other, block.term.operands());
        if let Terminator::Call { dest, raised, .. } = &block.term {
            for d in dest.iter().chain(raised.iter().flat_map(|(e, _)| e)) {
                other[d.0 as usize] += 1;
            }
        }
    }
    (0..n)
        .map(|l| made[l] == 1 && placed[l] == 1 && other[l] == 0 && !slot[l])
        .collect()
}

/// Counts each local among `operands`.
fn count<'a>(counts: &mut [u32], operands: impl IntoIterator<Item = &'a Operand>) {
    for l in operands.into_iter().filter_map(Operand::local) {
        counts[l.0 as usize] += 1;
    }
}
