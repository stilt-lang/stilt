//! Appending in place to a string (values.strings): an interpolation of two to four parts whose
//! first part is a string released right after it, as `s = "{s}{x}"` is, gives that reference
//! to the concatenation, which then appends to the string where it is when nothing else
//! references it, so a loop that builds a string runs in time linear in what it appends. This
//! pass reads the reference counting that `stilt-rc` inserts, whose `Stmt::Drop` releases the
//! first part, so it runs after it. The meaning is the same either way, which is why a debug
//! build does it too: only who frees the first part, and when, changes.

use crate::mir::{Function, Operand, Runtime, Rvalue, Stmt};

/// Gives each first part of a concatenation that is released right after it to the
/// concatenation instead.
pub(crate) fn concatenate_onto(f: &mut Function) {
    for block in &mut f.blocks {
        let mut i = 0;
        while i + 1 < block.stmts.len() {
            if let Some(onto) = onto(&block.stmts[i], &block.stmts[i + 1]) {
                if let Stmt::Assign(_, Rvalue::Runtime(runtime, _)) = &mut block.stmts[i] {
                    *runtime = onto;
                }
                block.stmts.remove(i + 1);
            }
            i += 1;
        }
    }
}

/// The concatenation that takes its first part, for `stmt` followed by `next`, when `stmt`
/// concatenates strings whose first part `next` releases, and that part is no other one.
fn onto(stmt: &Stmt, next: &Stmt) -> Option<Runtime> {
    let Stmt::Assign(result, Rvalue::Runtime(runtime, args)) = stmt else {
        return None;
    };
    let onto = match runtime {
        Runtime::Concat2 => Runtime::ConcatOnto2,
        Runtime::Concat3 => Runtime::ConcatOnto3,
        Runtime::Concat4 => Runtime::ConcatOnto4,
        _ => return None,
    };
    let (Some(Operand::Local(first)), Stmt::Drop(released)) = (args.first(), next) else {
        return None;
    };
    let alone = !args[1..].contains(&Operand::Local(*first));
    (first == released && result != first && alone).then_some(onto)
}
