//! A string that an interpolation starts with and releases right after is given to the
//! concatenation, which appends to it in place; one that is read again, or is another part of
//! the same interpolation too, keeps its reference.

use super::{assign, function, op, ret};
use crate::mir::{Const, Operand, Runtime, Rvalue, Stmt};
use crate::opt::optimize_counted;

/// `_2 = concat2(_1, second)`, then `after`, in a function whose `_1` and `_2` are strings.
fn concatenated(second: Operand, after: Vec<Stmt>) -> Vec<Stmt> {
    let mut stmts = vec![assign(
        2,
        Rvalue::Runtime(Runtime::Concat2, vec![op(1), second]),
    )];
    stmts.extend(after);
    let mut f = function(&[], 3, &[1, 2], vec![ret(stmts)]);
    optimize_counted(&mut f);
    f.blocks.swap_remove(0).stmts
}

fn text() -> Operand {
    Operand::Const(Const::Str("ab".into()))
}

#[test]
fn a_first_part_released_after_the_concatenation_is_appended_to() {
    let stmts = concatenated(text(), vec![Stmt::Drop(crate::mir::Local(1))]);
    assert_eq!(
        stmts,
        [assign(
            2,
            Rvalue::Runtime(Runtime::ConcatOnto2, vec![op(1), text()])
        )]
    );
}

#[test]
fn a_first_part_kept_or_written_twice_is_borrowed() {
    let kept = concatenated(text(), vec![]);
    assert!(matches!(
        &kept[0],
        Stmt::Assign(_, Rvalue::Runtime(Runtime::Concat2, _))
    ));
    let twice = concatenated(op(1), vec![Stmt::Drop(crate::mir::Local(1))]);
    assert_eq!(twice.len(), 2, "{twice:?}");
}
