//! The copies that inlining leaves: a local the source doesn't name, defined once by a copy of
//! a local defined once, is read as that local, and a named one stays for a debugger.

use super::{assign, function, op, ret};
use crate::mir::{
    Function, Local, LocalDecl, NumKind, Operand, ParamMode, Prim, Repr, Rvalue, Terminator,
};
use crate::opt::copies::propagate;

/// `_2 = _1 + 1`, `_3 = _2`, `_4 = _3`, then a return of `_4`.
fn chain() -> Function {
    let add = Rvalue::Prim(
        Prim::Add(NumKind::I64),
        vec![op(1), Operand::word(1)],
        super::LOC,
    );
    let mut f = function(
        &[ParamMode::Borrowed],
        3,
        &[],
        vec![ret(vec![
            assign(2, add),
            assign(3, Rvalue::Use(op(2))),
            assign(4, Rvalue::Use(op(3))),
        ])],
    );
    f.blocks[0].term = Terminator::Return(vec![op(4)]);
    f
}

#[test]
fn a_chain_of_copies_reads_the_local_it_starts_from() {
    let mut f = chain();
    propagate(&mut f);
    assert_eq!(f.blocks[0].stmts.len(), 1);
    assert_eq!(f.blocks[0].term, Terminator::Return(vec![op(2)]));
}

#[test]
fn a_copy_the_source_names_stays() {
    let mut f = chain();
    f.locals[3].name = Some(stilt_hir::hir::Name::from("x"));
    propagate(&mut f);
    // `_3` is the source's `x`; `_4`, a copy of it, reads it.
    assert_eq!(f.blocks[0].stmts[1], assign(3, Rvalue::Use(op(2))));
    assert_eq!(f.blocks[0].term, Terminator::Return(vec![op(3)]));
}

#[test]
fn a_copy_of_a_local_assigned_twice_stays() {
    let mut f = chain();
    f.blocks[0]
        .stmts
        .push(assign(2, Rvalue::Use(Operand::word(0))));
    let before = f.clone();
    propagate(&mut f);
    assert_eq!(f.blocks[0].stmts[1], before.blocks[0].stmts[1]);
}

#[test]
fn a_local_counted_by_a_copied_witness_follows_its_source() {
    let mut f = chain();
    f.locals.push(LocalDecl {
        repr: Repr::Generic(Local(3)),
        ..f.locals[0].clone()
    });
    propagate(&mut f);
    assert_eq!(f.locals[5].repr, Repr::Generic(Local(2)));
}
