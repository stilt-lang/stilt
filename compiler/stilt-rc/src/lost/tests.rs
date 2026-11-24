//! The copies that reference counting makes of what direct calls consume, and the places they
//! name (values.consumed-parameters).

use stilt_hir::hir::{Item, Name};
use stilt_mir::FnRef;
use stilt_mir::mir::{
    Arg, Block, BlockId, Callee, Const, Function, Local, LocalDecl, Operand, Param, ParamMode,
    Repr, Rvalue, Stmt, Terminator,
};

use super::{places, whole};
use crate::{Copied, Need, count};

fn item(name: &str) -> FnRef {
    FnRef::Function(Item {
        home: Name::from("main"),
        name: Name::from(name),
    })
}

fn decl(repr: Repr, name: Option<&str>) -> LocalDecl {
    LocalDecl {
        repr,
        slot: false,
        grouped: false,
        borrowed: false,
        var: false,
        name: name.map(Name::from),
        shown: None,
    }
}

/// The location word of line `line`.
fn line(line: u64) -> u64 {
    line << 20
}

/// A function whose local `xs` holds a string and is passed to a call of `g` with `args`, and
/// that then reads `xs` again if `after`.
fn caller(args: Vec<Arg>, after: bool) -> Function {
    let xs = Operand::Local(Local(1));
    let read = Stmt::Assign(Local(3), Rvalue::Tag(xs));
    Function {
        name: item("f"),
        params: vec![Param {
            local: Local(0),
            mode: ParamMode::Borrowed,
        }],
        hidden: 1,
        results: 1,
        locals: vec![
            decl(Repr::Scalar, None),
            decl(Repr::Heap, Some("xs")),
            decl(Repr::Heap, None),
            decl(Repr::Scalar, None),
        ],
        blocks: vec![
            Block {
                stmts: vec![
                    Stmt::At(line(4)),
                    Stmt::Assign(
                        Local(1),
                        Rvalue::Use(Operand::Const(Const::Str("a".into()))),
                    ),
                ],
                term: Terminator::Call {
                    callee: Callee::Direct(item("g")),
                    args,
                    dest: vec![Local(2)],
                    next: BlockId(1),
                    raised: None,
                },
            },
            Block {
                stmts: if after { vec![read] } else { Vec::new() },
                term: Terminator::Return(vec![Operand::Local(Local(2))]),
            },
        ],
        broken: false,
    }
}

fn own_xs() -> Arg {
    Arg::Own(Operand::Local(Local(1)))
}

#[test]
fn a_value_used_after_the_call_that_consumes_it_is_copied() {
    let mut f = caller(vec![Arg::Borrow(Operand::word(0)), own_xs()], true);
    let copied = count(&mut f);
    assert_eq!(
        copied,
        [Copied {
            block: BlockId(0),
            local: Local(1),
            callee: item("g"),
            need: Need::After,
            at: line(4),
        }]
    );
    let lost = places(&f, &copied);
    assert_eq!(&*lost[0].place, "xs");
}

#[test]
fn the_last_use_of_a_value_is_given_up() {
    let mut f = caller(vec![Arg::Borrow(Operand::word(0)), own_xs()], false);
    assert_eq!(count(&mut f), []);
}

#[test]
fn a_value_passed_twice_is_copied_for_the_call_that_consumes_it() {
    let both = vec![
        Arg::Borrow(Operand::word(0)),
        own_xs(),
        Arg::Borrow(Operand::Local(Local(1))),
    ];
    let mut f = caller(both, false);
    let copied = count(&mut f);
    assert_eq!(copied.len(), 1);
    assert_eq!(copied[0].need, Need::Twice);
}

#[test]
fn a_value_of_several_words_is_named_whole_when_the_call_copies_each() {
    let names: Vec<Name> = ["p.left", "p.right", "q"].map(Name::from).to_vec();
    let both = &names[..2];
    assert_eq!(&*whole(names[0], both, &names), "p");
    assert_eq!(&*whole(names[0], &names[..1], &names), "p.left");
    assert_eq!(&*whole(names[2], &names[2..], &names), "q");
}
