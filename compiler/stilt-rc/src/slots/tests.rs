//! Where the words of an `inout` parameter's value are needed: again where the function returns
//! or raises, which gives them back to the caller, and not after a store of the whole word, nor
//! where a panic ends the function. A word that nothing needs after a load gives the local the
//! word's reference, and one that something needs is copied, which a call that consumes the copy
//! shows as a lost reuse (values.consumed-parameters and values.inout-arguments).

use stilt_hir::hir::{Item, Name};
use stilt_mir::FnRef;
use stilt_mir::mir::{
    Arg, Block, BlockId, Callee, Function, Local, LocalDecl, Operand, Param, ParamMode, Repr,
    Rvalue, Stmt, Terminator,
};

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
        name: name.map(stilt_hir::hir::Name::from),
        shown: None,
    }
}

fn local(i: u32) -> Operand {
    Operand::Local(Local(i))
}

/// The location word of line `line`.
fn line(line: u64) -> u64 {
    line << 20
}

/// `*_p = _v`, of a heap word.
fn store(p: u32, v: u32) -> Stmt {
    Stmt::Store {
        slot: local(p),
        value: local(v),
        repr: Repr::Heap,
    }
}

/// What gives a loaded word's reference to the local that loads it through `_p`: the word is
/// left holding nothing, and no count is released.
fn cleared(p: u32) -> Stmt {
    Stmt::Store {
        slot: local(p),
        value: Operand::word(0),
        repr: Repr::Scalar,
    }
}

fn ret() -> Terminator {
    Terminator::Return(vec![Operand::word(0)])
}

fn block(stmts: Vec<Stmt>, term: Terminator) -> Block {
    Block { stmts, term }
}

/// A function whose `inout` parameter `table`, `_1`, points to a value of `words` heap words, one
/// or two, which its entry loads, the first into `_6` through `_1` and the second into `_8`
/// through `_7`, which points past `_1`, and passes to a call of `g` that consumes them, whose
/// result is `_2`. The call goes on at block 1, and raises its error, `_3`, to `raised` if given.
/// `blocks` are the function's blocks from block 1 on, and its other locals are `_4`, a heap word,
/// and `_5`, a scalar.
fn passing(words: u32, raised: Option<u32>, blocks: Vec<Block>) -> Function {
    let mut entry = vec![
        Stmt::At(line(4)),
        Stmt::Assign(Local(6), Rvalue::Load(local(1))),
    ];
    let mut args = vec![Arg::Borrow(Operand::word(0)), Arg::Own(local(6))];
    if words == 2 {
        entry.push(Stmt::Assign(Local(7), Rvalue::Offset(local(1), 1)));
        entry.push(Stmt::Assign(Local(8), Rvalue::Load(local(7))));
        args.push(Arg::Own(local(8)));
    }
    let call = Terminator::Call {
        callee: Callee::Direct(item("g")),
        args,
        dest: vec![Local(2)],
        next: BlockId(1),
        raised: raised.map(|b| (vec![Local(3)], BlockId(b))),
    };
    let table = if words == 1 { Repr::Heap } else { Repr::Scalar };
    let mut locals = vec![decl(Repr::Scalar, None), decl(table, Some("table"))];
    locals.extend([Repr::Heap, Repr::Heap, Repr::Heap, Repr::Scalar].map(|r| decl(r, None)));
    locals.extend([Repr::Heap, Repr::Scalar, Repr::Heap].map(|r| decl(r, None)));
    let params = [(0, ParamMode::Borrowed), (1, ParamMode::Ref)].map(|(l, mode)| Param {
        local: Local(l),
        mode,
    });
    Function {
        name: item("f"),
        params: params.to_vec(),
        hidden: 1,
        results: 1,
        locals,
        blocks: std::iter::once(block(entry, call)).chain(blocks).collect(),
        broken: false,
    }
}

/// The copy that the call of `g` loses reuse by, of `table`, for `need`.
fn lost(need: Need) -> Copied {
    Copied {
        block: BlockId(0),
        local: Local(1),
        callee: item("g"),
        need,
        at: line(4),
    }
}

/// Whether the counted entry gives the loaded word's reference to `_6`, rather than copy it.
fn handed(f: &Function) -> bool {
    let stmts = &f.blocks[0].stmts;
    assert_ne!(
        stmts.contains(&cleared(1)),
        stmts.contains(&Stmt::Dup(Local(6))),
        "{stmts:?}"
    );
    stmts.contains(&cleared(1))
}

#[test]
fn a_parameter_assigned_before_the_function_returns_hands_its_value_over() {
    let mut f = passing(1, None, vec![block(vec![store(1, 2)], ret())]);
    assert_eq!(count(&mut f), []);
    assert!(handed(&f));
}

#[test]
fn a_parameter_goes_back_to_the_caller_where_the_function_returns() {
    let mut f = passing(1, None, vec![block(Vec::new(), ret())]);
    let back = Need::Back {
        returns: true,
        raises: false,
    };
    assert_eq!(count(&mut f), [lost(back)]);
    assert!(!handed(&f));
}

#[test]
fn a_raise_between_the_use_and_the_assignment_keeps_the_copy() {
    let raise = block(Vec::new(), Terminator::Raise(vec![local(3)]));
    let mut f = passing(1, Some(2), vec![block(vec![store(1, 2)], ret()), raise]);
    let back = Need::Back {
        returns: false,
        raises: true,
    };
    assert_eq!(count(&mut f), [lost(back)]);
    assert!(!handed(&f));
}

#[test]
fn a_read_after_the_call_keeps_the_copy() {
    let read = vec![
        Stmt::Assign(Local(4), Rvalue::Load(local(1))),
        Stmt::Assign(Local(5), Rvalue::Tag(local(4))),
        store(1, 2),
    ];
    let mut f = passing(1, None, vec![block(read, ret())]);
    assert_eq!(count(&mut f), [lost(Need::After)]);
    assert!(!handed(&f));
}

#[test]
fn every_path_must_assign_the_parameter_but_one_that_panics() {
    let branch = |otherwise: Vec<Stmt>| {
        let branch = Terminator::Branch {
            cond: local(5),
            then: BlockId(2),
            otherwise: BlockId(3),
        };
        let panic = Terminator::Panic {
            kind: 0,
            detail: None,
            loc: Operand::word(0),
        };
        vec![
            block(vec![Stmt::Assign(Local(5), Rvalue::Tag(local(2)))], branch),
            block(Vec::new(), panic),
            block(otherwise, ret()),
        ]
    };
    let mut f = passing(1, None, branch(vec![store(1, 2)]));
    assert_eq!(count(&mut f), []);
    assert!(handed(&f));
    let mut f = passing(1, None, branch(Vec::new()));
    assert_eq!(count(&mut f).len(), 1);
    assert!(!handed(&f));
}

#[test]
fn each_word_of_a_parameter_is_handed_over_alone() {
    let mut f = passing(2, None, vec![block(vec![store(1, 2)], ret())]);
    let back = Need::Back {
        returns: true,
        raises: false,
    };
    assert_eq!(count(&mut f), [lost(back)]);
    let stmts = &f.blocks[0].stmts;
    assert!(stmts.contains(&cleared(1)), "{stmts:?}");
    assert!(stmts.contains(&Stmt::Dup(Local(8))), "{stmts:?}");
    let mut f = passing(2, None, vec![block(vec![store(1, 2), store(7, 2)], ret())]);
    assert_eq!(count(&mut f), []);
    let stmts = &f.blocks[0].stmts;
    assert!(
        stmts.contains(&cleared(1)) && stmts.contains(&cleared(7)),
        "{stmts:?}"
    );
}
