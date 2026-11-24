//! Building in the memory that a release keeps (values.consumed-parameters): which releases keep
//! memory, which objects are built in it, and where what nothing took goes back.

use stilt_hir::hir::{Item, Name};
use stilt_mir::FnRef;
use stilt_mir::mir::{
    Block, BlockId, Function, Heapness, Kept, Local, LocalDecl, Operand, Param, ParamMode, Repr,
    Runtime, Rvalue, Stmt, Terminator, Variant, data_layout, known_object,
};

use super::reuse;

fn decl(repr: Repr) -> LocalDecl {
    LocalDecl {
        repr,
        slot: false,
        grouped: false,
        borrowed: false,
        var: false,
        name: None,
        shown: None,
    }
}

fn local(i: u32) -> Operand {
    Operand::Local(Local(i))
}

/// A function whose first local is its location and whose second, a heap word, its one owned
/// parameter, with `heap` more heap locals, and these blocks.
fn function(heap: u32, blocks: Vec<Block>) -> Function {
    let mut locals = vec![decl(Repr::Scalar), decl(Repr::Heap)];
    locals.extend((0..heap).map(|_| decl(Repr::Heap)));
    Function {
        name: FnRef::Function(Item {
            home: Name::from("main"),
            name: Name::from("f"),
        }),
        params: vec![
            Param {
                local: Local(0),
                mode: ParamMode::Borrowed,
            },
            Param {
                local: Local(1),
                mode: ParamMode::Owned,
            },
        ],
        hidden: 1,
        results: 1,
        locals,
        blocks,
        broken: false,
    }
}

fn block(stmts: Vec<Stmt>, term: Terminator) -> Block {
    Block { stmts, term }
}

/// Field `index` of the object of two words that local 1 holds, into local `d`.
fn field(d: u32, index: u32) -> Stmt {
    Stmt::Assign(
        Local(d),
        Rvalue::Field {
            base: local(1),
            len: 2,
            index,
            variant: None,
        },
    )
}

/// A new object of two heap words into local `d`.
fn alloc(d: u32, a: u32, b: u32) -> Stmt {
    let fields = vec![
        (local(a), Heapness::Static(true)),
        (local(b), Heapness::Static(true)),
    ];
    Stmt::Assign(Local(d), Rvalue::Alloc(1, fields))
}

/// `match t { Pair(a, b) => Pair(b, a) }`, counted: the fields copied, `t` released, and a pair
/// of them built.
fn swap() -> Function {
    let stmts = vec![
        field(2, 0),
        Stmt::Dup(Local(2)),
        field(3, 1),
        Stmt::Dup(Local(3)),
        Stmt::Drop(Local(1)),
        alloc(4, 3, 2),
    ];
    function(3, vec![block(stmts, Terminator::Return(vec![local(4)]))])
}

/// Whether a function keeps memory anywhere or builds in it.
fn reuses(f: &Function) -> bool {
    f.blocks.iter().flat_map(|b| &b.stmts).any(|s| {
        matches!(
            s,
            Stmt::Assign(
                _,
                Rvalue::Runtime(Runtime::Reclaim, _) | Rvalue::AllocIn(..)
            )
        )
    })
}

#[test]
fn a_release_keeps_memory_for_the_object_built_after_it_and_hands_its_fields_over() {
    let mut f = swap();
    reuse(&mut f);
    let token = Local(5);
    assert_eq!(f.locals[5].repr, Repr::Scalar);
    let zero = Stmt::Assign(token, Rvalue::Use(Operand::word(0)));
    let reclaim = Rvalue::Runtime(
        Runtime::Reclaim,
        vec![
            local(1),
            Operand::word(2),
            Operand::word(3),
            Operand::word(0),
        ],
    );
    let stmts = &f.blocks[0].stmts;
    assert_eq!(stmts[..3], [zero.clone(), field(2, 0), field(3, 1)]);
    assert_eq!(
        stmts[3],
        Stmt::Assign(token, reclaim),
        "both fields taken over"
    );
    assert!(
        matches!(&stmts[4], Stmt::Assign(Local(4), Rvalue::AllocIn(m, 1, _, _)) if *m == Operand::Local(token)),
        "{stmts:?}"
    );
    assert_eq!(stmts[5], zero);
    let discard = Stmt::Effect(Runtime::Discard, vec![Operand::Local(token)]);
    assert_eq!(stmts[6..], [discard], "what nothing took goes back");
}

#[test]
fn an_object_of_another_size_or_built_before_takes_nothing() {
    let mut f = swap();
    f.blocks[0].stmts[5] = Stmt::Assign(
        Local(4),
        Rvalue::Alloc(1, vec![(local(3), Heapness::Static(true))]),
    );
    reuse(&mut f);
    assert!(!reuses(&f), "an object of one word");
    let mut f = swap();
    f.blocks[0].stmts.swap(4, 5);
    reuse(&mut f);
    assert!(!reuses(&f), "an object built before the release");
}

#[test]
fn a_copy_of_a_field_moves_into_the_branches_and_meets_its_release() {
    let mut f = swap();
    let stmts = std::mem::take(&mut f.blocks[0].stmts);
    f.blocks[0].stmts = stmts[..4].to_vec();
    f.blocks[0].term = Terminator::Branch {
        cond: local(0),
        then: BlockId(1),
        otherwise: BlockId(2),
    };
    f.blocks.push(block(
        stmts[4..].to_vec(),
        Terminator::Return(vec![local(4)]),
    ));
    let released = vec![
        Stmt::Drop(Local(2)),
        Stmt::Drop(Local(3)),
        Stmt::Drop(Local(1)),
    ];
    f.blocks
        .push(block(released, Terminator::Return(vec![local(0)])));
    reuse(&mut f);
    assert_eq!(f.blocks[0].stmts[1..], [field(2, 0), field(3, 1)]);
    assert_eq!(
        f.blocks[2].stmts,
        [Stmt::Drop(Local(1))],
        "each copy met its release"
    );
    let stmts = &f.blocks[1].stmts;
    assert!(
        matches!(&stmts[0], Stmt::Assign(_, Rvalue::Runtime(Runtime::Reclaim, args)) if args[2] == Operand::word(3)),
        "{stmts:?}"
    );
}

#[test]
fn a_release_in_a_loop_gives_back_what_it_kept_before_keeping_more() {
    let mut f = swap();
    let body = std::mem::take(&mut f.blocks[0].stmts);
    f.blocks[0].term = Terminator::Goto(BlockId(1));
    f.blocks.push(block(
        body,
        Terminator::Branch {
            cond: local(0),
            then: BlockId(1),
            otherwise: BlockId(2),
        },
    ));
    f.blocks
        .push(block(Vec::new(), Terminator::Return(vec![local(4)])));
    reuse(&mut f);
    let token = Operand::Local(Local(5));
    let stmts = &f.blocks[1].stmts;
    assert_eq!(
        stmts[4],
        Stmt::Effect(Runtime::Discard, vec![token.clone()])
    );
    assert!(matches!(
        &stmts[5],
        Stmt::Assign(_, Rvalue::Runtime(Runtime::Reclaim, _))
    ));
    assert_eq!(
        f.blocks[2].stmts,
        vec![Stmt::Effect(Runtime::Discard, vec![token])]
    );
}

#[test]
fn a_first_block_that_a_loop_enters_again_moves_after_a_new_one() {
    let mut f = swap();
    f.blocks[0].term = Terminator::Branch {
        cond: local(0),
        then: BlockId(0),
        otherwise: BlockId(1),
    };
    f.blocks
        .push(block(Vec::new(), Terminator::Return(vec![local(4)])));
    reuse(&mut f);
    assert_eq!(
        f.blocks[0],
        block(
            vec![Stmt::Assign(Local(5), Rvalue::Use(Operand::word(0)))],
            Terminator::Goto(BlockId(2))
        )
    );
    assert!(
        matches!(
            &f.blocks[2].term,
            Terminator::Branch {
                then: BlockId(2),
                ..
            }
        ),
        "the loop goes to the moved block"
    );
}

#[test]
fn a_known_variant_is_told_to_its_release_and_its_memory_keeps_what_stays() {
    // `match t { Pair(a, b) => Pair(a, b) }`, its fields read as those of variant 1, of two
    // heap words.
    let variant = Variant {
        tag: 1,
        layout: Some(data_layout(2, 0b11)),
    };
    let mut f = swap();
    for s in &mut f.blocks[0].stmts {
        if let Stmt::Assign(_, Rvalue::Field { variant: v, .. }) = s {
            *v = Some(variant);
        }
    }
    f.blocks[0].stmts[5] = alloc(4, 2, 3);
    reuse(&mut f);
    let stmts = &f.blocks[0].stmts;
    let known = Operand::word(known_object(Some(variant)));
    assert!(
        matches!(&stmts[3], Stmt::Assign(_, Rvalue::Runtime(Runtime::Reclaim, args)) if args[3] == known),
        "{stmts:?}"
    );
    let kept = Kept {
        header: true,
        words: 0b11,
    };
    assert!(
        matches!(&stmts[4], Stmt::Assign(_, Rvalue::AllocIn(_, 1, _, k)) if *k == kept),
        "the header and both fields stay: {stmts:?}"
    );
    // Swapped, the fields aren't where they were.
    let mut f = swap();
    if let Stmt::Assign(_, Rvalue::Field { variant: v, .. }) = &mut f.blocks[0].stmts[0] {
        *v = Some(variant);
    }
    reuse(&mut f);
    assert!(
        matches!(&f.blocks[0].stmts[4], Stmt::Assign(_, Rvalue::AllocIn(_, 1, _, k)) if k.words == 0),
        "{:?}",
        f.blocks[0].stmts
    );
}
