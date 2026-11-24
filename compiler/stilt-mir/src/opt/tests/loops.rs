//! The dominators and the natural loops that making a list unique once reads.

use super::{branch, counted_loop, function, goto, index, op, ret};
use crate::mir::ParamMode;
use crate::opt::loops::{Dominators, natural_loops};

#[test]
fn a_counted_loop_is_one_loop_entered_from_one_block() {
    // Block 1 enters the header, block 2, whose body, block 3, jumps back; block 4 exits.
    let f = counted_loop(1, index(1, op(4)));
    let dom = Dominators::of(&f);
    assert!(dom.dominates(1, 3) && dom.dominates(2, 4));
    assert!(!dom.dominates(3, 4));
    let loops = natural_loops(&f, &dom);
    assert_eq!(loops.len(), 1);
    let l = &loops[0];
    assert_eq!(
        (l.header, &l.latches, &l.blocks),
        (2, &vec![3], &vec![2, 3])
    );
    assert_eq!(l.preheader, Some(1));
}

#[test]
fn an_inner_loop_comes_before_the_loop_that_holds_it() {
    // Block 1 heads the outer loop, block 2 the inner, which block 3 jumps back to; block 4
    // jumps back to block 1, and block 5 returns.
    let blocks = vec![
        goto(Vec::new(), 1),
        branch(Vec::new(), 1, 2, 5),
        branch(Vec::new(), 1, 3, 4),
        goto(Vec::new(), 2),
        goto(Vec::new(), 1),
        ret(Vec::new()),
    ];
    let f = function(&[ParamMode::Borrowed], 0, &[], blocks);
    let loops = natural_loops(&f, &Dominators::of(&f));
    let heads: Vec<usize> = loops.iter().map(|l| l.header).collect();
    assert_eq!(heads, [2, 1]);
    // The inner loop is entered from block 1, which branches rather than jumps, and the outer
    // from block 0.
    assert_eq!((loops[0].preheader, loops[1].preheader), (None, Some(0)));
}

#[test]
fn a_loop_entered_from_two_blocks_has_no_block_that_enters_it() {
    // Blocks 1 and 2 both jump to block 3, which loops on itself.
    let blocks = vec![
        branch(Vec::new(), 1, 1, 2),
        goto(Vec::new(), 3),
        goto(Vec::new(), 3),
        branch(Vec::new(), 1, 3, 4),
        ret(Vec::new()),
    ];
    let f = function(&[ParamMode::Borrowed], 0, &[], blocks);
    let loops = natural_loops(&f, &Dominators::of(&f));
    assert_eq!(loops.len(), 1);
    assert_eq!((loops[0].header, loops[0].preheader), (3, None));
}

#[test]
fn a_read_of_a_constant_that_cant_panic_leaves_the_loop() {
    use crate::FnRef;
    use crate::mir::{Repr, Rvalue};
    use std::sync::Arc;

    // Block 1 enters the header, block 2, whose body, block 3, reads constants and jumps back;
    // block 4 exits. Only the read of the constant that can't panic moves to block 1.
    let read = |d, safe| {
        super::assign(
            d,
            Rvalue::Constant(FnRef::Main, op(0), 0, Arc::from([Repr::Heap]), safe),
        )
    };
    let blocks = vec![
        goto(Vec::new(), 1),
        goto(Vec::new(), 2),
        branch(Vec::new(), 1, 3, 4),
        goto(vec![read(2, true), read(3, false)], 2),
        ret(Vec::new()),
    ];
    let mut f = function(&[ParamMode::Borrowed], 3, &[2, 3], blocks);
    crate::opt::constants::hoist(&mut f);
    assert_eq!(f.blocks[1].stmts, [read(2, true)]);
    assert_eq!(f.blocks[3].stmts, [read(3, false)]);
}
