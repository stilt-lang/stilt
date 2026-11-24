//! Removing the blocks that a function's entry can't reach.

use crate::mir::{BlockId, Function, Terminator};

/// The function with only the blocks its entry reaches, in their order.
pub(crate) fn reachable(mut f: Function) -> Function {
    keep_reachable(&mut f);
    f
}

/// Keeps only the blocks of `f` that its entry reaches, in their order.
pub(crate) fn keep_reachable(f: &mut Function) {
    let mut seen = vec![false; f.blocks.len()];
    let mut stack = vec![BlockId(0)];
    while let Some(b) = stack.pop() {
        if std::mem::replace(&mut seen[b.0 as usize], true) {
            continue;
        }
        stack.extend(f.blocks[b.0 as usize].term.successors());
    }
    let mut renumber = vec![None; f.blocks.len()];
    let mut next = 0u32;
    for (i, &kept) in seen.iter().enumerate() {
        if kept {
            renumber[i] = Some(BlockId(next));
            next += 1;
        }
    }
    let new = |b: BlockId| renumber[b.0 as usize].expect("a reachable block's successor");
    let blocks = std::mem::take(&mut f.blocks);
    f.blocks = blocks
        .into_iter()
        .zip(seen)
        .filter_map(|(mut block, kept)| {
            kept.then(|| {
                retarget(&mut block.term, new);
                block
            })
        })
        .collect();
}

/// Renames the blocks a terminator jumps to.
pub(crate) fn retarget(term: &mut Terminator, new: impl Fn(BlockId) -> BlockId) {
    match term {
        Terminator::Goto(b) => *b = new(*b),
        Terminator::Branch {
            then, otherwise, ..
        } => {
            *then = new(*then);
            *otherwise = new(*otherwise);
        }
        Terminator::Switch {
            cases, otherwise, ..
        } => {
            for (_, b) in cases {
                *b = new(*b);
            }
            *otherwise = new(*otherwise);
        }
        Terminator::Call { next, raised, .. } => {
            *next = new(*next);
            if let Some((_, b)) = raised.as_mut() {
                *b = new(*b);
            }
        }
        Terminator::Return(_)
        | Terminator::Raise(_)
        | Terminator::Panic { .. }
        | Terminator::Unreachable => {}
    }
}
