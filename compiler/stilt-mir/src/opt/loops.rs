//! The loops of a function: which block dominates which, and each natural loop with its
//! header, its body and the block that enters it from outside.

use std::collections::BTreeSet;

use crate::mir::{Function, Terminator};

/// The immediate dominator of each block the entry reaches, the entry being its own.
pub(crate) struct Dominators {
    idom: Vec<Option<usize>>,
}

impl Dominators {
    /// The dominators of `f`'s blocks, by the iterative algorithm of Cooper, Harvey and
    /// Kennedy over the blocks in reverse postorder.
    pub(crate) fn of(f: &Function) -> Self {
        let order = crate::opt::ranges::reverse_postorder(f);
        let mut rank = vec![usize::MAX; f.blocks.len()];
        for (i, &b) in order.iter().enumerate() {
            rank[b] = i;
        }
        let preds = predecessors(f);
        let mut idom = vec![None; f.blocks.len()];
        idom[0] = Some(0);
        let mut changed = true;
        while changed {
            changed = false;
            for &b in order.iter().skip(1) {
                let mut new = None;
                for &p in &preds[b] {
                    if idom[p].is_none() {
                        continue;
                    }
                    new = Some(new.map_or(p, |n| intersect(&idom, &rank, p, n)));
                }
                if new.is_some() && idom[b] != new {
                    idom[b] = new;
                    changed = true;
                }
            }
        }
        Self { idom }
    }

    /// `b` and each block that dominates it, up to the entry.
    pub(crate) fn chain(&self, b: usize) -> impl Iterator<Item = usize> + '_ {
        std::iter::successors(Some(b), |&at| self.idom[at].filter(|&up| up != at))
    }

    /// Whether every path from the entry to `b` passes through `a`.
    pub(crate) fn dominates(&self, a: usize, b: usize) -> bool {
        self.chain(b).any(|at| at == a)
    }
}

/// The nearest common dominator of `a` and `b`, by walking up from the later in reverse
/// postorder.
fn intersect(idom: &[Option<usize>], rank: &[usize], mut a: usize, mut b: usize) -> usize {
    while a != b {
        while rank[a] > rank[b] {
            a = idom[a].expect("a processed block's dominator");
        }
        while rank[b] > rank[a] {
            b = idom[b].expect("a processed block's dominator");
        }
    }
    a
}

/// Each block's predecessors.
pub(crate) fn predecessors(f: &Function) -> Vec<Vec<usize>> {
    let mut preds = vec![Vec::new(); f.blocks.len()];
    for (b, block) in f.blocks.iter().enumerate() {
        for s in block.term.successors() {
            preds[s.0 as usize].push(b);
        }
    }
    preds
}

/// A natural loop: a header that dominates the blocks that jump back to it, its latches.
pub(crate) struct Loop {
    pub(crate) header: usize,
    pub(crate) latches: Vec<usize>,
    /// The blocks of the loop, in their order in the function.
    pub(crate) blocks: Vec<usize>,
    /// The one block outside the loop that enters it, by a jump to the header, if there is
    /// exactly one.
    pub(crate) preheader: Option<usize>,
}

/// The natural loops of `f`, one per header, the smallest first, so that a loop comes before
/// each loop that holds it.
pub(crate) fn natural_loops(f: &Function, dom: &Dominators) -> Vec<Loop> {
    let preds = predecessors(f);
    let mut loops: Vec<Loop> = Vec::new();
    for (b, block) in f.blocks.iter().enumerate() {
        for s in block.term.successors() {
            let h = s.0 as usize;
            if !dom.dominates(h, b) {
                continue;
            }
            match loops.iter_mut().find(|l| l.header == h) {
                Some(l) => l.latches.push(b),
                None => loops.push(Loop {
                    header: h,
                    latches: vec![b],
                    blocks: Vec::new(),
                    preheader: None,
                }),
            }
        }
    }
    for l in &mut loops {
        l.blocks = body(&preds, l.header, &l.latches);
        l.preheader = preheader(f, &preds, l);
    }
    loops.sort_by_key(|l| l.blocks.len());
    loops
}

/// The header, and every block that reaches a latch without passing through the header, in
/// their order.
fn body(preds: &[Vec<usize>], header: usize, latches: &[usize]) -> Vec<usize> {
    let mut body = BTreeSet::from([header]);
    let mut stack: Vec<usize> = latches.to_vec();
    while let Some(b) = stack.pop() {
        if body.insert(b) {
            stack.extend(preds[b].iter().copied());
        }
    }
    body.into_iter().collect()
}

/// The loop's one predecessor outside it, if it enters the loop by a jump.
fn preheader(f: &Function, preds: &[Vec<usize>], l: &Loop) -> Option<usize> {
    let mut outside = preds[l.header]
        .iter()
        .filter(|&&p| l.blocks.binary_search(&p).is_err());
    let p = *outside.next()?;
    let jumps = matches!(f.blocks[p].term, Terminator::Goto(h) if h.0 as usize == l.header);
    (outside.next().is_none() && jumps).then_some(p)
}
