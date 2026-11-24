//! `par.fold`: the elements combined in the tree of par.fold-tree, which the list's length
//! alone fixes. On several threads, the parts are the subtrees a few levels down the tree, each
//! folded by one thread, and the calling thread combines them as the levels above say, each
//! combination once the parts below it have ended, so the calls of `f` are those of the
//! sequential run on the same values, and a float fold gives the same bits on any number of
//! threads (numbers.ieee-754).

use std::sync::atomic::{AtomicU64, Ordering};

use super::{PARTS_PER_THREAD, give, held, release, share_closure, threads_for};
use crate::abi::{Ret, call2, call2_out};
use crate::list::{self, get};
use crate::map::{dup_words, words_of};
use crate::object::{Header, dup, share_elements};
use crate::shape::Shape;
use crate::workers::Call;

/// The fold of one call: the list, the closure that combines two values, and their shape.
#[derive(Clone, Copy)]
struct Fold {
    loc: u64,
    xs: u64,
    f: u64,
    t: Shape,
}

/// Where par.fold-tree splits elements `lo` up to `hi`, of which there are at least two: after the
/// first half, rounded down.
fn middle(lo: usize, hi: usize) -> usize {
    lo + (hi - lo) / 2
}

impl Fold {
    /// `f` of two values, which it gives up.
    ///
    /// # Safety
    ///
    /// `left` and `right` are live values of the shape, which own their references.
    unsafe fn combine(self, left: u64, right: u64) -> u64 {
        // SAFETY: as the caller guarantees; `f` borrows both, and gives a value that owns its
        // references.
        unsafe {
            let combined = if self.t.words() > 1 {
                let mut words = vec![0u64; self.t.words()];
                call2_out(
                    self.loc,
                    self.f,
                    (left, right),
                    words.as_mut_ptr(),
                    std::ptr::null_mut(),
                );
                held(&words, self.t)
            } else {
                call2(self.loc, self.f, left, right, std::ptr::null_mut()).value
            };
            release(left, self.t);
            release(right, self.t);
            combined
        }
    }

    /// Elements `lo` up to `hi` folded: one element is itself, and more are their first half
    /// folded, combined with the rest folded.
    ///
    /// # Safety
    ///
    /// The list is live, with more than `hi` elements, and `lo < hi`.
    unsafe fn tree(self, lo: usize, hi: usize) -> u64 {
        if hi - lo == 1 {
            // SAFETY: as the caller guarantees.
            return unsafe { get(self.xs as *mut Header, lo) };
        }
        let mid = middle(lo, hi);
        // SAFETY: as the caller guarantees.
        unsafe {
            let left = self.tree(lo, mid);
            let right = self.tree(mid, hi);
            self.combine(left, right)
        }
    }
}

/// The parts of a fold of elements `lo` up to `hi`: its subtrees `depth` levels down, or less
/// where a subtree is one element, from the first to the last.
fn parts(lo: usize, hi: usize, depth: u32, into: &mut Vec<(usize, usize)>) {
    if depth == 0 || hi - lo == 1 {
        into.push((lo, hi));
        return;
    }
    let mid = middle(lo, hi);
    parts(lo, mid, depth - 1, into);
    parts(mid, hi, depth - 1, into);
}

/// The fold of elements `lo` up to `hi`, whose subtrees `depth` levels down are the parts of
/// `call`, which it finishes in order, from `*next` on, their values being in `values`.
///
/// # Safety
///
/// As for [`Fold::tree`], and the parts are those [`parts`] gives.
unsafe fn above(
    fold: Fold,
    (lo, hi, depth): (usize, usize, u32),
    call: &mut Call<'_>,
    values: &[AtomicU64],
    next: &mut usize,
) -> u64 {
    if depth == 0 || hi - lo == 1 {
        call.finish(*next);
        *next += 1;
        return values[*next - 1].load(Ordering::Relaxed);
    }
    let mid = middle(lo, hi);
    // SAFETY: as the caller guarantees.
    unsafe {
        let left = above(fold, (lo, mid, depth - 1), call, values, next);
        let right = above(fold, (mid, hi, depth - 1), call, values, next);
        fold.combine(left, right)
    }
}

/// The fold of a list of `n` elements, at least [`super::FEW`], on `threads` threads.
///
/// # Safety
///
/// As for [`Fold::tree`] over the whole list.
unsafe fn in_parts(fold: Fold, n: usize, threads: usize) -> u64 {
    // SAFETY: as the caller guarantees: `f` and what the elements share are marked, and each
    // part folds its own elements.
    unsafe {
        share_closure(fold.f);
        share_elements(fold.xs as *mut Header);
    }
    let depth = (PARTS_PER_THREAD * threads)
        .next_power_of_two()
        .trailing_zeros();
    let mut ranges = Vec::new();
    parts(0, n, depth, &mut ranges);
    let values: Vec<AtomicU64> = ranges.iter().map(|_| AtomicU64::new(0)).collect();
    let run = |k: usize| {
        let (lo, hi) = ranges[k];
        // SAFETY: as the caller guarantees.
        let value = unsafe { fold.tree(lo, hi) };
        values[k].store(value, Ordering::Relaxed);
    };
    let mut call = Call::start(ranges.len(), &run);
    // SAFETY: as the caller guarantees.
    unsafe { above(fold, (0, n, depth), &mut call, &values, &mut 0) }
}

/// `par.fold(xs, empty, f)`: `empty` for an empty list, and otherwise the elements combined
/// by `f` in the tree of par.fold-tree, its result given as a native gives a type parameter's.
///
/// # Safety
///
/// `xs` is a live list of elements of the shape `t`, `empty` a lent value of it, `f` a live
/// closure that combines two, raising nothing, and `out` points to room for the words of one
/// of several words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_par_fold(
    loc: u64,
    t: u64,
    xs: u64,
    empty: u64,
    f: u64,
    out: u64,
) -> Ret {
    let out = out as usize as *mut u64;
    let fold = Fold {
        loc,
        xs,
        f,
        t: Shape(t),
    };
    // SAFETY: as the caller guarantees; each element taken from the list has references of
    // its own, which the tree hands to `f`'s results.
    unsafe {
        let n = list::len(xs as *mut Header);
        if n == 0 {
            let words = words_of(&empty, fold.t);
            if fold.t.words() > 1 {
                dup_words(words, fold.t);
                std::ptr::copy_nonoverlapping(words.as_ptr(), out, words.len());
                return Ret::ok(0);
            }
            if fold.t.heap() {
                dup(empty);
            }
            return Ret::ok(empty);
        }
        let threads = threads_for(n);
        let value = if threads == 1 {
            fold.tree(0, n)
        } else {
            in_parts(fold, n, threads)
        };
        give(value, fold.t, out)
    }
}
