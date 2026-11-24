//! The consumers of iterators that give one element by its position or its order (views.consumers):
//! `first`, `last`, `nth`, and on elements with `Ord`, `max` and `min`, which keep the first of
//! equal elements. Each gives an `Option` as a native does (`crate::abi`).

use super::consumers::{Run, option};
use super::values::release;
use crate::abi::{COMPARE, GREATER, LESS, Ret, method2};
use crate::shape::Shape;

/// `it.first()`: the first element.
///
/// # Safety
///
/// `it` is a live iterator, and `out` points to room for the words of an element.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_first(
    loc: u64,
    _shape: u64,
    it: u64,
    out: u64,
) -> Ret {
    let out = out as usize as *mut u64;
    // SAFETY: as the caller guarantees; the element is owned.
    unsafe {
        let mut run = Run::new(loc, it);
        option(run.next(), run.shape(), out, false)
    }
}

/// `it.last()`: the last element.
///
/// # Safety
///
/// As for [`stilt_std_view_Iter_first`].
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_last(
    loc: u64,
    _shape: u64,
    it: u64,
    out: u64,
) -> Ret {
    let out = out as usize as *mut u64;
    // SAFETY: as the caller guarantees; each element is owned, and released once a later one
    // comes.
    unsafe {
        let mut run = Run::new(loc, it);
        let mut last = None;
        while let Some(x) = run.next() {
            if let Some(earlier) = last.replace(x) {
                release(earlier, run.shape());
            }
        }
        option(last, run.shape(), out, false)
    }
}

/// `it.nth(n)`: the element at `n`, counting from 0, and `None` for a negative `n`.
///
/// # Safety
///
/// As for [`stilt_std_view_Iter_first`].
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_nth(
    loc: u64,
    _shape: u64,
    it: u64,
    n: i64,
    out: u64,
) -> Ret {
    let out = out as usize as *mut u64;
    // SAFETY: as the caller guarantees; each element before the `n`th is released.
    unsafe {
        let mut run = Run::new(loc, it);
        let shape = run.shape();
        if n < 0 {
            return option(None, shape, out, false);
        }
        for _ in 0..n {
            match run.next() {
                Some(x) => release(x, shape),
                None => return option(None, shape, out, false),
            }
        }
        option(run.next(), shape, out, false)
    }
}

/// The element that `ord` puts furthest in the direction `beyond`, the first of equal ones.
///
/// # Safety
///
/// `it` is a live iterator, `ord` its elements' `Ord` dictionary, and `out` points to room for
/// the words of an element.
unsafe fn extreme(loc: u64, ord: u64, it: u64, out: *mut u64, beyond: u64) -> Ret {
    // SAFETY: as the caller guarantees; each element is owned, lent to `compare`, and released
    // once it loses.
    unsafe {
        let mut run = Run::new(loc, it);
        let shape: Shape = run.shape();
        let mut best: Option<u64> = None;
        while let Some(x) = run.next() {
            best = Some(match best {
                Some(b) if method2(loc, ord, COMPARE, x, b).value == beyond => {
                    release(b, shape);
                    x
                }
                Some(b) => {
                    release(x, shape);
                    b
                }
                None => x,
            });
        }
        option(best, shape, out, false)
    }
}

/// `it.max()`: the greatest element, the first of equal ones.
///
/// # Safety
///
/// As for [`extreme`].
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_max(
    loc: u64,
    _shape: u64,
    ord: u64,
    it: u64,
    out: u64,
) -> Ret {
    let out = out as usize as *mut u64;
    // SAFETY: as the caller guarantees.
    unsafe { extreme(loc, ord, it, out, GREATER) }
}

/// `it.min()`: the least element, the first of equal ones.
///
/// # Safety
///
/// As for [`extreme`].
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_min(
    loc: u64,
    _shape: u64,
    ord: u64,
    it: u64,
    out: u64,
) -> Ret {
    let out = out as usize as *mut u64;
    // SAFETY: as the caller guarantees.
    unsafe { extreme(loc, ord, it, out, LESS) }
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_std_view_Iter_first,
        stilt_std_view_Iter_last,
        stilt_std_view_Iter_nth,
        stilt_std_view_Iter_max,
        stilt_std_view_Iter_min,
    ]
}
