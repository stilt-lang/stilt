//! The functions of `std.par` (par.std-par). Each means its sequential run
//! (par.sequential-meaning): `map` and `each` call `f` on the elements from the first to the last,
//! `both` calls `f`, then `g`, and `fold` combines the elements in the balanced tree that the
//! list's length fixes. Its closures perform no effect and reach no shared value
//! (par.what-runs-in-parallel), so a run in parts on several threads (`crate::workers`) gives what
//! the sequential run gives, whatever the number of threads: each part writes its own elements, a
//! fold's parts are subtrees of the tree that the caller then combines as the tree says, and a
//! panic is the first in that order (par.panics).
//!
//! Before a call runs on several threads, its closures are marked shared with what they
//! capture, which every thread reads, and so is what the list's elements reach through an
//! object that something else references too (`crate::object::share_elements`), so that the
//! threads count those objects atomically. A call over fewer than [`FEW`] elements, or
//! on a system of one core, runs on the calling thread, and marks nothing.

mod fold;
#[cfg(test)]
mod tests;

use fold::stilt_std_par_fold;

use crate::abi::{Ret, call1, call1_out};
use crate::list::{self, Loan, box_of, lend, update};
use crate::map::words_of;
use crate::object::{Header, drop, free_box, share, share_elements, unique};
use crate::shape::Shape;
use crate::workers::{self, Call};

/// The fewest elements that a call runs on several threads: a call over fewer runs on the
/// calling thread, since starting parts on other threads costs more than a few calls of `f`
/// save. `par.both` always runs on two.
const FEW: usize = 4;

/// The parts that each thread takes, on average: more parts than threads even out parts that
/// take longer than others.
const PARTS_PER_THREAD: usize = 4;

/// The number of threads a call over `n` elements runs on, the calling thread among them.
fn threads_for(n: usize) -> usize {
    if n < FEW { 1 } else { workers::threads() }
}

/// Elements `k * n / parts` up to `(k + 1) * n / parts`: part `k` of `parts` of `n` elements.
fn part(n: usize, parts: usize, k: usize) -> std::ops::Range<usize> {
    k * n / parts..(k + 1) * n / parts
}

/// Runs a call of `parts` parts, part `k` being `run(k)`, on the calling thread and the pool's,
/// and finishes the parts in order.
fn in_parts(parts: usize, run: &(impl Fn(usize) + Sync)) {
    let mut call = Call::start(parts, run);
    for k in 0..parts {
        call.finish(k);
    }
}

/// Marks a closure that several threads call shared, with what it captures.
///
/// # Safety
///
/// `f` is a live closure that only the calling thread reaches unless it is marked.
unsafe fn share_closure(f: u64) {
    // SAFETY: as the caller guarantees.
    unsafe { share(f, Shape::word(true)) }
}

/// A value that a closure a native calls gives, in the one word that holds it where a type
/// parameter stands: its word, or a box of the words it wrote, which owns them.
fn held(words: &[u64], shape: Shape) -> u64 {
    if shape.words() > 1 {
        box_of(words, shape)
    } else {
        words.first().copied().unwrap_or(0)
    }
}

/// Releases a value held in one word.
///
/// # Safety
///
/// `x` is a live value of the shape, which owns its references.
unsafe fn release(x: u64, shape: Shape) {
    if shape.words() > 1 || shape.heap() {
        // SAFETY: as the caller guarantees; a box releases the words it holds.
        unsafe { drop(x) }
    }
}

/// Writes a value held in one word, which it gives up, to `out` as the words of its layout, or
/// gives its word: a native's result of a type parameter (`crate::abi`).
///
/// # Safety
///
/// `x` is a live value of the shape, which owns its references, and `out` points to room for
/// its words when it has several.
unsafe fn give(x: u64, shape: Shape, out: *mut u64) -> Ret {
    if shape.words() <= 1 {
        return Ret::ok(x);
    }
    // SAFETY: as the caller guarantees: the box's words move to `out`, and the box goes alone.
    unsafe {
        let words = words_of(&x, shape);
        std::ptr::copy_nonoverlapping(words.as_ptr(), out, words.len());
        free_box(x as *mut Header);
    }
    Ret::ok(0)
}

/// `par.map(xs, f)`: the list of `f` of each element, in order.
///
/// # Safety
///
/// `xs` is a live list of elements of the shape `t`, and `f` a live closure from them to values
/// of the shape `u`, which raises nothing.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_par_map(
    loc: u64,
    _elem: u64,
    result: u64,
    xs: u64,
    f: u64,
) -> Ret {
    // SAFETY: as the caller guarantees: each part writes its own elements of the new list,
    // which has room for them all, and only once every part has ended does it hold them.
    unsafe {
        let n = list::len(xs as *mut Header);
        let mapped = list::new(n, Shape(result)) as u64;
        let threads = threads_for(n);
        if threads == 1 {
            map_part(loc, f, (xs, mapped), 0..n);
        } else {
            share_closure(f);
            share_elements(xs as *mut Header);
            let parts = n.min(PARTS_PER_THREAD * threads);
            in_parts(parts, &|k| {
                map_part(loc, f, (xs, mapped), part(n, parts, k));
            });
        }
        list::set_len(mapped as *mut Header, n);
        Ret::ok(mapped)
    }
}

/// Writes `f` of each element of `xs` in `range` as the same element of `mapped`.
///
/// # Safety
///
/// `xs` is a live list, `mapped` a list of `f`'s results with room for the elements in `range`,
/// which no other thread writes, and `f` as for [`stilt_std_par_map`].
unsafe fn map_part(loc: u64, f: u64, (xs, mapped): (u64, u64), range: std::ops::Range<usize>) {
    let (xs, mapped) = (xs as *mut Header, mapped as *mut Header);
    // SAFETY: as the caller guarantees: `f` borrows each lent element, and gives a value that
    // owns its references, which the new list takes.
    unsafe {
        let result = list::shape(mapped);
        let mut loan = Loan::new();
        for i in range {
            let element = lend(xs, i, &mut loan);
            let at = list::at(mapped, i);
            if result.words() > 1 {
                // The closure writes its result to memory that holds zeros.
                let out = at.cast::<u64>();
                std::ptr::write_bytes(out, 0, result.words());
                call1_out(loc, f, element, out, std::ptr::null_mut());
            } else {
                let value = call1(loc, f, element, std::ptr::null_mut()).value;
                if result.packed() {
                    list::write(mapped, i, value);
                } else {
                    at.cast::<u64>().write(value);
                }
            }
        }
    }
}

/// `par.each(inout xs, f)`: calls `f` on each element of `xs` in place, from the first to the last,
/// once the list is unique (par.writes-in-place). `f` takes a pointer to the words of an element.
///
/// # Safety
///
/// `slot` holds a live list of elements of the shape `t`, and `f` is a live closure that takes
/// a pointer to the words of one, and raises nothing.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_par_each(loc: u64, _t: u64, slot: u64, f: u64) -> Ret {
    let slot = slot as usize as *mut u64;
    // SAFETY: as the caller guarantees; the list is unique, and each part writes its own
    // elements, which `f` alone reaches meanwhile.
    unsafe {
        let xs = unique(slot);
        let n = list::len(xs);
        let threads = threads_for(n);
        if threads == 1 {
            each_part(loc, f, xs as u64, 0..n);
        } else {
            share_closure(f);
            share_elements(xs);
            let parts = n.min(PARTS_PER_THREAD * threads);
            let xs = xs as u64;
            in_parts(parts, &|k| each_part(loc, f, xs, part(n, parts, k)));
        }
    }
    Ret::unit()
}

/// Calls `f` on each element of `xs` in `range` in place.
///
/// # Safety
///
/// `xs` is a live list that nothing else references, whose elements in `range` no other thread
/// reaches, and `f` as for [`stilt_std_par_each`].
unsafe fn each_part(loc: u64, f: u64, xs: u64, range: std::ops::Range<usize>) {
    let xs = xs as *mut Header;
    // SAFETY: as the caller guarantees: an element held in words of its own is written in
    // place, and a packed one through a word that `update` writes back.
    unsafe {
        let packed = list::shape(xs).packed();
        for i in range {
            if packed {
                update(xs, i, |words| {
                    call1(loc, f, words.as_mut_ptr() as u64, std::ptr::null_mut());
                });
            } else {
                call1(loc, f, list::at(xs, i) as u64, std::ptr::null_mut());
            }
        }
    }
}

/// The value of a closure of no parameters, in the one word that holds it.
///
/// # Safety
///
/// `f` is a live closure of no parameters, which gives a value of the shape and raises
/// nothing.
unsafe fn run(loc: u64, f: u64, shape: Shape) -> u64 {
    // SAFETY: as the caller guarantees.
    unsafe { crate::std_lazy::compute(loc, f, shape) }
}

/// `par.both(f, g)`: the pair of `f()` and `g()`, `f` called first, on the calling thread, and
/// `g` on another, their words then written to `out`.
///
/// # Safety
///
/// `first` and `second` are live closures of no parameters giving values of their shapes,
/// which raise nothing, and `out` points to room for the words of both, or is null when they
/// have none.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_par_both(
    loc: u64,
    first_shape: u64,
    second_shape: u64,
    first: u64,
    second: u64,
    out: u64,
) -> Ret {
    let out = out as usize as *mut u64;
    let shapes = [Shape(first_shape), Shape(second_shape)];
    let closures = [first, second];
    let values = [0, 1].map(|_| std::sync::atomic::AtomicU64::new(0));
    let compute = |k: usize| {
        // SAFETY: as the caller guarantees.
        let value = unsafe { run(loc, closures[k], shapes[k]) };
        values[k].store(value, std::sync::atomic::Ordering::Relaxed);
    };
    // SAFETY: as the caller guarantees; each value's words move to `out`.
    unsafe {
        if workers::threads() == 1 {
            compute(0);
            compute(1);
        } else {
            // `f` runs on the calling thread, so only what `g` reaches meets another thread.
            share_closure(second);
            in_parts(2, &compute);
        }
        let mut room = out;
        for (value, shape) in values.into_iter().zip(shapes) {
            let (value, len) = (value.into_inner(), shape.words());
            if len > 0 {
                let words = words_of(&value, shape).to_vec();
                std::ptr::copy_nonoverlapping(words.as_ptr(), room, len);
                if len > 1 {
                    free_box(value as *mut Header);
                }
                room = room.add(len);
            }
        }
    }
    Ret::unit()
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_std_par_map,
        stilt_std_par_each,
        stilt_std_par_both,
        stilt_std_par_fold,
    ]
}
