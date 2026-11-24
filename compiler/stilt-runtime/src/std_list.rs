//! The native methods of `List<T>` (std.lists).
//!
//! Each takes the witness of `T` after its location, which is the shape of its values
//! (`crate::shape`), then its arguments: a list it borrows, or the slot of an `inout` one, which
//! it makes unique before it writes it. It takes and gives an element in the one word that holds
//! it where a type parameter stands, which `crate::list` converts. An element it keeps gets
//! references of its own; one it returns, out of a list it takes it from, keeps the list's.

use crate::abi::{COMPARE, GREATER, NONE, Ret, call1, call1_out, method2, some};
use crate::layout::{SIGNED_ORDER, UNSIGNED_ORDER};
use crate::map;
use crate::object::{self, Header, unique};
use crate::shape::Shape;
use crate::sort::{merge_sort, sort_integers};
use crate::support::out_of_bounds;
use crate::{list, panic, structural};

/// The number of elements of a live list.
///
/// # Safety
///
/// `xs` is a live list.
unsafe fn len(xs: u64) -> usize {
    // SAFETY: the caller guarantees the list is alive.
    unsafe { list::len(xs as *mut Header) }
}

/// `List.new()`.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_prelude_List_new(_loc: u64, shape: u64) -> Ret {
    Ret::ok(list::new(0, Shape(shape)) as u64)
}

/// `xs.len()`.
///
/// # Safety
///
/// `xs` is a live list.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_List_len(_loc: u64, _shape: u64, xs: u64) -> Ret {
    // SAFETY: the caller guarantees the list is alive.
    Ret::ok(unsafe { len(xs) } as u64)
}

/// `xs.is_empty()`.
///
/// # Safety
///
/// `xs` is a live list.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_List_is_empty(
    _loc: u64,
    _shape: u64,
    xs: u64,
) -> Ret {
    // SAFETY: the caller guarantees the list is alive.
    Ret::ok(u64::from(unsafe { len(xs) } == 0))
}

/// `xs.get(i)`: `Some` of element `i`, or `None` out of bounds, an element of several words
/// written to the memory `out` points to (`crate::abi`).
///
/// # Safety
///
/// `xs` is a live list, and `out` points to room for an element of several words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_List_get(
    _loc: u64,
    _shape: u64,
    xs: u64,
    i: i64,
    out: u64,
) -> Ret {
    let out = out as usize as *mut u64;
    // SAFETY: the caller guarantees the list is alive; the index is in bounds.
    unsafe {
        let Some(i) = usize::try_from(i).ok().filter(|&i| i < len(xs)) else {
            return NONE;
        };
        some(list::give_copy(xs as *mut Header, i, out))
    }
}

/// `xs.push(x)`: appends `x`.
///
/// # Safety
///
/// `slot` holds a live list, and `x` is a live element.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_List_push(
    _loc: u64,
    _shape: u64,
    slot: u64,
    x: u64,
) -> Ret {
    let slot = slot as usize as *mut u64;
    // SAFETY: the caller guarantees the slot holds a list and the element is alive; the list
    // has room for it once reserved.
    unsafe {
        let xs = list::reserve(slot);
        let len = list::len(xs);
        list::write(xs, len, x);
        list::set_len(xs, len + 1);
    }
    Ret::unit()
}

/// `xs.pop()`: removes the last element and returns it, or `None` when the list is empty, an
/// element of several words written to the memory `out` points to.
///
/// # Safety
///
/// `slot` holds a live list, and `out` points to room for an element of several words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_List_pop(
    _loc: u64,
    _shape: u64,
    slot: u64,
    out: u64,
) -> Ret {
    let slot = slot as usize as *mut u64;
    let out = out as usize as *mut u64;
    // SAFETY: the caller guarantees the slot holds a list.
    unsafe {
        let len = len(*slot);
        if len == 0 {
            return NONE;
        }
        let xs = unique(slot);
        some(list::remove(xs, len - 1, out))
    }
}

/// `xs.insert(i, x)`: `x` at index `i`, the elements from `i` on moved after it, or a panic
/// with `bounds` unless `0 ≤ i ≤ len`.
///
/// # Safety
///
/// `slot` holds a live list, and `x` is a live element.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_List_insert(
    loc: u64,
    _shape: u64,
    slot: u64,
    i: i64,
    x: u64,
) -> Ret {
    let slot = slot as usize as *mut u64;
    // SAFETY: the caller guarantees the slot holds a list and the element is alive.
    unsafe {
        let len = len(*slot);
        let at = usize::try_from(i).ok().filter(|&i| i <= len);
        let Some(at) = at else {
            out_of_bounds(loc, i, len)
        };
        list::insert(unique(slot), at, x);
    }
    Ret::unit()
}

/// `xs.remove(i)`: removes element `i` and returns it, or a panic with `bounds` unless
/// `0 ≤ i < len`, an element of several words written to the memory `out` points to.
///
/// # Safety
///
/// `slot` holds a live list, and `out` points to room for an element of several words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_List_remove(
    loc: u64,
    _shape: u64,
    slot: u64,
    i: i64,
    out: u64,
) -> Ret {
    let slot = slot as usize as *mut u64;
    let out = out as usize as *mut u64;
    // SAFETY: the caller guarantees the slot holds a list.
    unsafe {
        let len = len(*slot);
        let at = usize::try_from(i).ok().filter(|&i| i < len);
        let Some(at) = at else {
            out_of_bounds(loc, i, len)
        };
        Ret::ok(list::remove(unique(slot), at, out))
    }
}

/// `xs.slice(start, end)`: the elements from `start` up to `end`, or a panic with `bounds`
/// unless `0 ≤ start ≤ end ≤ len`.
///
/// # Safety
///
/// `xs` is a live list.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_List_slice(
    loc: u64,
    _shape: u64,
    xs: u64,
    start: i64,
    end: i64,
) -> Ret {
    // SAFETY: the caller guarantees the list is alive.
    let len = unsafe { len(xs) };
    let range = usize::try_from(start)
        .ok()
        .zip(usize::try_from(end).ok())
        .filter(|&(s, e)| s <= e && e <= len);
    let Some((s, e)) = range else {
        panic::panic(
            loc,
            panic::BOUNDS,
            &format!("the range {start}..{end} is out of bounds for a list of length {len}"),
        )
    };
    // SAFETY: as above, and the range is in bounds.
    Ret::ok(unsafe { structural::slice(xs as *mut Header, s, e) } as u64)
}

/// `xs.sorted_by(key)`: the elements in ascending order of their keys, stable.
///
/// # Safety
///
/// `ord` is the key type's `Ord` dictionary, `xs` a live list, `key` a live closure from its
/// elements to keys, and `err` the memory for an error of several words that `key` raises,
/// which [`crate::abi::call1`] gives it.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_List_sorted_by(
    loc: u64,
    _shape: u64,
    key_shape: u64,
    ord: u64,
    xs: u64,
    key: u64,
    err: u64,
) -> Ret {
    let err = err as usize as *mut u64;
    // SAFETY: as the caller guarantees.
    unsafe { sort(loc, Shape(key_shape), ord, xs, (key, err), false) }
}

/// `xs.sorted_desc_by(key)`: the elements in descending order of their keys, stable.
///
/// # Safety
///
/// As for `stilt_std_prelude_List_sorted_by`.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_List_sorted_desc_by(
    loc: u64,
    _shape: u64,
    key_shape: u64,
    ord: u64,
    xs: u64,
    key: u64,
    err: u64,
) -> Ret {
    let err = err as usize as *mut u64;
    // SAFETY: as the caller guarantees.
    unsafe { sort(loc, Shape(key_shape), ord, xs, (key, err), true) }
}

/// Calls `key` once per element, in order, then sorts the elements by their keys, keeping
/// equal keys in their order (std.list-sorting): as integers when `ord`'s tag says the keys'
/// order is that of integers, and otherwise through `ord`. An error that `key` raises is raised
/// again, once the keys computed so far are released, an error of several words having gone to
/// the memory `err` points to. Each element is lent to `key` in the one
/// word that holds it for a native, a box on the stack for one of several words, since the key
/// it gives owns its references. A key of several words is written to memory of this function's,
/// one key after the other, which each is lent to `ord` from (`crate::abi`).
///
/// # Safety
///
/// As for `stilt_std_prelude_List_sorted_by`.
unsafe fn sort(
    loc: u64,
    key_shape: Shape,
    ord: u64,
    xs: u64,
    (key, err): (u64, *mut u64),
    descending: bool,
) -> Ret {
    let list = xs as *mut Header;
    // SAFETY: the caller guarantees the list is alive; `key` can't reach it to change it.
    let (count, shape) = unsafe { (list::len(list), list::shape(list)) };
    let kw = if key_shape.size() > 8 {
        key_shape.words()
    } else {
        1
    };
    let mut keys = Keys::new(key_shape, kw, count);
    // Each key, or for one of several words its place, with its element's position, which the
    // sort carries along.
    let mut keyed: Vec<(u64, usize)> = Vec::with_capacity(count);
    let mut loan = list::Loan::new();
    for i in 0..count {
        // SAFETY: the element exists, and `key` is a closure that takes the elements, which
        // borrows the lent word for the call.
        let given = unsafe {
            let element = list::lend(list, i, &mut loan);
            if kw == 1 {
                call1(loc, key, element, err)
            } else {
                call1_out(loc, key, element, keys.room(i), err)
            }
        };
        if given.raised != 0 {
            keys.release(&keyed);
            return given;
        }
        keyed.push((if kw == 1 { given.value } else { i as u64 }, i));
    }
    // SAFETY: the caller guarantees `ord` is the keys' `Ord`, a live dictionary.
    match unsafe { (*(ord as *const Header)).tag } {
        SIGNED_ORDER => sort_integers(&mut keyed, true, descending),
        UNSIGNED_ORDER => sort_integers(&mut keyed, false, descending),
        _ => {
            let after = |first: &(u64, usize), second: &(u64, usize)| {
                let (first, second) = if descending {
                    (second.0, first.0)
                } else {
                    (first.0, second.0)
                };
                let compare = |first: u64, second: u64| {
                    // SAFETY: as above.
                    unsafe { method2(loc, ord, COMPARE, first, second).value == GREATER }
                };
                if kw == 1 {
                    return compare(first, second);
                }
                let mut loans = (list::Loan::new(), list::Loan::new());
                compare(
                    keys.lent(first, &mut loans.0),
                    keys.lent(second, &mut loans.1),
                )
            };
            merge_sort(&mut keyed, &after);
        }
    }
    let sorted = list::new(count, shape);
    for (j, &(_, i)) in keyed.iter().enumerate() {
        // SAFETY: the new list has room for every element, which gets references of its own.
        unsafe { list::copy_element(list, i, sorted, j) };
    }
    // SAFETY: the new list's first `count` elements are set.
    unsafe { list::set_len(sorted, count) };
    keys.release(&keyed);
    Ret::ok(sorted as u64)
}

/// The keys of a sort of several words each, one after the other, which own their references.
struct Keys {
    shape: Shape,
    words: usize,
    memory: Vec<u64>,
}

impl Keys {
    fn new(shape: Shape, words: usize, n: usize) -> Self {
        let memory = if words > 1 {
            vec![0; n * words]
        } else {
            Vec::new()
        };
        Self {
            shape,
            words,
            memory,
        }
    }

    /// The room of key `i`.
    fn room(&mut self, i: usize) -> *mut u64 {
        self.memory[i * self.words..].as_mut_ptr()
    }

    /// The key that `k` stands for, lent in one word: itself for a key of one word, and
    /// otherwise a box in `loan` of the words of the key at that place.
    fn lent(&self, k: u64, loan: &mut list::Loan) -> u64 {
        if self.words == 1 {
            return k;
        }
        let at = usize::try_from(k).unwrap_or(0) * self.words;
        map::lent(&self.memory[at..at + self.words], self.shape, loan)
    }

    /// Releases the keys of `keyed`.
    fn release(&self, keyed: &[(u64, usize)]) {
        for &(k, _) in keyed {
            if self.words == 1 {
                // SAFETY: each key of one word is one that the sort owns.
                unsafe { release_word(k, self.shape.heap()) };
            } else {
                let at = usize::try_from(k).unwrap_or(0) * self.words;
                // SAFETY: as above.
                unsafe { map::drop_words(&self.memory[at..at + self.words], self.shape) };
            }
        }
    }
}

/// Releases a word that the caller owns, in a list of `heap` words.
///
/// # Safety
///
/// `x` owns a reference, if it is a heap word.
unsafe fn release_word(x: u64, heap: bool) {
    if heap {
        // SAFETY: the caller guarantees the word owns a reference.
        unsafe { object::drop(x) }
    }
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_std_prelude_List_new,
        stilt_std_prelude_List_len,
        stilt_std_prelude_List_is_empty,
        stilt_std_prelude_List_get,
        stilt_std_prelude_List_push,
        stilt_std_prelude_List_pop,
        stilt_std_prelude_List_insert,
        stilt_std_prelude_List_remove,
        stilt_std_prelude_List_slice,
        stilt_std_prelude_List_sorted_by,
        stilt_std_prelude_List_sorted_desc_by,
    ]
}
