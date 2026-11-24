//! The structural impls that compiled code calls rather than inlines (traits.prelude-traits and
//! traits.structural-impls): those of strings and lists, the hashes they build on, and the
//! comparison of constant patterns (patterns.constants).
//!
//! A structural hash is FNV-1a over the words of a value, a variant's index or a list's length
//! first, as the reference interpreter computes it, so that a key type's `hash` and `eq` run
//! as often, and in the same order, in both (std.finding-keys). Programs can't observe the
//! hashes themselves (traits.prelude-traits).

use crate::abi::{COMPARE, EQ, EQUAL, HASH, SHOW_NESTED, method1, method2, ordering};
use crate::list::{self, Loan};
use crate::object::{self, DATA, Header, LIST, STR, data_field, data_field_is_heap, pointer};
use crate::text;

pub(crate) const FNV: u64 = 0xcbf2_9ce4_8422_2325;
const PRIME: u64 = 0x0000_0100_0000_01b3;

/// `h` with the word `x` mixed in.
pub(crate) const fn mix(h: u64, x: u64) -> u64 {
    (h ^ x).wrapping_mul(PRIME)
}

/// The hash a structural hash starts from, which is also the hash of `()`.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_hash_start() -> u64 {
    FNV
}

/// `h` with the word `x` mixed in.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_hash_mix(h: u64, x: u64) -> u64 {
    mix(h, x)
}

/// The hash of an integer or a `bool`.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_hash_word(x: u64) -> u64 {
    mix(FNV, x)
}

/// The hash of a string: each of its bytes mixed in turn.
///
/// # Safety
///
/// `s` is a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_hash_str(s: u64) -> u64 {
    // SAFETY: the caller guarantees the string is alive.
    unsafe { text::bytes(&s) }
        .iter()
        .fold(FNV, |h, &b| mix(h, u64::from(b)))
}

/// Whether two strings are equal, byte for byte.
///
/// # Safety
///
/// `a` and `b` are live strings.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_str_eq(a: u64, b: u64) -> u64 {
    // SAFETY: the caller guarantees the strings are alive.
    u64::from(a == b || unsafe { text::bytes(&a) == text::bytes(&b) })
}

/// The order of two strings, by their bytes, as an `Ordering`.
///
/// # Safety
///
/// `a` and `b` are live strings.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_str_compare(a: u64, b: u64) -> u64 {
    // SAFETY: the caller guarantees the strings are alive.
    ordering(unsafe { text::bytes(&a).cmp(text::bytes(&b)) })
}

/// Whether two values are the same by structure, for a constant pattern: constants hold no
/// floats or functions, so their words compare (patterns.constants). The lowest bit of `heap`, a
/// witness or 0 or 1, tells whether the values are heap words.
///
/// # Safety
///
/// `a` and `b` are live values of one type.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_same(a: u64, b: u64, heap: u64) -> u64 {
    // SAFETY: the caller guarantees the values are alive.
    u64::from(heap & 1 == 0 && a == b || heap & 1 != 0 && unsafe { same(a, b) })
}

/// Whether two heap words are the same by structure. A string may be held in its word or in an
/// object, which an object's kind tells, so a string object and an immediate of its type compare
/// by their bytes; two immediates are the same only if their words are, as two variants without
/// payloads or two strings held in their words are.
///
/// # Safety
///
/// `left` and `right` are live heap words of one type.
unsafe fn same(left: u64, right: u64) -> bool {
    if left == right {
        return true;
    }
    let (Some(l), Some(r)) = (pointer(left), pointer(right)) else {
        return match pointer(left).or(pointer(right)) {
            // SAFETY: the caller guarantees the object is alive, and the immediate of its type.
            Some(o) if unsafe { (*o).kind } == STR => unsafe {
                text::bytes(&left) == text::bytes(&right)
            },
            _ => false,
        };
    };
    // SAFETY: the caller guarantees both objects are alive, and of one kind since they have
    // one type.
    unsafe {
        match (*l).kind {
            STR => text::bytes(&left) == text::bytes(&right),
            DATA => {
                let len = crate::object::data_len(l);
                (*l).tag == (*r).tag
                    && crate::object::data_len(r) == len
                    && (0..len).all(|i| {
                        let (lf, rf) = (*data_field(l, i), *data_field(r, i));
                        if data_field_is_heap(l, i) {
                            same(lf, rf)
                        } else {
                            lf == rf
                        }
                    })
            }
            LIST => same_lists(l, r),
            _ => false,
        }
    }
}

/// Whether two lists of one type are the same by structure: each word of each element.
///
/// # Safety
///
/// `l` and `r` are live lists of one type.
unsafe fn same_lists(l: *mut Header, r: *mut Header) -> bool {
    // SAFETY: the caller guarantees both lists are alive, so their elements are.
    unsafe {
        let shape = list::shape(l);
        let n = list::len(l);
        n == list::len(r)
            && (0..n).all(|i| {
                if shape.packed() {
                    return list::take(l, i) == list::take(r, i);
                }
                let (ls, rs) = (list::element_words(l, i), list::element_words(r, i));
                ls.iter().zip(rs).enumerate().all(|(k, (&a, &b))| {
                    if shape.heap_word(k) {
                        same(a, b)
                    } else {
                        a == b
                    }
                })
            })
    }
}

/// The elements from `start` up to `end` of a list, which are in bounds, as a new list.
///
/// # Safety
///
/// `xs` is a live list, and `start <= end <= len`.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_list_slice(xs: u64, start: u64, end: u64) -> u64 {
    // SAFETY: the caller guarantees the list is alive and the range in bounds.
    unsafe { slice(xs as *mut Header, start as usize, end as usize) as u64 }
}

/// Elements `start` up to `end` of a list, as a new list that holds new references to them.
///
/// # Safety
///
/// `xs` is a live list, and `start <= end <= len`.
pub(crate) unsafe fn slice(xs: *mut Header, start: usize, end: usize) -> *mut Header {
    // SAFETY: the caller guarantees the list is alive and the range in bounds.
    unsafe { list::copy_range(xs, start, end, end - start) }
}

/// `xs == ys` on lists, through the elements' `Eq`: the same length, then each pair in turn,
/// until one differs.
///
/// # Safety
///
/// `eq` is the element type's `Eq` dictionary, and `xs` and `ys` live lists of that type.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_list_eq(loc: u64, eq: u64, xs: u64, ys: u64) -> u64 {
    let (xs, ys) = (xs as *mut Header, ys as *mut Header);
    // SAFETY: the caller guarantees the lists are alive and the dictionary is their
    // elements' `Eq`.
    unsafe {
        let len = list::len(xs);
        let (mut left, mut right) = (Loan::new(), Loan::new());
        u64::from(
            len == list::len(ys)
                && (0..len).all(|i| {
                    let x = list::lend(xs, i, &mut left);
                    let y = list::lend(ys, i, &mut right);
                    method2(loc, eq, EQ, x, y).value != 0
                }),
        )
    }
}

/// The lexicographic order of two lists, through the elements' `Ord`.
///
/// # Safety
///
/// `ord` is the element type's `Ord` dictionary, and `xs` and `ys` live lists of that type.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_list_compare(loc: u64, ord: u64, xs: u64, ys: u64) -> u64 {
    let (xs, ys) = (xs as *mut Header, ys as *mut Header);
    // SAFETY: as for `stilt_rt_list_eq`.
    unsafe {
        let (len, other) = (list::len(xs), list::len(ys));
        let (mut left, mut right) = (Loan::new(), Loan::new());
        for i in 0..len.min(other) {
            let x = list::lend(xs, i, &mut left);
            let y = list::lend(ys, i, &mut right);
            let order = method2(loc, ord, COMPARE, x, y).value;
            if order != EQUAL {
                return order;
            }
        }
        ordering(len.cmp(&other))
    }
}

/// The hash of a list: its length, then each element's hash.
///
/// # Safety
///
/// `hash` is the element type's `Hash` dictionary, and `xs` a live list of that type.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_list_hash(loc: u64, hash: u64, xs: u64) -> u64 {
    let xs = xs as *mut Header;
    // SAFETY: as for `stilt_rt_list_eq`.
    unsafe {
        let n = list::len(xs);
        let mut a = Loan::new();
        (0..n).fold(mix(FNV, n as u64), |h, i| {
            mix(h, method1(loc, hash, HASH, list::lend(xs, i, &mut a)).value)
        })
    }
}

/// The text of a list: `[` and `]` around its elements' nested texts (std.show-output).
///
/// # Safety
///
/// `show` is the element type's `Show` dictionary, and `xs` a live list of that type.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_list_show(loc: u64, show: u64, xs: u64) -> u64 {
    let xs = xs as *mut Header;
    // SAFETY: as for `stilt_rt_list_eq`.
    unsafe {
        let mut out = vec![b'['];
        let mut a = Loan::new();
        for i in 0..list::len(xs) {
            if i > 0 {
                out.extend_from_slice(b", ");
            }
            let x = list::lend(xs, i, &mut a);
            append_shown(&mut out, method1(loc, show, SHOW_NESTED, x).value);
        }
        out.push(b']');
        text::new(&out)
    }
}

/// Appends a string that the caller owns to `out`, and releases it.
///
/// # Safety
///
/// `s` is a live string that the caller owns.
pub(crate) unsafe fn append_shown(out: &mut Vec<u8>, s: u64) {
    // SAFETY: the caller guarantees the string is alive and its own.
    unsafe {
        out.extend_from_slice(text::bytes(&s));
        object::drop(s);
    }
}

/// The total order of floats, as an `Ordering`: every NaN equals every other and exceeds
/// every other value, and `-0.0` is less than `0.0` (traits.floats). Compiled code passes
/// an `f32` widened to an `f64`, which keeps its place in the order.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_float_compare(x: f64, y: f64) -> u64 {
    let order = match (x.is_nan(), y.is_nan()) {
        (true, true) => std::cmp::Ordering::Equal,
        (true, false) => std::cmp::Ordering::Greater,
        (false, true) => std::cmp::Ordering::Less,
        (false, false) => x
            .partial_cmp(&y)
            .unwrap_or(std::cmp::Ordering::Equal)
            .then_with(|| y.is_sign_negative().cmp(&x.is_sign_negative())),
    };
    ordering(order)
}

/// `x.round()`: the nearest integer, half away from zero (std.floats). Compiled code passes
/// an `f32` widened to an `f64`, whose rounding is the `f32`'s exactly.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_round(x: f64) -> f64 {
    x.round()
}

/// `a % b` on floats: the remainder of the division truncated toward zero, which is exact
/// (numbers.division-and-remainder), so that of two `f32`s widened to `f64`s is the `f32`s' own.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_fmod(a: f64, b: f64) -> f64 {
    a % b
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_rt_hash_start,
        stilt_rt_hash_mix,
        stilt_rt_hash_word,
        stilt_rt_hash_str,
        stilt_rt_str_eq,
        stilt_rt_str_compare,
        stilt_rt_same,
        stilt_rt_list_slice,
        stilt_rt_list_eq,
        stilt_rt_list_compare,
        stilt_rt_list_hash,
        stilt_rt_list_show,
        stilt_rt_float_compare,
        stilt_rt_round,
        stilt_rt_fmod,
    ]
}
