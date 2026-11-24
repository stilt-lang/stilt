//! The structural impls of tuples whose length is known at run time only: those of a pack that
//! grows through polymorphic recursion, which compiled code holds as a list of its elements,
//! each in a box of one field that holds it in the one word that holds it where a type
//! parameter stands. Each takes a list of the elements' dictionaries, in order, and calls each
//! element's impl, as a tuple's structural impl does (traits.structural-impls).

use crate::abi::{COMPARE, EQ, EQUAL, HASH, SHOW_NESTED, method1, method2, ordering};
use crate::list::{self, Loan};
use crate::object::{Header, data_field};
use crate::structural::{FNV, append_shown, mix};
use crate::text;

/// Element `i` of a pack's tuple, in the word its box holds, and its dictionary, borrowed.
///
/// # Safety
///
/// `xs` is a live list of boxes, and `dicts` a live list of as many dictionaries.
unsafe fn element(
    xs: *mut Header,
    dicts: *mut Header,
    i: usize,
    loans: &mut [Loan; 2],
) -> (u64, u64) {
    // SAFETY: the caller guarantees both lists are alive and as long; a box has one field.
    unsafe {
        let boxed = list::lend(xs, i, &mut loans[0]) as *mut Header;
        (*data_field(boxed, 0), list::lend(dicts, i, &mut loans[1]))
    }
}

/// `xs == ys` on two tuples of one pack: each pair of elements in turn, until one differs.
///
/// # Safety
///
/// `eqs` holds the elements' `Eq` dictionaries, and `xs` and `ys` are live tuples of the pack.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_pack_eq(loc: u64, eqs: u64, xs: u64, ys: u64) -> u64 {
    let (xs, ys, eqs) = (xs as *mut Header, ys as *mut Header, eqs as *mut Header);
    // SAFETY: the caller guarantees the lists are alive and of one pack.
    unsafe {
        let (mut a, mut b) = ([Loan::new(), Loan::new()], [Loan::new(), Loan::new()]);
        u64::from((0..list::len(xs)).all(|i| {
            let (x, eq) = element(xs, eqs, i, &mut a);
            let (y, _) = element(ys, eqs, i, &mut b);
            method2(loc, eq, EQ, x, y).value != 0
        }))
    }
}

/// The lexicographic order of two tuples of one pack.
///
/// # Safety
///
/// As for [`stilt_rt_pack_eq`], with the elements' `Ord` dictionaries.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_pack_compare(
    loc: u64,
    ords: u64,
    xs: u64,
    ys: u64,
) -> u64 {
    let (xs, ys, ords) = (xs as *mut Header, ys as *mut Header, ords as *mut Header);
    // SAFETY: as for `stilt_rt_pack_eq`.
    unsafe {
        let (mut a, mut b) = ([Loan::new(), Loan::new()], [Loan::new(), Loan::new()]);
        for i in 0..list::len(xs) {
            let (x, ord) = element(xs, ords, i, &mut a);
            let (y, _) = element(ys, ords, i, &mut b);
            let order = method2(loc, ord, COMPARE, x, y).value;
            if order != EQUAL {
                return order;
            }
        }
        ordering(std::cmp::Ordering::Equal)
    }
}

/// The hash of a tuple of a pack: each element's hash mixed in turn, as a tuple's.
///
/// # Safety
///
/// `hashes` holds the elements' `Hash` dictionaries, and `xs` is a live tuple of the pack.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_pack_hash(loc: u64, hashes: u64, xs: u64) -> u64 {
    let (xs, hashes) = (xs as *mut Header, hashes as *mut Header);
    // SAFETY: as for `stilt_rt_pack_eq`.
    unsafe {
        let mut a = [Loan::new(), Loan::new()];
        (0..list::len(xs)).fold(FNV, |h, i| {
            let (x, hash) = element(xs, hashes, i, &mut a);
            mix(h, method1(loc, hash, HASH, x).value)
        })
    }
}

/// The text of a tuple of a pack: `(` and `)` around its elements' nested texts, with a comma
/// after the only one (std.show-output).
///
/// # Safety
///
/// `shows` holds the elements' `Show` dictionaries, and `xs` is a live tuple of the pack.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_pack_show(loc: u64, shows: u64, xs: u64) -> u64 {
    let (xs, shows) = (xs as *mut Header, shows as *mut Header);
    // SAFETY: as for `stilt_rt_pack_eq`.
    unsafe {
        let n = list::len(xs);
        let mut out = vec![b'('];
        let mut a = [Loan::new(), Loan::new()];
        for i in 0..n {
            if i > 0 {
                out.extend_from_slice(b", ");
            }
            let (x, show) = element(xs, shows, i, &mut a);
            append_shown(&mut out, method1(loc, show, SHOW_NESTED, x).value);
        }
        if n == 1 {
            out.push(b',');
        }
        out.push(b')');
        text::new(&out)
    }
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_rt_pack_eq,
        stilt_rt_pack_compare,
        stilt_rt_pack_hash,
        stilt_rt_pack_show,
    ]
}
