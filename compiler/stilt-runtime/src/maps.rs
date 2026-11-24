//! The functions that compiled code calls on maps: indexing, writing an entry, walking the
//! entries in insertion order (std.maps), and the structural `Eq` and `Show` of maps
//! (traits.map-equality; std.show-output).
//!
//! Each takes the dictionaries of the key type that it needs, and finds a key by its type's
//! `hash` and `eq`, as [`map::find`] calls them. A key comes in the one word that holds it for a
//! native, a box of its words if it has several (`crate::map`), and a value or a key that a map
//! gives is a pointer to its words, which compiled code reads.

use crate::abi::{EQ, SHOW_NESTED, method1, method2};
use crate::list::Loan;
use crate::map::{self, Keys, dup_words, lent, words_of};
use crate::object::{Header, unique};
use crate::structural::append_shown;
use crate::{panic, text};

/// `m[k]`: a pointer to the words of the value of key `k`, or of the map's default, without a
/// count of their own, or a panic with `missing-key` at `loc` (std.map-element-places).
///
/// # Safety
///
/// `eq` and `hash` are the key type's dictionaries, `m` is a live map, and `k` a key.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_map_index(
    loc: u64,
    eq: u64,
    hash: u64,
    m: u64,
    k: u64,
) -> u64 {
    let m = m as *mut Header;
    // SAFETY: the caller guarantees the map is alive and the dictionaries are its keys'.
    unsafe {
        let k = words_of(&k, map::shapes(m).0);
        match map::find(m, Keys { loc, eq, hash }, k).0 {
            Some(position) => map::value_at(m, position) as u64,
            None => map::default(m).map_or_else(
                || {
                    panic::panic(
                        loc,
                        panic::MISSING_KEY,
                        "the key isn't in the map, which has no default",
                    )
                },
                |d| d.as_ptr() as u64,
            ),
        }
    }
}

/// `m[k] = v` on the map a slot holds, made unique: the entry's value replaced, or a new entry
/// at the end. It borrows `k`, and takes `v` if it is one word, or copies the words of its box.
///
/// # Safety
///
/// `eq` and `hash` are the key type's dictionaries, `slot` holds a live map, `k` is a key
/// and `v` a value that the map now owns if it is one word.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_map_store(
    loc: u64,
    eq: u64,
    hash: u64,
    slot: u64,
    k: u64,
    v: u64,
) {
    let slot = slot as usize as *mut u64;
    // SAFETY: the caller guarantees the slot holds a map, and the dictionaries are its keys'.
    unsafe {
        let m = unique(slot);
        let (key, value) = map::shapes(m);
        let v = words_of(&v, value);
        if v.len() > 1 {
            dup_words(v, value);
        }
        store(m, Keys { loc, eq, hash }, words_of(&k, key), v);
    }
}

/// Stores the words `v`, which the map now owns, as the value of the key whose words are `k`,
/// which it borrows, and returns the position of the key's entry.
///
/// # Safety
///
/// `m` is a live, unique map whose keys `keys` finds, and `k` a key.
pub(crate) unsafe fn store(m: *mut Header, keys: Keys, k: &[u64], v: &[u64]) -> usize {
    // SAFETY: the caller guarantees the map is alive and unique.
    unsafe {
        match map::find(m, keys, k) {
            (Some(position), _) => {
                map::replace(m, position, v);
                position
            }
            (None, hash) => {
                dup_words(k, map::shapes(m).0);
                map::add(m, k, v, hash)
            }
        }
    }
}

/// The position of the first entry at or after `position`, or `u64::MAX` after the last.
///
/// # Safety
///
/// `m` is a live map.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_map_next(m: u64, position: u64) -> u64 {
    // SAFETY: the caller guarantees the map is alive.
    unsafe { map::next(m as *mut Header, position as usize) }.map_or(u64::MAX, |p| p as u64)
}

/// A pointer to the words of the key of the entry at a position, without a count of their own.
///
/// # Safety
///
/// `m` is a live map with an entry at `position`.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_map_key_at(m: u64, position: u64) -> u64 {
    // SAFETY: the caller guarantees the entry exists.
    unsafe { map::key_at(m as *mut Header, position as usize) as u64 }
}

/// A pointer to the words of the value of the entry at a position, without a count of their
/// own.
///
/// # Safety
///
/// `m` is a live map with an entry at `position`.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_map_value_at(m: u64, position: u64) -> u64 {
    // SAFETY: the caller guarantees the entry exists.
    unsafe { map::value_at(m as *mut Header, position as usize) as u64 }
}

/// A pointer to the words of a map's default, without a count of their own, or 0 for a map
/// that has none.
///
/// # Safety
///
/// `m` is a live map.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_map_default(m: u64) -> u64 {
    // SAFETY: the caller guarantees the map is alive.
    unsafe { map::default(m as *mut Header) }.map_or(0, |d| d.as_ptr() as u64)
}

/// The key of a map's entry, or its value if `value` is set, whose words `at` points to, in the
/// one word that holds it where a type parameter stands, with references of its own: its word,
/// or for one of several words, a new box of them, as code past the caps of instances holds it.
///
/// # Safety
///
/// `m` is a live map, and `at` points to the words of one of its keys, or of its values.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_map_held(m: u64, at: u64, value: u64) -> u64 {
    let at = at as usize as *const u64;
    // SAFETY: the caller guarantees the map is alive and `at` points to its words.
    unsafe {
        let (key, val) = map::shapes(m as *mut Header);
        let shape = if value == 0 { key } else { val };
        let words = std::slice::from_raw_parts(at, shape.words());
        dup_words(words, shape);
        match words {
            [w] => *w,
            _ => crate::list::box_of(words, shape),
        }
    }
}

/// The words of the keys and of the values of a map's entries in insertion order.
///
/// # Safety
///
/// `m` is a live map.
pub(crate) unsafe fn entries(m: *mut Header) -> Vec<(Vec<u64>, Vec<u64>)> {
    let mut out = Vec::new();
    // SAFETY: the caller guarantees the map is alive.
    unsafe {
        let (key, value) = map::shapes(m);
        let mut position = map::next(m, 0);
        while let Some(p) = position {
            let k = std::slice::from_raw_parts(map::key_at(m, p), key.words());
            let v = std::slice::from_raw_parts(map::value_at(m, p), value.words());
            out.push((k.to_vec(), v.to_vec()));
            position = map::next(m, p + 1);
        }
    }
    out
}

/// `a == b` on maps: the same number of entries, and each entry of `a`, in its order, found in
/// `b` with an equal value, in any order (traits.map-equality).
///
/// # Safety
///
/// The dictionaries are the key type's `Eq` and `Hash` and the value type's `Eq`, and `a`
/// and `b` live maps of those types.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_map_eq(
    loc: u64,
    eq: u64,
    hash: u64,
    value_eq: u64,
    a: u64,
    b: u64,
) -> u64 {
    let (a, b) = (a as *mut Header, b as *mut Header);
    let keys = Keys { loc, eq, hash };
    // SAFETY: the caller guarantees the maps are alive and the dictionaries are theirs.
    unsafe {
        let value = map::shapes(a).1;
        u64::from(
            map::len(a) == map::len(b)
                && entries(a)
                    .into_iter()
                    .all(|(k, v)| match map::find(b, keys, &k).0 {
                        Some(position) => {
                            let other =
                                std::slice::from_raw_parts(map::value_at(b, position), v.len());
                            let (mut mine, mut theirs) = (Loan::new(), Loan::new());
                            let mine = lent(&v, value, &mut mine);
                            let theirs = lent(other, value, &mut theirs);
                            method2(loc, value_eq, EQ, mine, theirs).value != 0
                        }
                        None => false,
                    }),
        )
    }
}

/// The text of a map: `{k: v, …}` in insertion order, from the nested texts of its keys and
/// values (std.show-output).
///
/// # Safety
///
/// The dictionaries are the `Show` of the key and the value types, and `m` a live map of
/// those types.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_map_show(
    loc: u64,
    key_show: u64,
    value_show: u64,
    m: u64,
) -> u64 {
    let mut out = vec![b'{'];
    let m = m as *mut Header;
    // SAFETY: the caller guarantees the map is alive and the dictionaries are its types'.
    unsafe {
        let (key, value) = map::shapes(m);
        for (i, (k, v)) in entries(m).into_iter().enumerate() {
            if i > 0 {
                out.extend_from_slice(b", ");
            }
            let (mut key_loan, mut value_loan) = (Loan::new(), Loan::new());
            let k = lent(&k, key, &mut key_loan);
            let v = lent(&v, value, &mut value_loan);
            append_shown(&mut out, method1(loc, key_show, SHOW_NESTED, k).value);
            out.extend_from_slice(b": ");
            append_shown(&mut out, method1(loc, value_show, SHOW_NESTED, v).value);
        }
    }
    out.push(b'}');
    text::new(&out)
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_rt_map_index,
        stilt_rt_map_store,
        stilt_rt_map_next,
        stilt_rt_map_key_at,
        stilt_rt_map_value_at,
        stilt_rt_map_default,
        stilt_rt_map_held,
        stilt_rt_map_eq,
        stilt_rt_map_show,
    ]
}
