//! The native methods of `Map<K: Eq + Hash, V>` (std.maps).
//!
//! Each takes, after its location, the witness of `K`, its `Eq` and `Hash` dictionaries and
//! the witness of `V`, each witness the shape of its type's values (`crate::shape`), then its
//! arguments: a map it borrows, or the slot of an `inout` one, which it makes unique before it
//! writes it, and a key or a value in the one word that holds it for a native, a box of its words
//! if it has several, which it copies the words of (`crate::map`). A native that gives a value of
//! several words writes them to the memory its last argument points to, and returns the tag of
//! the `Option` that holds it.

use crate::abi::{NONE, Ret, immediate, option, some};
use crate::map::{self, Keys, drop_words, dup_words, words_of};
use crate::maps::store;
use crate::object::{Header, unique};
use crate::shape::Shape;

/// `Map.new()`.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_prelude_Map_new(
    _loc: u64,
    key: u64,
    _eq: u64,
    _hash: u64,
    value: u64,
) -> Ret {
    Ret::ok(map::new(Shape(key), Shape(value), None) as u64)
}

/// `Map.with_default(d)`: an empty map whose index gives `d` for a missing key.
///
/// # Safety
///
/// `d` is a live value of the value type.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_Map_with_default(
    _loc: u64,
    key: u64,
    _eq: u64,
    _hash: u64,
    value: u64,
    d: u64,
) -> Ret {
    let value = Shape(value);
    // SAFETY: the caller guarantees the value is alive.
    let d: Box<[u64]> = unsafe {
        let words = words_of(&d, value);
        dup_words(words, value);
        words.into()
    };
    Ret::ok(map::new(Shape(key), value, Some(d)) as u64)
}

/// `m.len()`: its number of entries.
///
/// # Safety
///
/// `m` is a live map.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_Map_len(
    _loc: u64,
    _kh: u64,
    _eq: u64,
    _hash: u64,
    _vh: u64,
    m: u64,
) -> Ret {
    // SAFETY: the caller guarantees the map is alive.
    Ret::ok(unsafe { map::len(m as *mut Header) } as u64)
}

/// `m.is_empty()`.
///
/// # Safety
///
/// `m` is a live map.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_Map_is_empty(
    _loc: u64,
    _kh: u64,
    _eq: u64,
    _hash: u64,
    _vh: u64,
    m: u64,
) -> Ret {
    // SAFETY: the caller guarantees the map is alive.
    Ret::ok(u64::from(unsafe { map::len(m as *mut Header) } == 0))
}

/// `m.contains(k)`: whether an entry has key `k`.
///
/// # Safety
///
/// The dictionaries are the key type's, `m` is a live map and `k` a key.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_Map_contains(
    loc: u64,
    _kh: u64,
    eq: u64,
    hash: u64,
    _vh: u64,
    m: u64,
    k: u64,
) -> Ret {
    let keys = Keys { loc, eq, hash };
    let m = m as *mut Header;
    // SAFETY: the caller guarantees the map is alive and the dictionaries are its keys'.
    unsafe {
        let k = words_of(&k, map::shapes(m).0);
        Ret::ok(u64::from(map::find(m, keys, k).0.is_some()))
    }
}

/// Gives `Some` of the words of a value of shape `shape`, which own their references: in the
/// result for a value of one word, and otherwise in the memory `out` points to, the result
/// holding the tag, or where `out` is null, as code past the caps of instances passes, in its
/// box.
///
/// # Safety
///
/// `out` points to room for the words of a value of several words, or is null.
pub(crate) unsafe fn give(words: &[u64], shape: Shape, out: *mut u64) -> Ret {
    if words.len() == 1 {
        return some(words[0]);
    }
    if out.is_null() {
        return some(crate::list::box_of(words, shape));
    }
    // SAFETY: the caller guarantees the room.
    unsafe { std::ptr::copy_nonoverlapping(words.as_ptr(), out, words.len()) };
    Ret::words(immediate(1), 0)
}

/// `m.get(k)`: `Some` of the value of key `k`, or `None`, whatever the map's default.
///
/// # Safety
///
/// As for `stilt_std_prelude_Map_contains`, and `out` points to room for a value of several
/// words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_Map_get(
    loc: u64,
    _kh: u64,
    eq: u64,
    hash: u64,
    _vh: u64,
    m: u64,
    k: u64,
    out: u64,
) -> Ret {
    let out = out as usize as *mut u64;
    let keys = Keys { loc, eq, hash };
    let m = m as *mut Header;
    // SAFETY: the caller guarantees the map is alive and the dictionaries are its keys'.
    unsafe {
        let (key, value) = map::shapes(m);
        let Some(position) = map::find(m, keys, words_of(&k, key)).0 else {
            return option(None);
        };
        let words = std::slice::from_raw_parts(map::value_at(m, position), value.words());
        dup_words(words, value);
        give(words, value, out)
    }
}

/// `m.insert(k, v)`: the value of key `k` replaced, or a new entry at the end.
///
/// # Safety
///
/// The dictionaries are the key type's, `slot` holds a live map, and `k` and `v` are a live
/// key and value.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_Map_insert(
    loc: u64,
    _kh: u64,
    eq: u64,
    hash: u64,
    _vh: u64,
    slot: u64,
    k: u64,
    v: u64,
) -> Ret {
    let slot = slot as usize as *mut u64;
    let keys = Keys { loc, eq, hash };
    // SAFETY: the caller guarantees the slot holds a map and the words are alive.
    unsafe {
        let m = unique(slot);
        let (key, value) = map::shapes(m);
        let v = words_of(&v, value);
        dup_words(v, value);
        store(m, keys, words_of(&k, key), v);
    }
    Ret::unit()
}

/// `m.remove(k)`: removes the entry of key `k` and returns `Some` of its value, or `None`.
///
/// # Safety
///
/// The dictionaries are the key type's, `slot` holds a live map, `k` is a live key, and `out`
/// points to room for a value of several words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_Map_remove(
    loc: u64,
    _kh: u64,
    eq: u64,
    hash: u64,
    _vh: u64,
    slot: u64,
    k: u64,
    out: u64,
) -> Ret {
    let slot = slot as usize as *mut u64;
    let out = out as usize as *mut u64;
    let keys = Keys { loc, eq, hash };
    // SAFETY: the caller guarantees the slot holds a map and the key is alive.
    unsafe {
        let (key, value) = map::shapes(*slot as *mut Header);
        let Some(position) = map::find(*slot as *mut Header, keys, words_of(&k, key)).0 else {
            return NONE;
        };
        let m = unique(slot);
        let (stored, v) = map::remove_at(m, position);
        drop_words(&stored, key);
        give(&v, value, out)
    }
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_std_prelude_Map_new,
        stilt_std_prelude_Map_with_default,
        stilt_std_prelude_Map_len,
        stilt_std_prelude_Map_is_empty,
        stilt_std_prelude_Map_contains,
        stilt_std_prelude_Map_get,
        stilt_std_prelude_Map_insert,
        stilt_std_prelude_Map_remove,
    ]
}
