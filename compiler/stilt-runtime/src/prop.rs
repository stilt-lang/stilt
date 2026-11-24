//! The values of a property's cases, as compiled code reads them (tests.property-cases and
//! tests.running-cases).
//!
//! The compiler generates and shrinks a property's values as data, and writes each case's to a
//! [`Tape`]: in the order the values' parts are generated, a scalar's word as compiled code holds
//! it, a list's or a map's length, a variant's number, and each string apart. The property's
//! entry reads them back through these functions, building each value as code of its type
//! builds it, and calls the closure with them. A map is built by inserting its entries in order,
//! which calls its key type's `hash` and `eq` (std.finding-keys): the tape notes the position of
//! each entry's key, so that the compiler learns which entries a key equal to an earlier one
//! replaced.

use crate::map::{self, Keys, dup_words, words_of};
use crate::maps::store;
use crate::object::unique;
use crate::shape::Shape;
use crate::text;

/// The parts of a case's values, in the order the property's entry reads them, and the
/// positions of the map entries it stores.
#[derive(Debug, Default)]
pub struct Tape {
    words: Vec<u64>,
    strings: Vec<String>,
    next_word: usize,
    next_string: usize,
    notes: Vec<u64>,
}

impl Tape {
    /// A tape of these words and strings.
    #[must_use]
    pub fn new(words: Vec<u64>, strings: Vec<String>) -> Self {
        Self {
            words,
            strings,
            ..Self::default()
        }
    }

    /// The position of each map entry's key, in the order the entries were stored.
    #[must_use]
    pub fn notes(&self) -> &[u64] {
        &self.notes
    }
}

/// The tape a word points to.
///
/// # Safety
///
/// `tape` points to a live tape that nothing else uses while the property runs.
unsafe fn tape<'a>(tape: u64) -> &'a mut Tape {
    // SAFETY: the caller guarantees it.
    unsafe { &mut *(tape as *mut Tape) }
}

/// The next word of the tape: a scalar, a length or a variant's number.
///
/// # Safety
///
/// `t` points to a live tape.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_prop_word(t: u64) -> u64 {
    // SAFETY: the caller guarantees the tape lives.
    let t = unsafe { tape(t) };
    let w = t.words.get(t.next_word).copied().unwrap_or(0);
    t.next_word += 1;
    w
}

/// The next string of the tape, as a new string.
///
/// # Safety
///
/// `t` points to a live tape.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_prop_str(t: u64) -> u64 {
    // SAFETY: the caller guarantees the tape lives.
    let t = unsafe { tape(t) };
    let s = t.strings.get(t.next_string).map_or("", String::as_str);
    t.next_string += 1;
    text::from(s)
}

/// An empty map, of keys and values of these shapes.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_prop_map(key: u64, value: u64) -> u64 {
    map::new(Shape(key), Shape(value), None) as u64
}

/// `m[k] = v` on the map a slot holds, as [`crate::maps`]'s store, noting the position of the
/// key's entry on the tape.
///
/// # Safety
///
/// `t` points to a live tape, `eq` and `hash` are the key type's dictionaries, `slot` holds a
/// live map, `k` is a key, and `v` a value that the map now owns if it is one word.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_prop_store(
    t: u64,
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
        let position = store(m, Keys { loc, eq, hash }, words_of(&k, key), v);
        tape(t).notes.push(position as u64);
    }
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_rt_prop_word,
        stilt_rt_prop_str,
        stilt_rt_prop_map,
        stilt_rt_prop_store,
    ]
}
