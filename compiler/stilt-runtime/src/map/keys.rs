//! Finding a key: its type's `hash`, called once, then `eq` on each stored key of the same hash
//! in insertion order, until one call returns `true` (std.finding-keys).
//!
//! The structural `Eq` and `Hash` of an integer type, `bool` and `str` run no code of the
//! program and can't panic, and their dictionaries' tags say so (`crate::layout`), so a map
//! hashes and compares such keys itself, by the same functions as those dictionaries, and calls
//! nothing. Their hashes are the dictionaries' own, so that a map reached through other
//! dictionaries of the same type, such as those that code past the caps of instances forwards,
//! finds the same entries.

use super::{Index, Probe, State, lent, state};
use crate::abi::{EQ, HASH, method1, method2};
use crate::layout::{MASK_WORDS, STR_KEYS, WORD_KEYS};
use crate::list::Loan;
use crate::object::{Header, pointer};
use crate::shape::Shape;
use crate::structural::{FNV, mix, stilt_rt_hash_str};
use crate::text;

/// The dictionaries through which a map finds its keys: the key type's `Eq` and `Hash`.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Keys {
    pub(crate) loc: u64,
    pub(crate) eq: u64,
    pub(crate) hash: u64,
}

/// How a map hashes and compares keys: through their dictionaries, or itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Called,
    Words,
    Strings,
}

/// The tag of a dictionary.
fn tag(dict: u64) -> Option<u16> {
    // SAFETY: a map's dictionaries are live data objects.
    pointer(dict).map(|d| unsafe { (*d).tag })
}

impl Keys {
    fn kind(self) -> Kind {
        match (tag(self.eq), tag(self.hash)) {
            (Some(WORD_KEYS), Some(WORD_KEYS)) => Kind::Words,
            (Some(STR_KEYS), Some(STR_KEYS)) => Kind::Strings,
            _ => Kind::Called,
        }
    }

    fn hash(self, k: &[u64], shape: Shape) -> u64 {
        let call = |k: u64| {
            // SAFETY: `hash` is the key type's `Hash` dictionary, and `k` a key.
            unsafe { method1(self.loc, self.hash, HASH, k).value }
        };
        if let [w] = k {
            return call(*w);
        }
        let mut loan = Loan::new();
        call(lent(k, shape, &mut loan))
    }

    fn eq(self, k: &[u64], other: &[u64], shape: Shape) -> bool {
        let call = |k: u64, other: u64| {
            // SAFETY: `eq` is the key type's `Eq` dictionary, and both words are keys.
            unsafe { method2(self.loc, self.eq, EQ, k, other).value != 0 }
        };
        if let ([a], [b]) = (k, other) {
            return call(*a, *b);
        }
        let mut loans = (Loan::new(), Loan::new());
        call(
            lent(k, shape, &mut loans.0),
            lent(other, shape, &mut loans.1),
        )
    }
}

/// The words of a key or a value, copied out of a map: on the stack for at most
/// [`MASK_WORDS`] words, the rest of the room left as it is, and otherwise from the allocator,
/// as a buffer that no count sees.
pub(crate) struct Words {
    room: [std::mem::MaybeUninit<u64>; MASK_WORDS],
    len: usize,
    large: Vec<u64>,
}

impl Words {
    pub(super) fn of(words: &[u64]) -> Self {
        let mut out = Self {
            room: [std::mem::MaybeUninit::uninit(); MASK_WORDS],
            len: words.len(),
            large: Vec::new(),
        };
        if words.len() > MASK_WORDS {
            out.large = words.to_vec();
            return out;
        }
        for (w, &x) in out.room.iter_mut().zip(words) {
            w.write(x);
        }
        out
    }
}

impl std::ops::Deref for Words {
    type Target = [u64];

    fn deref(&self) -> &[u64] {
        if self.len > MASK_WORDS {
            return &self.large;
        }
        // SAFETY: the first `len` words are written, and `len` is at most the room.
        unsafe { std::slice::from_raw_parts(self.room.as_ptr().cast(), self.len) }
    }
}

/// The next entry along a probe whose stored hash is `hash`.
fn next_of(state: &State, probe: &mut Probe, hash: u64) -> Option<usize> {
    let index: &Index = &state.index;
    probe.next(index, |p| state.hash_at(p) == hash)
}

/// The position of the entry whose key has the words `k`, if there is one, with `k`'s hash.
///
/// # Safety
///
/// `map` is a live map, and `k` the words of a key of its key type.
pub(crate) unsafe fn find(map: *mut Header, keys: Keys, k: &[u64]) -> (Option<usize>, u64) {
    match (keys.kind(), k) {
        // SAFETY: the caller guarantees the map is alive and `k` one of its keys, of one word.
        (Kind::Words, [w]) => unsafe { find_word(map, *w) },
        // SAFETY: as above, a string.
        (Kind::Strings, [s]) => unsafe { find_str(map, *s) },
        // SAFETY: as above.
        _ => unsafe { find_called(map, keys, k) },
    }
}

/// [`find`] for a key whose `hash` and `eq` are its type's structural ones of a word.
///
/// # Safety
///
/// `map` is a live map of keys of one word.
unsafe fn find_word(map: *mut Header, k: u64) -> (Option<usize>, u64) {
    // SAFETY: the caller guarantees the map is alive; nothing runs while it is borrowed.
    let state = unsafe { state(map) };
    let hash = mix(FNV, k);
    let mut probe = state.index.probe(hash);
    while let Some(position) = next_of(state, &mut probe, hash) {
        if state.entry(position)[0] == k {
            return (Some(position), hash);
        }
    }
    (None, hash)
}

/// [`find`] for a string whose `hash` and `eq` are the structural ones of `str`.
///
/// # Safety
///
/// `map` is a live map of strings, and `k` a live string.
unsafe fn find_str(map: *mut Header, k: u64) -> (Option<usize>, u64) {
    // SAFETY: the caller guarantees the map and the strings are alive; nothing runs while they
    // are borrowed.
    unsafe {
        let state = state(map);
        let hash = stilt_rt_hash_str(k);
        let bytes = text::bytes(&k);
        let mut probe = state.index.probe(hash);
        while let Some(position) = next_of(state, &mut probe, hash) {
            let other = state.entry(position)[0];
            if other == k || text::bytes(&other) == bytes {
                return (Some(position), hash);
            }
        }
        (None, hash)
    }
}

/// [`find`] through the key type's dictionaries, which run code of the program. That code can't
/// reach this map, which its caller borrows or holds alone, but may reach others, so no borrow
/// of the map's state lasts across a call, and a stored key is copied out before `eq` takes it.
///
/// # Safety
///
/// As for [`find`].
unsafe fn find_called(map: *mut Header, keys: Keys, k: &[u64]) -> (Option<usize>, u64) {
    // SAFETY: the caller guarantees the map is alive.
    let shape = unsafe { state(map).key };
    let hash = keys.hash(k, shape);
    // SAFETY: as above.
    let mut probe = unsafe { state(map).index.probe(hash) };
    // SAFETY: as above.
    while let Some(position) = next_of(unsafe { state(map) }, &mut probe, hash) {
        let equal = if let [_] = k {
            // SAFETY: as above; the position holds an entry.
            let other = unsafe { state(map).entry(position)[0] };
            keys.eq(k, &[other], shape)
        } else {
            // SAFETY: as above.
            let other = unsafe { Words::of(&state(map).entry(position)[..k.len()]) };
            keys.eq(k, &other, shape)
        };
        if equal {
            return (Some(position), hash);
        }
    }
    (None, hash)
}
