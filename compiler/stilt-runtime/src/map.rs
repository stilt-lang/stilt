//! Maps: entries in insertion order, found by the key type's own `hash` and `eq` (std.maps), copied
//! on write.
//!
//! A map object holds a pointer to its state after its header. The state keeps the entries in
//! insertion order, each the words of its key, then the words of its value, as a list holds an
//! element of their types (`crate::shape`), so that a key or a value of several words is held
//! inline, and a narrow scalar widened to a word; then the key's hash. A removed entry leaves a
//! gap until the entries are compacted. An open-addressing table of their positions finds them
//! from their hashes ([`index`]). Finding a key calls its type's `hash` once, then `eq` on each
//! stored key of the same hash in insertion order, until one call returns `true`, exactly as the
//! record fixes the calls ([`keys`]); a key of several words is lent to them in a box that no
//! count frees.
//!
//! Compiled code and natives give a key or a value in the one word that holds it where a type
//! parameter stands for a native (`crate::abi`): its word, or for one of several words, a box of
//! them, which the map copies the words of.

mod index;
mod keys;
#[cfg(test)]
mod tests;

use index::{Index, MAX_ENTRIES, Probe};
pub(crate) use keys::{Keys, Words, find};

use crate::list::Loan;
use crate::object::{HEADER, Header, MAP, SHARED, alloc_object, data_field, dup, lent_data};
use crate::shape::Shape;

/// The size of a map object, its state apart.
const SIZE: usize = HEADER + 8;

#[derive(Clone)]
struct State {
    key: Shape,
    value: Shape,
    /// The words of each entry, one after the other: the key's, the value's, and the hash.
    words: Vec<u64>,
    /// Whether each entry is still in the map.
    live: Vec<bool>,
    /// The positions of the entries, by their hashes.
    index: Index,
    count: usize,
    /// The words of the value that indexing a missing key gives.
    default: Option<Box<[u64]>>,
}

impl State {
    fn key_words(&self) -> usize {
        self.key.words()
    }

    fn value_words(&self) -> usize {
        self.value.words()
    }

    fn stride(&self) -> usize {
        self.key_words() + self.value_words() + 1
    }

    fn entry(&self, position: usize) -> &[u64] {
        let n = self.stride();
        &self.words[position * n..(position + 1) * n]
    }

    fn entry_mut(&mut self, position: usize) -> &mut [u64] {
        let n = self.stride();
        &mut self.words[position * n..(position + 1) * n]
    }

    /// The hash of the key of the entry at a position.
    fn hash_at(&self, position: usize) -> u64 {
        let n = self.stride();
        self.words[position * n + n - 1]
    }

    /// The index of the entries in the map, built again in their order.
    fn reindex(&mut self, n: usize) {
        let entries = (0..self.live.len()).filter(|&p| self.live[p]);
        self.index = Index::of(n, entries.map(|p| (p, self.hash_at(p))));
    }
}

/// The state of a map.
///
/// # Safety
///
/// `map` is a live map.
unsafe fn state<'a>(map: *mut Header) -> &'a mut State {
    // SAFETY: the caller guarantees `map` is a map, whose state pointer follows its header.
    unsafe { &mut **map.cast::<u8>().add(HEADER).cast::<*mut State>() }
}

fn new_with(state: State) -> *mut Header {
    let map = alloc_object(SIZE, MAP, 0, 0, 0);
    // SAFETY: the object was allocated with room for the state pointer.
    unsafe {
        map.cast::<u8>()
            .add(HEADER)
            .cast::<*mut State>()
            .write(Box::into_raw(Box::new(state)));
    }
    map
}

/// A new empty map of keys and values of these shapes, with a default it now owns the words of
/// if `default` is given.
pub(crate) fn new(key: Shape, value: Shape, default: Option<Box<[u64]>>) -> *mut Header {
    new_with(State {
        key,
        value,
        words: Vec::new(),
        live: Vec::new(),
        index: Index::default(),
        count: 0,
        default,
    })
}

/// The shapes of a map's keys and values.
///
/// # Safety
///
/// `map` is a live map.
pub(crate) unsafe fn shapes(map: *mut Header) -> (Shape, Shape) {
    // SAFETY: the caller guarantees the map is alive.
    let state = unsafe { state(map) };
    (state.key, state.value)
}

/// The words of a value of shape `shape` given in the one word that holds it for a native: the
/// word, or the fields of its box.
///
/// # Safety
///
/// `x` is a live value of that shape, a box of its words if it has several.
pub(crate) unsafe fn words_of(x: &u64, shape: Shape) -> &[u64] {
    let n = shape.words();
    if n == 1 {
        return std::slice::from_ref(x);
    }
    // SAFETY: the caller guarantees `x` is a box of `n` fields.
    unsafe { std::slice::from_raw_parts(data_field(*x as *mut Header, 0), n) }
}

/// Counts a new reference to each heap word of `words`, of shape `shape`.
///
/// # Safety
///
/// The words are alive.
pub(crate) unsafe fn dup_words(words: &[u64], shape: Shape) {
    for (i, &w) in words.iter().enumerate() {
        if word_heap(shape, i) {
            // SAFETY: the caller guarantees the word is alive.
            unsafe { dup(w) };
        }
    }
}

/// Releases each heap word of `words`, of shape `shape`.
///
/// # Safety
///
/// The words own their references.
pub(crate) unsafe fn drop_words(words: &[u64], shape: Shape) {
    for (i, &w) in words.iter().enumerate() {
        if word_heap(shape, i) {
            // SAFETY: the caller guarantees the word owns its reference.
            unsafe { crate::object::drop(w) };
        }
    }
}

/// Whether word `i` of a key or a value of shape `shape` is a heap word: a narrow scalar is
/// none.
fn word_heap(shape: Shape, i: usize) -> bool {
    !shape.packed() && shape.heap_word(i)
}

/// A value of shape `shape` in one word, lent to a method of a dictionary: its word, or a box of
/// its words in `loan`.
pub(crate) fn lent(words: &[u64], shape: Shape, loan: &mut Loan) -> u64 {
    if words.len() == 1 {
        return words[0];
    }
    lent_data(loan.room(words.len()), words, |i| word_heap(shape, i)) as u64
}

/// Calls `f` on each heap word a map holds: its keys, values and default.
///
/// # Safety
///
/// `map` is a live map.
pub(crate) unsafe fn for_each_heap(map: *mut Header, mut f: impl FnMut(u64)) {
    // SAFETY: as the caller guarantees; `f` reads each place.
    unsafe { for_each_heap_place(map, |p| f(*p)) }
}

/// Calls `f` on the place of each heap word a map holds, as [`for_each_heap`] reaches them.
///
/// # Safety
///
/// `map` is a live map, and `f` leaves a heap word that is equal in each place.
pub(crate) unsafe fn for_each_heap_place(map: *mut Header, mut f: impl FnMut(*mut u64)) {
    // SAFETY: the caller guarantees the map is alive.
    let state = unsafe { state(map) };
    let (kw, vw, n) = (state.key_words(), state.value_words(), state.stride());
    let (key, value) = (state.key, state.value);
    for p in (0..state.live.len()).filter(|&p| state.live[p]) {
        let entry = &mut state.words[p * n..p * n + kw + vw];
        for (i, w) in entry.iter_mut().enumerate() {
            if (i < kw && word_heap(key, i)) || (i >= kw && word_heap(value, i - kw)) {
                f(w);
            }
        }
    }
    for (i, w) in state
        .default
        .iter_mut()
        .flat_map(|d| d.iter_mut())
        .enumerate()
    {
        if word_heap(value, i) {
            f(w);
        }
    }
}

/// Frees a map's state, whose words are already released, and returns the size of the map
/// object itself.
///
/// # Safety
///
/// `map` is a map that nothing references.
pub(crate) unsafe fn free_state(map: *mut Header) -> usize {
    // SAFETY: the caller guarantees nothing uses the map; its state came from `Box::into_raw`.
    unsafe {
        drop(Box::from_raw(state(map)));
    }
    SIZE
}

/// A copy of a map, which holds new references to its words.
///
/// # Safety
///
/// `map` is a live map.
pub(crate) unsafe fn copy(map: *mut Header) -> *mut Header {
    // SAFETY: the caller guarantees the map is alive.
    unsafe {
        let copy = new_with(state(map).clone());
        (*copy).flags = (*map).flags & !SHARED;
        for_each_heap(copy, |w| dup(w));
        copy
    }
}

/// The number of entries of a map.
///
/// # Safety
///
/// `map` is a live map.
pub(crate) unsafe fn len(map: *mut Header) -> usize {
    // SAFETY: the caller guarantees the map is alive.
    unsafe { state(map).count }
}

/// The words of a map's default, if it has one.
///
/// # Safety
///
/// `map` is a live map, which outlives the words.
pub(crate) unsafe fn default<'a>(map: *mut Header) -> Option<&'a [u64]> {
    // SAFETY: the caller guarantees the map is alive.
    unsafe { state(map).default.as_deref() }
}

/// A pointer to the words of the value of the entry at a position, which live as long as the
/// map doesn't change.
///
/// # Safety
///
/// `map` is a live map with an entry at `position`.
pub(crate) unsafe fn value_at(map: *mut Header, position: usize) -> *const u64 {
    // SAFETY: the caller guarantees the entry exists.
    let state = unsafe { state(map) };
    let kw = state.key_words();
    state.entry(position)[kw..].as_ptr()
}

/// A pointer to the words of the key of the entry at a position, which live as long as the map
/// doesn't change.
///
/// # Safety
///
/// `map` is a live map with an entry at `position`.
pub(crate) unsafe fn key_at(map: *mut Header, position: usize) -> *const u64 {
    // SAFETY: the caller guarantees the entry exists.
    unsafe { state(map).entry(position).as_ptr() }
}

/// The position of the first entry at or after `position`, if there is one.
///
/// # Safety
///
/// `map` is a live map.
pub(crate) unsafe fn next(map: *mut Header, position: usize) -> Option<usize> {
    // SAFETY: the caller guarantees the map is alive.
    let live = unsafe { &state(map).live };
    (position..live.len()).find(|&p| live[p])
}

/// Stores `v`, the words of a value that the map now owns, as the value of the entry at a
/// position, and releases the words it replaces. The entry keeps its stored key.
///
/// # Safety
///
/// `map` is a live, unique map with an entry at `position`, and `v` owns its references.
pub(crate) unsafe fn replace(map: *mut Header, position: usize, v: &[u64]) {
    // SAFETY: the caller guarantees the entry exists.
    let state = unsafe { state(map) };
    let (kw, vw, shape) = (state.key_words(), state.value_words(), state.value);
    if let [w] = v {
        let old = std::mem::replace(&mut state.entry_mut(position)[kw], *w);
        // SAFETY: the replaced word owned its reference.
        return unsafe { drop_words(&[old], shape) };
    }
    let old = Words::of(&state.entry(position)[kw..kw + vw]);
    state.entry_mut(position)[kw..kw + vw].copy_from_slice(v);
    // SAFETY: the replaced words owned their references.
    unsafe { drop_words(&old, shape) };
}

/// Adds an entry at the end, whose key's and value's words the map now owns, and returns its
/// position.
///
/// # Safety
///
/// `map` is a live, unique map, and `hash` is `k`'s.
pub(crate) unsafe fn add(map: *mut Header, k: &[u64], v: &[u64], hash: u64) -> usize {
    // SAFETY: the caller guarantees the map is alive.
    let state = unsafe { state(map) };
    let position = state.live.len();
    if position >= MAX_ENTRIES {
        crate::entry::fatal("out of memory");
    }
    if !state.index.has_room() {
        state.reindex(state.count + 1);
    }
    state.index.put(position, hash);
    state.words.extend_from_slice(k);
    state.words.extend_from_slice(v);
    state.words.push(hash);
    state.live.push(true);
    state.count += 1;
    position
}

/// Removes the entry at a position, and returns its key's and value's words, which the caller
/// now owns.
///
/// # Safety
///
/// `map` is a live, unique map with an entry at `position`.
pub(crate) unsafe fn remove_at(map: *mut Header, position: usize) -> (Words, Words) {
    // SAFETY: the caller guarantees the entry exists.
    let state = unsafe { state(map) };
    let (kw, vw) = (state.key_words(), state.value_words());
    let entry = state.entry(position);
    let (k, v, hash) = (
        Words::of(&entry[..kw]),
        Words::of(&entry[kw..kw + vw]),
        entry[kw + vw],
    );
    state.live[position] = false;
    state.count -= 1;
    state.index.remove(position, hash);
    if state.live.len() > 8 && state.count * 2 < state.live.len() {
        compact(state);
    }
    (k, v)
}

/// Closes the gaps that removed entries left, keeping the order of the others.
fn compact(state: &mut State) {
    let n = state.stride();
    let mut words = Vec::with_capacity(state.count * n);
    for p in (0..state.live.len()).filter(|&p| state.live[p]) {
        words.extend_from_slice(state.entry(p));
    }
    state.words = words;
    state.live = vec![true; state.count];
    state.reindex(state.count);
}
