//! The functions that compiled code calls for what it doesn't do inline: counting references,
//! allocating, copying on write, and reaching into lists and maps.
//!
//! Every function here takes and returns words, as the compiler's code passes them. Where one
//! returns a word without a count of its own, it says so, and the caller counts a reference
//! before it keeps the word.

use crate::object::{self, Header};
use crate::shape::Shape;
use crate::{list, panic, text};

/// Counts one more reference to a heap word.
///
/// # Safety
///
/// `word` is a live heap word.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_dup(word: u64) {
    // SAFETY: the caller guarantees the word is live.
    unsafe { object::dup(word) }
}

/// Counts one reference less to a heap word, freeing its object after the last.
///
/// # Safety
///
/// `word` is a heap word that owns a reference.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_drop(word: u64) {
    // SAFETY: the caller guarantees the word owns a reference.
    unsafe { object::drop(word) }
}

/// A new data object of `len` fields and tag `tag`, whose masks are zero and whose fields
/// the caller sets.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_alloc_data(len: u64, tag: u64) -> u64 {
    let len = usize::try_from(len).expect("a data object of under 2^63 fields");
    object::alloc_data(
        len,
        u16::try_from(tag).expect("a variant index under 65536"),
    ) as u64
}

/// Makes the object a slot holds unique, copying it if it is shared, and returns it.
///
/// # Safety
///
/// `slot` points to a word that owns a live data object, list or map.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_unique(slot: u64) -> u64 {
    let slot = slot as usize as *mut u64;
    // SAFETY: the caller guarantees the slot holds an object it owns.
    unsafe { object::unique(slot) as u64 }
}

/// A pointer to the words of the value that a slot holds in one word, of the shape `shape`,
/// as an `inout` argument passes them: for a value of several words, the fields of its box,
/// made unique, and otherwise the slot.
///
/// # Safety
///
/// `slot` points to a word that owns a live value of this shape.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_inout_words(slot: u64, shape: u64) -> u64 {
    let slot = slot as usize as *mut u64;
    if Shape(shape).words() <= 1 {
        return slot as u64;
    }
    // SAFETY: the caller guarantees the slot owns the value, here a box of its words.
    unsafe { object::data_field(object::unique(slot), 0) as u64 }
}

/// A new empty list with room for `cap` elements of the shape `shape`.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_list_new(cap: u64, shape: u64) -> u64 {
    let cap = usize::try_from(cap).expect("a list of under 2^63 elements");
    list::new(cap, Shape(shape)) as u64
}

/// Appends a value, in the one word that holds it where a type parameter stands, which it
/// consumes, to a list that nothing else references.
///
/// # Safety
///
/// `list` is a live list that nothing else references, and `x` a live value of its elements'
/// type, which owns its references.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_list_push(list: u64, x: u64) {
    // SAFETY: the caller guarantees the list is unique and the value alive.
    unsafe { list::push_value(list as *mut Header, x) }
}

/// Appends a value, in the one word that holds it where a type parameter stands, which it
/// consumes, to the list a slot holds, made unique.
///
/// # Safety
///
/// `slot` points to a word that owns a live list, and `x` is a live value of its elements'
/// type, which owns its references.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_list_append_value(slot: u64, x: u64) {
    let slot = slot as usize as *mut u64;
    // SAFETY: the caller guarantees the slot holds a list it owns and the value is alive.
    unsafe { list::push_value(list::reserve(slot), x) }
}

/// Appends an element, whose words are at `words`, which it takes, to a list that nothing else
/// references: the words of a value held inline, or a narrow scalar in the low bytes of a word.
///
/// # Safety
///
/// `list` is a live list that nothing else references, and `words` points to the words of a
/// live value of its elements' type, which own their references.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_list_push_words(list: u64, words: u64) {
    let words = words as usize as *const u8;
    // SAFETY: the caller guarantees the list is unique and the words are an element's.
    unsafe { list::push_bytes(list as *mut Header, words) }
}

/// Appends an element, whose words are at `words`, which it takes, to the list a slot holds,
/// made unique.
///
/// # Safety
///
/// `slot` points to a word that owns a live list, and `words` to the words of a live value of
/// its elements' type, which own their references.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_list_append_words(slot: u64, words: u64) {
    let slot = slot as usize as *mut u64;
    let words = words as usize as *const u8;
    // SAFETY: the caller guarantees the slot holds a list it owns and the words are an
    // element's.
    unsafe { list::push_bytes(list::reserve(slot), words) }
}

/// The number of elements of a list.
///
/// # Safety
///
/// `list` is a live list.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_list_len(list: u64) -> u64 {
    // SAFETY: the caller guarantees the list is alive.
    unsafe { list::len(list as *mut Header) as u64 }
}

/// Word `word` of element `i` of a list, which must be in bounds, without a count of its own:
/// a packed scalar widened to a word.
///
/// # Safety
///
/// `list` is a live list with more than `i` elements, of more than `word` words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_list_at(list: u64, i: u64, _elem: u64, word: u64) -> u64 {
    let (list, i) = (
        list as *mut Header,
        usize::try_from(i).unwrap_or(usize::MAX),
    );
    // SAFETY: the caller guarantees the element and its word exist.
    unsafe {
        if list::shape(list).packed() {
            list::take(list, i)
        } else {
            list::element_words(list, i)[usize::try_from(word).unwrap_or(usize::MAX)]
        }
    }
}

/// The panic of an index out of a list's bounds (std.lists).
pub(crate) fn out_of_bounds(loc: u64, i: i64, len: usize) -> ! {
    panic::panic(
        loc,
        panic::BOUNDS,
        &format!("index {i} is out of bounds for a list of length {len}"),
    )
}

/// The index `i` of a list, or a panic with `bounds` at `loc` (std.lists).
///
/// # Safety
///
/// `list` is a live list.
unsafe fn in_bounds(loc: u64, list: *mut Header, i: i64) -> usize {
    // SAFETY: the caller guarantees the list is alive.
    let len = unsafe { list::len(list) };
    usize::try_from(i)
        .ok()
        .filter(|&i| i < len)
        .unwrap_or_else(|| out_of_bounds(loc, i, len))
}

/// The first word of `xs[i]`, without a count of its own, or a panic with `bounds` at `loc`
/// (std.lists). Compiled code reads elements inline, and calls this when `i` is out of
/// bounds.
///
/// # Safety
///
/// `list` is a live list.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_list_index(loc: u64, list: u64, i: i64) -> u64 {
    // SAFETY: the caller guarantees the list is alive, and the index is checked.
    unsafe {
        let i = in_bounds(loc, list as *mut Header, i) as u64;
        stilt_rt_list_at(list, i, 0, 0)
    }
}

/// `xs[i]`, in the one word that holds it where a type parameter stands, with references of
/// its own, or a panic with `bounds` at `loc`.
///
/// # Safety
///
/// `list` is a live list.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_list_get(loc: u64, list: u64, i: i64) -> u64 {
    let list = list as *mut Header;
    // SAFETY: the caller guarantees the list is alive, and the index is checked.
    unsafe { list::get(list, in_bounds(loc, list, i)) }
}

/// A pointer to element `i` of the list a slot holds, made unique so that the element can be
/// written, or a panic with `bounds` at `loc`.
///
/// # Safety
///
/// `slot` points to a word that owns a live list.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_list_slot(loc: u64, slot: u64, i: i64) -> u64 {
    let slot = slot as usize as *mut u64;
    // SAFETY: the caller guarantees the slot holds a list it owns.
    let element = unsafe {
        list::element_slot(slot, i)
            .unwrap_or_else(|| out_of_bounds(loc, i, list::len(*slot as *mut Header)))
    };
    element as usize as u64
}

/// `xs[i] = x` on the list a slot holds, made unique, `x` being in the one word that holds it
/// where a type parameter stands, which it consumes; or a panic with `bounds` at `loc`.
///
/// # Safety
///
/// `slot` points to a word that owns a live list, and `x` is a live value of its elements'
/// type, which owns its references.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_list_put(loc: u64, slot: u64, i: i64, x: u64) {
    let slot = slot as usize as *mut u64;
    // SAFETY: the caller guarantees the slot holds a list it owns and the value is alive; the
    // old element is released before the new one counts its references.
    unsafe {
        let list = object::unique(slot);
        let i = in_bounds(loc, list, i);
        list::release(list, i);
        list::write(list, i, x);
        if list::shape(list).heap() {
            object::drop(x);
        }
    }
}

/// The concatenation of a list of strings, which it borrows: the text of an interpolation.
///
/// # Safety
///
/// `parts` is a live list of strings.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_concat(parts: u64) -> u64 {
    // SAFETY: the caller guarantees the list and its strings are alive.
    unsafe {
        let parts = list::words(parts as *mut Header);
        text::concat(parts.iter().map(|p| text::bytes(p)))
    }
}

/// The concatenation of two strings, which it borrows: the text of an interpolation of two
/// parts, as of three and of four.
///
/// # Safety
///
/// The strings are alive.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_concat2(a: u64, b: u64) -> u64 {
    // SAFETY: the caller guarantees the strings are alive.
    text::concat([a, b].iter().map(|s| unsafe { text::bytes(s) }))
}

/// The concatenation of three strings, which it borrows.
///
/// # Safety
///
/// The strings are alive.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_concat3(a: u64, b: u64, c: u64) -> u64 {
    // SAFETY: the caller guarantees the strings are alive.
    text::concat([a, b, c].iter().map(|s| unsafe { text::bytes(s) }))
}

/// The concatenation of four strings, which it borrows.
///
/// # Safety
///
/// The strings are alive.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_concat4(a: u64, b: u64, c: u64, d: u64) -> u64 {
    // SAFETY: the caller guarantees the strings are alive.
    text::concat([a, b, c, d].iter().map(|s| unsafe { text::bytes(s) }))
}

/// The string `a`, which it takes, with `b` after it, appended in place when nothing else
/// references `a`: the text of an interpolation of two parts that starts with a string released
/// after it, as `s = "{s}{x}"` is; as of three and of four.
///
/// # Safety
///
/// `a` is a live string the caller owns, and `b` a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_concat_onto2(a: u64, b: u64) -> u64 {
    // SAFETY: the caller guarantees the strings are alive and that it owns `a`.
    unsafe { text::onto(a, &[text::bytes(&b)]) }
}

/// The string `a`, which it takes, with `b` and `c` after it.
///
/// # Safety
///
/// `a` is a live string the caller owns, and the others live strings.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_concat_onto3(a: u64, b: u64, c: u64) -> u64 {
    // SAFETY: the caller guarantees the strings are alive and that it owns `a`.
    unsafe { text::onto(a, &[text::bytes(&b), text::bytes(&c)]) }
}

/// The string `a`, which it takes, with `b`, `c` and `d` after it.
///
/// # Safety
///
/// `a` is a live string the caller owns, and the others live strings.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_concat_onto4(a: u64, b: u64, c: u64, d: u64) -> u64 {
    // SAFETY: the caller guarantees the strings are alive and that it owns `a`.
    unsafe { text::onto(a, &[text::bytes(&b), text::bytes(&c), text::bytes(&d)]) }
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_rt_dup,
        stilt_rt_drop,
        stilt_rt_alloc_data,
        stilt_rt_unique,
        stilt_rt_concat_onto2,
        stilt_rt_concat_onto3,
        stilt_rt_concat_onto4,
        stilt_rt_inout_words,
        stilt_rt_list_new,
        stilt_rt_list_push,
        stilt_rt_list_push_words,
        stilt_rt_list_append_value,
        stilt_rt_list_append_words,
        stilt_rt_list_len,
        stilt_rt_list_at,
        stilt_rt_list_index,
        stilt_rt_list_get,
        stilt_rt_list_slot,
        stilt_rt_list_put,
        stilt_rt_concat,
        stilt_rt_concat2,
        stilt_rt_concat3,
        stilt_rt_concat4,
    ]
}
