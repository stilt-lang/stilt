//! Strings: owned, immutable sequences of UTF-8 bytes (values.strings).
//!
//! A string is one word, in one of two forms. A string of at most [`INLINE`] bytes that the
//! runtime makes is held in the word itself, an immediate: on the little-endian targets the
//! runtime supports, the word's first byte is twice the string's length plus one, which sets the
//! lowest bit that marks an immediate, and its other bytes are the string's, then zeros. Any
//! other string is a pointer to an object, which holds the string's length after its header,
//! then its bytes. A string literal is an immortal object that the compiler emits in that
//! layout, whatever its length.
//!
//! Strings are values, so a program can't tell the two forms apart: equal strings may have
//! different forms, and are compared by their bytes. A string held in its word is made and
//! released without the pool, so slicing, splitting or interpolating short text allocates
//! nothing, and a list of short strings holds their bytes in its elements. A slice copies its
//! bytes rather than share its parent's: a string is one word, so a view of a parent would take
//! an object of its own, which costs what a copy of a few hundred bytes does, and would keep a
//! large parent alive for as long as a small slice of it lives.
//!
//! A string that the program appends to has room after its bytes, which its header's `len`
//! counts, and which only [`onto`] writes: a string nothing else references is written in place
//! when it has room, and grows to twice its length when it hasn't, so `s = "{s}{x}"` in a loop
//! runs in time linear in what it appends, as pushing onto a list does.

use std::fmt::Write as _;

use crate::object::{HEADER, Header, STR, alloc_object};

#[cfg(test)]
mod tests;

const _: () = assert!(
    cfg!(target_endian = "little"),
    "a string held in its word keeps its bytes after the word's first"
);

/// The most bytes a string held in its word has.
pub(crate) const INLINE: usize = 7;

/// The offset of a string object's bytes.
pub(crate) const BYTES: usize = HEADER + 8;

/// Whether a string is held in its word, rather than in an object.
pub(crate) const fn is_inline(word: u64) -> bool {
    word & 1 != 0
}

/// The word of a string of at most [`INLINE`] bytes, held in the word. Its bytes are read by
/// loads of fixed sizes, since a copy of a length known only at run time calls `memcpy`: two
/// loads of four bytes that overlap for four to seven, and the first, middle and last bytes for
/// one to three.
fn inline(bytes: &[u8]) -> u64 {
    let n = bytes.len();
    debug_assert!(n <= INLINE, "a string short enough for its word");
    let body = match n {
        0 => 0,
        1..=3 => {
            u64::from(bytes[0])
                | u64::from(bytes[n / 2]) << (8 * (n / 2))
                | u64::from(bytes[n - 1]) << (8 * (n - 1))
        }
        _ => {
            let four = |at: usize| {
                let word = [bytes[at], bytes[at + 1], bytes[at + 2], bytes[at + 3]];
                u64::from(u32::from_le_bytes(word))
            };
            four(0) | four(n - 4) << (8 * (n - 4))
        }
    };
    body << 8 | (n as u64) << 1 | 1
}

/// Copies `src` to `dst`: a part of at most 16 bytes, as most parts of a text are, by two loads
/// and two stores of one size that overlap, and a longer one by `memcpy`, whose call would cost
/// a short part more than its bytes.
///
/// # Safety
///
/// `dst` has room for the bytes of `src`, which doesn't overlap it.
unsafe fn copy(src: &[u8], dst: *mut u8) {
    /// Copies `n` bytes, from `size` to twice as many, as two words of `size` bytes.
    ///
    /// # Safety
    ///
    /// As for [`copy`].
    unsafe fn twice<T>(s: *const u8, dst: *mut u8, n: usize) {
        let last = n - std::mem::size_of::<T>();
        // SAFETY: both words lie within the `n` bytes of each side.
        unsafe {
            let (a, b) = (
                s.cast::<T>().read_unaligned(),
                s.add(last).cast::<T>().read_unaligned(),
            );
            dst.cast::<T>().write_unaligned(a);
            dst.add(last).cast::<T>().write_unaligned(b);
        }
    }
    let (s, n) = (src.as_ptr(), src.len());
    // SAFETY: as the caller guarantees.
    unsafe {
        match n {
            0 => {}
            1 => dst.write(*s),
            2..=3 => twice::<u16>(s, dst, n),
            4..=7 => twice::<u32>(s, dst, n),
            8..=16 => twice::<u64>(s, dst, n),
            _ => std::ptr::copy_nonoverlapping(s, dst, n),
        }
    }
}

/// The size of a string object.
///
/// # Safety
///
/// `object` is a live string object.
pub(crate) unsafe fn size(object: *mut Header) -> usize {
    // SAFETY: the caller guarantees `object` is a string, which holds its length and its room.
    BYTES + unsafe { len(object as u64) + (*object).extent as usize }
}

/// The string `a`, which it takes, with `parts` after it: written in `a`'s own memory when it
/// is an object that nothing else references, which grows to twice its length when its room is
/// too small, and otherwise a new string, with as much room if it needs an object, `a`
/// released, as it is when the parts hold more than a header's `len` counts. No part is `a`'s
/// memory, since a part that is `a` references it too.
///
/// # Safety
///
/// `a` is a live string that the caller owns, and the parts outlive the call.
pub(crate) unsafe fn onto(a: u64, parts: &[&[u8]]) -> u64 {
    let added: usize = parts.iter().map(|p| p.len()).sum();
    let object = a as *mut Header;
    // SAFETY: the caller guarantees `a` is a live string it owns.
    unsafe {
        let len = len(a);
        if is_inline(a) || !crate::object::is_unique(object) || u32::try_from(added).is_err() {
            let out = with_room(bytes(&a), parts, len + added);
            crate::object::drop(a);
            return out;
        }
        let room = (*object).extent as usize;
        let object = if room < added {
            grown(object, len, len + added)
        } else {
            object
        };
        let mut at = object.cast::<u8>().add(BYTES + len);
        for part in parts {
            copy(part, at);
            at = at.add(part.len());
        }
        object
            .cast::<u8>()
            .add(HEADER)
            .cast::<u64>()
            .write((len + added) as u64);
        (*object).extent -= u32::try_from(added).expect("room for the parts");
        object as u64
    }
}

/// The room a string of `len` bytes is given when it grows: as many bytes again, within what a
/// header's `len` counts.
fn room_for(len: usize) -> u32 {
    u32::try_from(len).unwrap_or(u32::MAX)
}

/// A new string of `first` and then `parts`, `total` bytes: held in its word if it is short
/// enough, and otherwise an object with room after them.
fn with_room(first: &[u8], parts: &[&[u8]], total: usize) -> u64 {
    if total <= INLINE {
        return concat(std::iter::once(first).chain(parts.iter().copied()));
    }
    let room = room_for(total);
    let object = alloc_object(BYTES + total + room as usize, STR, 0, 0, room);
    // SAFETY: the object has room for `total` bytes after its length.
    unsafe {
        object
            .cast::<u8>()
            .add(HEADER)
            .cast::<u64>()
            .write(total as u64);
        let mut at = object.cast::<u8>().add(BYTES);
        for part in std::iter::once(&first).chain(parts) {
            copy(part, at);
            at = at.add(part.len());
        }
    }
    object as u64
}

/// A unique string of `len` bytes resized to hold `needed` bytes and as many again, its room
/// counting the bytes past its length.
///
/// # Safety
///
/// `object` is a live string object of `len` bytes that nothing else references.
unsafe fn grown(object: *mut Header, len: usize, needed: usize) -> *mut Header {
    // SAFETY: the caller guarantees the string is alive and its own.
    unsafe {
        let old = size(object);
        let added = u32::try_from(needed - len).expect("a part that a header's `len` counts");
        let room = room_for(needed).min(u32::MAX - added);
        let new = BYTES + needed + room as usize;
        let object = crate::object::realloc_bytes(object.cast(), old, new).cast::<Header>();
        (*object).extent = room + added;
        object
    }
}

/// A new string holding `bytes`, which are UTF-8.
pub(crate) fn new(bytes: &[u8]) -> u64 {
    if bytes.len() <= INLINE {
        return inline(bytes);
    }
    let mut out = Builder::new(bytes.len());
    out.push(bytes);
    out.finish()
}

/// A new string whose bytes are written in turn, with room for exactly `len` of them, every
/// one of which is written, as UTF-8, before [`Builder::finish`] gives the string: held in its
/// word, or an object.
#[derive(Debug)]
pub(crate) struct Builder {
    /// The string's object, or null for a string held in its word.
    object: *mut Header,
    /// The word of a string held in it, its bytes written as they come.
    word: u64,
    len: usize,
    written: usize,
}

impl Builder {
    pub(crate) fn new(len: usize) -> Self {
        if len <= INLINE {
            return Self {
                object: std::ptr::null_mut(),
                word: (len as u64) << 1 | 1,
                len,
                written: 0,
            };
        }
        let object = alloc_object(BYTES + len, STR, 0, 0, 0);
        // SAFETY: the object has room for its length.
        unsafe {
            let at = object.cast::<u8>().add(HEADER).cast::<u64>();
            at.write(len as u64);
        }
        Self {
            object,
            word: 0,
            len,
            written: 0,
        }
    }

    /// Where the string's bytes start.
    fn start(&mut self) -> *mut u8 {
        if self.object.is_null() {
            // SAFETY: the word's bytes after its first hold the string's.
            unsafe { (&raw mut self.word).cast::<u8>().add(1) }
        } else {
            // SAFETY: the object holds its bytes from `BYTES` on.
            unsafe { self.object.cast::<u8>().add(BYTES) }
        }
    }

    /// Writes `bytes` after those already written.
    pub(crate) fn push(&mut self, bytes: &[u8]) {
        assert!(bytes.len() <= self.len - self.written, "room for the bytes");
        // SAFETY: the string has room for `len` bytes, of which `written` are written, and
        // `bytes` fit after them.
        unsafe { copy(bytes, self.start().add(self.written)) };
        self.written += bytes.len();
    }

    /// The bytes written so far, to change in place.
    pub(crate) fn written_mut(&mut self) -> &mut [u8] {
        // SAFETY: the first `written` bytes are written.
        unsafe { std::slice::from_raw_parts_mut(self.start(), self.written) }
    }

    /// The string, every byte of which is written.
    pub(crate) fn finish(self) -> u64 {
        assert_eq!(self.written, self.len, "every byte written");
        if self.object.is_null() {
            self.word
        } else {
            self.object as u64
        }
    }
}

/// The concatenation of strings.
pub(crate) fn concat<'a>(parts: impl Iterator<Item = &'a [u8]> + Clone) -> u64 {
    let len = parts.clone().map(<[u8]>::len).sum();
    let mut out = Builder::new(len);
    for part in parts {
        out.push(part);
    }
    out.finish()
}

/// A new string of Rust text.
pub(crate) fn from(text: &str) -> u64 {
    new(text.as_bytes())
}

/// The length of a string, in bytes.
///
/// # Safety
///
/// `word` is a live string.
pub(crate) unsafe fn len(word: u64) -> usize {
    if is_inline(word) {
        return (word as usize & 0xff) >> 1;
    }
    // SAFETY: the caller guarantees `word` is a string object, which holds its length.
    let len = unsafe { (word as *const u8).add(HEADER).cast::<u64>().read() };
    usize::try_from(len).expect("a string of under 2^63 bytes")
}

/// The bytes of the string that `word` holds: those of the word itself, or of its object.
///
/// # Safety
///
/// `word` holds a live string, which outlives the slice.
pub(crate) unsafe fn bytes(word: &u64) -> &[u8] {
    // SAFETY: the caller guarantees the string; one held in its word has its bytes after the
    // word's first, and an object its bytes from `BYTES` on.
    unsafe {
        let len = len(*word);
        let start = if is_inline(*word) {
            std::ptr::from_ref(word).cast::<u8>().add(1)
        } else {
            (*word as *const u8).add(BYTES)
        };
        std::slice::from_raw_parts(start, len)
    }
}

/// The text of the string that `word` holds.
///
/// # Safety
///
/// `word` holds a live string, which outlives the text.
pub(crate) unsafe fn text(word: &u64) -> &str {
    // SAFETY: every string holds UTF-8 (values.strings), and the caller guarantees it lives.
    unsafe { std::str::from_utf8_unchecked(bytes(word)) }
}

/// Quotes and escapes text, as a string nested inside another value is shown
/// (std.show-names-and-escapes).
pub(crate) fn quote(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            '\0' => out.push_str("\\0"),
            c if c < ' ' || c == '\u{7f}' => {
                let _ = write!(out, "\\u{{{:x}}}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
