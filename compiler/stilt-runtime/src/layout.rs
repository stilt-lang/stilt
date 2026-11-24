//! The layout of objects as compiled code reads it inline: where the count sits in every
//! object, a data object's layout word, the length, capacity and elements in a list, the bits of
//! a shape ([`crate::shape`]) and the thread's pool of small blocks (goal debug-speed); and the
//! tags that the compiler gives dictionaries. The tests check each offset against the runtime's
//! own definitions, and that the header keeps its bit for objects that threads share apart from
//! every kind's own flags.

/// The low bits of a heap word that are zero for a pointer, since every object is aligned to 8.
pub const ALIGN_BITS: u8 = 7;

/// The offset of an object's reference count, a `u32`, of which 0 marks an immortal object.
pub const RC: i32 = 0;

/// The bit of the word at [`RC`], whose low 32 bits are the count, that is set when threads
/// share the object: its count then changes by atomic instructions, which only the runtime
/// executes, and a write never changes it in place (Values and costs, "Counts that are atomic
/// only when shared"). One load of the word gives the count and the bit, and on both targets a
/// test of one bit branches in one instruction.
pub const SHARED_BIT: u64 = 1 << 47;

/// The size of every object's header, after which a data object's fields start.
pub const HEADER: i32 = 16;

/// The offset of an object's kind, a `u8`.
pub const KIND: u32 = 4;
/// The offset of an object's tag, a `u16`, a variant's index.
pub const TAG: u32 = 6;

/// The offset of a data object's layout word, a `u32` that tells how many fields it has and which
/// of them are heap words ([`data_layout`]).
pub const LAYOUT: u32 = 8;

/// The most fields whose heap bits a data object's layout word holds itself: an object of up to
/// this many fields takes its header and a word per field, and no more, 256 bytes at most.
pub const INLINE_FIELDS: usize = 30;

/// The bit of the layout word of a data object of more than [`INLINE_FIELDS`] fields, whose other
/// bits are its number of fields, and whose mask words follow its fields, one per 64 of them.
pub const LAYOUT_LARGE: u32 = 1 << 31;

/// The number of mask words after the fields of a data object of `len` fields: none for one
/// whose layout word holds its heap bits.
#[must_use]
pub const fn mask_words(len: usize) -> usize {
    if len <= INLINE_FIELDS {
        0
    } else {
        len.div_ceil(64)
    }
}

/// The layout word of a data object of `len` fields whose heap words are the bits of `mask`: for
/// a small object, a bit set above the mask's at `len`, so that the word tells both, and for a
/// larger one, [`LAYOUT_LARGE`] with `len`. The compiler writes it whole where it knows the
/// fields, and compares it whole where it knows what an object it takes apart holds.
#[must_use]
pub const fn data_layout(len: usize, mask: u64) -> u32 {
    if len <= INLINE_FIELDS {
        (1 << len | mask & ((1 << len) - 1)) as u32
    } else {
        LAYOUT_LARGE | len as u32
    }
}

/// The kind of a data object, which the static objects of compiled code are, or strings.
pub const KIND_DATA: u8 = 0;
/// The kind of a string.
pub const KIND_STR: u8 = 1;

/// The offset of a list's length, a `u64`.
pub const LIST_LEN: i32 = 16;

/// The offset of a list's capacity, a `u64`.
pub const LIST_CAP: i32 = 24;

/// The offset of a list's pointer to its elements, each of the size its shape gives.
pub const LIST_DATA: i32 = 32;

/// The bit of a shape that tells whether the word that holds a value where a type parameter
/// stands is a heap word.
pub const SHAPE_HEAP: u64 = 1;

/// The bit of the shape of a scalar narrower than a word whose reads extend its sign.
pub const SHAPE_SIGNED: u64 = 2;

/// Where a shape's size of an element, in bytes, starts.
pub const SHAPE_SIZE_SHIFT: u32 = 2;
/// The bits of a shape's size of an element, from [`SHAPE_SIZE_SHIFT`] on.
pub const SHAPE_SIZE_BITS: u64 = 0x3fff;

/// Where a shape's mask starts, whose bit `16 + i` tells whether word `i` of an element is a
/// heap word.
pub const SHAPE_MASK_SHIFT: u32 = 16;

/// The most words of an element whose heap words a shape's mask tells: the shape of a larger
/// one points to a description of its words ([`crate::shape`]).
pub const MASK_WORDS: usize = 48;

/// The low bits of the shape of an element of more than [`MASK_WORDS`] words, whose bits from
/// [`SHAPE_MASK_SHIFT`] on point to the description of its words.
pub const SHAPE_LARGE: u64 = SHAPE_HEAP | SHAPE_SIGNED;

/// The low bits of the constant that compiled code passes to read and write an element of more
/// than [`MASK_WORDS`] words in place, whose bits from [`SHAPE_MASK_SHIFT`] on are its size in
/// bytes. The runtime never reads it.
pub const SHAPE_SIZED: u64 = SHAPE_SIGNED;

/// The offset in a thread's pool of small blocks (`crate::pool`) of the thread that owns it.
pub const POOL_OWNER: i32 = 0;
/// The offset of the bytes a pool may count before it checks the heap's limit again.
pub const POOL_ROOM: i32 = 8;
/// The offset of the bytes a pool has counted since it last flushed.
pub const POOL_BYTES: i32 = 16;
/// The offset of the objects a pool has counted since it last flushed.
pub const POOL_OBJECTS: i32 = 24;
/// The offset of the free part of a pool's chunk.
pub const POOL_NEXT: i32 = 32;
/// The offset of the end of a pool's chunk.
pub const POOL_END: i32 = 40;
/// The offset of the first block of each of a pool's lists of freed blocks, by size.
pub const POOL_HEADS: i32 = 48;

/// The largest block a pool keeps, in bytes.
pub const POOL_LARGEST: usize = 256;
/// The number of a pool's lists, one for each multiple of 8 up to [`POOL_LARGEST`].
pub const POOL_LISTS: usize = POOL_LARGEST / 8;

/// The tag of the dictionary of the structural `Ord` of a signed integer type, whose keys a sort
/// compares itself.
pub const SIGNED_ORDER: u16 = 1;
/// The tag of the dictionary of the structural `Ord` of an unsigned integer type.
pub const UNSIGNED_ORDER: u16 = 2;

/// The tag of the dictionaries of the structural `Eq` and `Hash` of an integer type or `bool`,
/// whose keys a map hashes and compares itself. Every other dictionary's tag is 0, but those of
/// [`STR_KEYS`] and the orders.
pub const WORD_KEYS: u16 = 3;
/// The tag of the dictionaries of the structural `Eq` and `Hash` of `str`.
pub const STR_KEYS: u16 = 4;

/// The tag of a box: the data object that holds the words of a value of a type that isn't
/// recursive, which no variant's index is. The runtime counts the boxes a program makes, which
/// it reports at its end when `STILT_COUNTS` is set (goal inline-values).
pub const BOX: u16 = u16::MAX;

/// The lowest of the tags that the runtime gives its own data objects, a box, a task's handle and
/// a `Shared<T>`'s handle, which no variant's index reaches: the memory of an object with one of
/// them is never built in again (`crate::object::reuse`).
pub const RUNTIME_TAGS: u16 = u16::MAX - 2;

#[cfg(test)]
mod tests {
    use std::mem::offset_of;

    use crate::object::{HEADER, Header};

    #[test]
    fn the_offsets_are_the_runtimes() {
        assert_eq!(
            super::RC,
            i32::try_from(offset_of!(Header, rc)).unwrap_or(-1)
        );
        let flags = 8 * offset_of!(Header, flags);
        assert_eq!(super::SHARED_BIT, u64::from(crate::object::SHARED) << flags);
        assert_eq!(super::HEADER, i32::try_from(HEADER).unwrap_or(-1));
        assert_eq!(super::KIND as usize, offset_of!(Header, kind));
        assert_eq!(super::TAG as usize, offset_of!(Header, tag));
        assert_eq!(super::KIND_DATA, crate::object::DATA);
        assert_eq!(super::KIND_STR, crate::object::STR);
        let (len, cap, data) = crate::list::body_offsets();
        assert_eq!(super::LIST_LEN, i32::try_from(HEADER + len).unwrap_or(-1));
        assert_eq!(super::LIST_CAP, i32::try_from(HEADER + cap).unwrap_or(-1));
        assert_eq!(super::LIST_DATA, i32::try_from(HEADER + data).unwrap_or(-1));
        assert_eq!(64 - super::SHAPE_MASK_SHIFT as usize, super::MASK_WORDS);
        assert_eq!(super::LAYOUT as usize, offset_of!(Header, extent));
        assert_eq!(
            crate::object::data_size(super::INLINE_FIELDS),
            super::POOL_LARGEST,
            "the largest small data object is the pool's largest block"
        );
        let pool = crate::pool::offsets();
        let ours = [
            super::POOL_OWNER,
            super::POOL_ROOM,
            super::POOL_BYTES,
            super::POOL_OBJECTS,
            super::POOL_NEXT,
            super::POOL_END,
            super::POOL_HEADS,
        ];
        assert_eq!(pool, ours.map(|o| usize::try_from(o).unwrap_or(0)));
        for word in [0, 1, 3, 8, 9, 15, 16, 0x1000, 0x1001, 0x1004] {
            let inline = word != 0 && word & u64::from(super::ALIGN_BITS) == 0;
            assert_eq!(inline, crate::object::pointer(word).is_some(), "{word:#x}");
        }
    }

    #[test]
    fn a_layout_word_tells_the_fields_and_their_heap_words() {
        use super::{INLINE_FIELDS, LAYOUT_LARGE, data_layout};
        assert_eq!(data_layout(0, 0), 1);
        assert_eq!(data_layout(5, 0b1_0010), 0b11_0010);
        assert_eq!(
            data_layout(2, 0b111),
            0b111,
            "bits past the fields are not heap words"
        );
        assert_eq!(data_layout(INLINE_FIELDS, u64::MAX), u32::MAX >> 1);
        assert_eq!(data_layout(INLINE_FIELDS + 1, 1), LAYOUT_LARGE | 31);
        assert_eq!(data_layout(1000, 0), LAYOUT_LARGE | 0x3e8);
    }

    /// A function that copies an object.
    type CopyObject = unsafe fn(*mut Header) -> *mut Header;

    #[test]
    fn the_shared_bit_is_apart_and_unset() {
        use crate::object::SHARED;
        use crate::shape::Shape;
        assert_eq!(SHARED.count_ones(), 1);
        let list = crate::list::from_words(&[1, 2, 3], Shape::word(false));
        let map = crate::map::new(Shape::word(false), Shape::word(true), None);
        // SAFETY: `list` and `map` are the live objects just made, each dropped once at the end
        // with its copy.
        unsafe {
            let copies: [(_, CopyObject); 2] = [(list, crate::list::copy), (map, crate::map::copy)];
            for (original, copy) in copies {
                assert_eq!((*original).flags & SHARED, 0);
                (*original).flags |= SHARED;
                let fresh = copy(original);
                assert_eq!((*fresh).flags & SHARED, 0);
                (*original).flags &= !SHARED;
                crate::object::drop(fresh as u64);
                crate::object::drop(original as u64);
            }
        }
    }
}
