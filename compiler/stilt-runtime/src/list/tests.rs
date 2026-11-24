use crate::layout::{SHAPE_MASK_SHIFT, SHAPE_SIGNED, SHAPE_SIZE_SHIFT};
use crate::object::{self, Header, data_field};
use crate::shape::Shape;
use crate::text;

/// The shape of a record of a scalar then a string, held inline in two words.
const PAIR: Shape = Shape(1 | 16 << SHAPE_SIZE_SHIFT | 0b10 << SHAPE_MASK_SHIFT);

/// The count of the object a heap word points to.
fn count(word: u64) -> u32 {
    // SAFETY: each test passes a live object.
    unsafe { (*(word as *mut Header)).rc }
}

/// A new box of a scalar and a string, which takes the string's reference.
fn pair(n: u64, s: u64) -> u64 {
    super::values::box_of(&[n, s], PAIR)
}

#[test]
fn a_narrow_scalar_is_read_back_with_its_sign() {
    let signed = |bytes: u64| Shape(SHAPE_SIGNED | bytes << SHAPE_SIZE_SHIFT);
    for (shape, x) in [
        (signed(1), (-128i64).cast_unsigned()),
        (Shape::unsigned(1), 255),
        (signed(2), (-2i64).cast_unsigned()),
        (Shape::unsigned(2), 65535),
        (signed(4), (-5i64).cast_unsigned()),
        (Shape::unsigned(4), u64::from(1.5f32.to_bits())),
    ] {
        let list = super::new(1, shape);
        // SAFETY: the list is new, with room for one element.
        unsafe {
            super::insert(list, 0, x);
            assert_eq!(super::get(list, 0), x, "{shape:?}");
            assert_eq!(super::remove(list, 0, std::ptr::null_mut()), x, "{shape:?}");
            object::drop(list as u64);
        }
    }
}

#[test]
fn a_record_held_inline_counts_its_heap_words() {
    let s = text::from("shared by the copies");
    let list = super::new(0, PAIR);
    // SAFETY: the list and the boxes are live, and each reference is released once.
    unsafe {
        let first = pair(1, s);
        super::insert(list, 0, first);
        object::drop(first);
        assert_eq!(count(s), 1, "the element holds the string");
        let copy = super::copy(list);
        assert_eq!(count(s), 2);
        let got = super::get(copy, 0);
        assert_eq!((*data_field(got as *mut Header, 0), count(s)), (1, 3));
        object::drop(got);
        let mut loan = super::Loan::new();
        let lent = super::lend(list, 0, &mut loan);
        assert_eq!((count(lent), count(s)), (0, 2), "a loan counts nothing");
        object::drop(copy as u64);
        object::drop(list as u64);
    }
}

#[test]
fn removing_and_inserting_move_the_elements_after() {
    let list = super::from_words(&[1, 2, 3], Shape::word(false));
    // SAFETY: the list is live and its own.
    unsafe {
        assert_eq!(super::remove(list, 0, std::ptr::null_mut()), 1);
        super::insert(list, 1, 9);
        assert_eq!(super::words(list), [2, 9, 3]);
        let slice = super::copy_range(list, 1, 3, 0);
        assert_eq!(super::words(slice), [9, 3]);
        object::drop(slice as u64);
        object::drop(list as u64);
    }
}
