//! The adapters of iterators (views.adapters): each makes a node that holds the iterators it reads
//! and its closure, and runs nothing until a consumer pulls it (views.laziness). Each takes the
//! witness of its element type, and of its result's where it has one of its own.

use super::{Kind, node, shape, values};
use crate::abi::Ret;
use crate::shape::Shape;

/// `it.map(f)`: each element passed through `f`.
///
/// # Safety
///
/// `it` is a live iterator and `f` a live closure from its elements to elements of the shape
/// `out`.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_map(
    _loc: u64,
    shape_in: u64,
    out: u64,
    it: u64,
    f: u64,
) -> Ret {
    let fields = [it, f, shape_in, 0];
    node(
        Kind::MapWith,
        Shape(out),
        fields,
        [true, true, false, false],
        &[it],
    )
}

/// The adapter of `kind`, whose elements are those of `it`, with the closure `p`.
///
/// # Safety
///
/// `it` is a live iterator and `p` a live closure from its elements to `bool`.
unsafe fn with_closure(kind: Kind, it: u64, p: u64) -> Ret {
    // SAFETY: the caller guarantees the iterator.
    let elements = unsafe { shape(it) };
    node(
        kind,
        elements,
        [it, p, 0, 0],
        [true, true, false, false],
        &[it],
    )
}

/// The adapter of `kind`, whose elements are those of `it`, with the count `n`.
///
/// # Safety
///
/// `it` is a live iterator.
unsafe fn with_count(kind: Kind, it: u64, n: u64) -> Ret {
    // SAFETY: the caller guarantees the iterator.
    let elements = unsafe { shape(it) };
    node(
        kind,
        elements,
        [it, 0, n, 0],
        [true, false, false, false],
        &[it],
    )
}

/// `it.filter(keep)`: the elements that `keep` accepts.
///
/// # Safety
///
/// As for [`with_closure`].
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_filter(
    _loc: u64,
    _shape: u64,
    it: u64,
    keep: u64,
) -> Ret {
    // SAFETY: as the caller guarantees.
    unsafe { with_closure(Kind::Filter, it, keep) }
}

/// `it.take(n)`: the first `n` elements.
///
/// # Safety
///
/// `it` is a live iterator.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_take(
    _loc: u64,
    _shape: u64,
    it: u64,
    n: u64,
) -> Ret {
    // SAFETY: as the caller guarantees.
    unsafe { with_count(Kind::Take, it, n) }
}

/// `it.skip(n)`: the elements after the first `n`.
///
/// # Safety
///
/// `it` is a live iterator.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_skip(
    _loc: u64,
    _shape: u64,
    it: u64,
    n: u64,
) -> Ret {
    // SAFETY: as the caller guarantees.
    unsafe { with_count(Kind::Skip, it, n) }
}

/// `it.take_while(p)`: the elements before the first that `p` rejects.
///
/// # Safety
///
/// As for [`with_closure`].
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_take_while(
    _loc: u64,
    _shape: u64,
    it: u64,
    p: u64,
) -> Ret {
    // SAFETY: as the caller guarantees.
    unsafe { with_closure(Kind::TakeWhile, it, p) }
}

/// `it.skip_while(p)`: the elements from the first that `p` rejects.
///
/// # Safety
///
/// As for [`with_closure`].
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_skip_while(
    _loc: u64,
    _shape: u64,
    it: u64,
    p: u64,
) -> Ret {
    // SAFETY: as the caller guarantees.
    unsafe { with_closure(Kind::SkipWhile, it, p) }
}

/// `it.enumerate(start)`: each element paired with its index, counting from `start`.
///
/// # Safety
///
/// `it` is a live iterator of elements of the shape `elements`.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_enumerate(
    _loc: u64,
    elements: u64,
    it: u64,
    start: u64,
) -> Ret {
    let pair = values::tuple_shape(&[Shape::word(false), Shape(elements)]);
    let fields = [it, 0, start, elements];
    node(
        Kind::Enumerate,
        pair,
        fields,
        [true, false, false, false],
        &[it],
    )
}

/// `it.zip(other)`: the pairs of the elements of both, ending with the shorter.
///
/// # Safety
///
/// `it` and `other` are live iterators of elements of the shapes `first` and `second`.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_zip(
    _loc: u64,
    first: u64,
    second: u64,
    it: u64,
    other: u64,
) -> Ret {
    let pair = values::tuple_shape(&[Shape(first), Shape(second)]);
    let fields = [it, other, first, second];
    node(
        Kind::Zip,
        pair,
        fields,
        [true, true, false, false],
        &[it, other],
    )
}

/// `it.chain(other)`: the elements of `it`, then those of `other`.
///
/// # Safety
///
/// `it` and `other` are live iterators of elements of one shape.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_chain(
    _loc: u64,
    _shape: u64,
    it: u64,
    other: u64,
) -> Ret {
    // SAFETY: the caller guarantees the iterator.
    let elements = unsafe { shape(it) };
    let fields = [it, other, 0, 0];
    node(
        Kind::Chain,
        elements,
        fields,
        [true, true, false, false],
        &[it, other],
    )
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_std_view_Iter_map,
        stilt_std_view_Iter_filter,
        stilt_std_view_Iter_take,
        stilt_std_view_Iter_skip,
        stilt_std_view_Iter_take_while,
        stilt_std_view_Iter_skip_while,
        stilt_std_view_Iter_enumerate,
        stilt_std_view_Iter_zip,
        stilt_std_view_Iter_chain,
    ]
}
