//! The iterators of `std.view` (views.making-iterator, views.adapters, views.laziness and views.consumers). An iterator is a data object, a
//! *node*: a source, which holds the list, map or string its elements come from with a
//! reference of its own, or an adapter, which holds the iterators it reads and the closure it
//! calls, captured by copy (values.independent-copies), each with a reference of its own. Making or
//! adapting an iterator runs nothing (views.laziness): a consumer ([`consumers`]) or a `for` loop
//! ([`loops`]) pulls its elements one at a time ([`pull`]), through a state of its own that starts
//! at zero, so that every consumer starts from the first element and the node never changes.
//!
//! An element goes from node to node in the one word that holds it where a type parameter
//! stands, owning its references: its word, or for a value of several words, a box of them
//! ([`values`]). Each node keeps the shape of its elements, which tells which.

mod adapters;
mod consumers;
mod loops;
mod positions;
mod pull;
mod values;

use crate::abi::Ret;
use crate::object::{Header, alloc_data, data_field, dup, set_masks};
use crate::shape::Shape;
use crate::{list, map, text};

/// The kinds of node, which a node's field [`KIND`] holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u64)]
enum Kind {
    /// The elements `B..C` of the list `A`.
    List,
    /// The entries of the map `A`, as pairs, in insertion order.
    Map,
    /// The integers `B..C`.
    Range,
    /// The Unicode scalar values of the bytes `B..C` of the string `A`, each a string.
    Chars,
    /// The bytes `B..C` of the string `A`.
    Bytes,
    /// Each element of `A` passed through the closure `B`; `C` is the shape of `A`'s elements.
    MapWith,
    /// The elements of `A` that the closure `B` accepts.
    Filter,
    /// The first `C` elements of `A`.
    Take,
    /// The elements of `A` after the first `C`.
    Skip,
    /// The elements of `A` before the first that the closure `B` rejects.
    TakeWhile,
    /// The elements of `A` from the first that the closure `B` rejects.
    SkipWhile,
    /// Each element of `A` paired with its index, counting from `C`; `D` is the shape of `A`'s.
    Enumerate,
    /// The pairs of the elements of `A` and `B`; `C` and `D` are the shapes of theirs.
    Zip,
    /// The elements of `A`, then those of `B`.
    Chain,
}

impl Kind {
    const ALL: [Kind; 14] = [
        Kind::List,
        Kind::Map,
        Kind::Range,
        Kind::Chars,
        Kind::Bytes,
        Kind::MapWith,
        Kind::Filter,
        Kind::Take,
        Kind::Skip,
        Kind::TakeWhile,
        Kind::SkipWhile,
        Kind::Enumerate,
        Kind::Zip,
        Kind::Chain,
    ];

    /// The words of state the node itself keeps while it is pulled: a position, a count or a
    /// flag, or none for an adapter that only calls its closure.
    const fn own_state(self) -> usize {
        match self {
            Kind::MapWith | Kind::Filter | Kind::Zip => 0,
            _ => 1,
        }
    }
}

/// The fields of a node: its kind, the words of state its whole tree keeps, the shape of its
/// elements, then four that its kind gives a meaning to.
const KIND: usize = 0;
const STATE: usize = 1;
const SHAPE: usize = 2;
const A: usize = 3;
const B: usize = 4;
const C: usize = 5;
const D: usize = 6;
const FIELDS: usize = 7;

/// A field of a node.
///
/// # Safety
///
/// `node` is a live node.
unsafe fn field(node: u64, i: usize) -> u64 {
    // SAFETY: the caller guarantees the node, which has `FIELDS` fields.
    unsafe { *data_field(node as *mut Header, i) }
}

/// The kind of a node.
///
/// # Safety
///
/// `node` is a live node.
unsafe fn kind(node: u64) -> Kind {
    // SAFETY: the caller guarantees the node, whose kind is one of `Kind::ALL`.
    Kind::ALL[usize::try_from(unsafe { field(node, KIND) }).unwrap_or(0)]
}

/// The words of state that pulling a node's tree keeps.
///
/// # Safety
///
/// `node` is a live node.
unsafe fn state_len(node: u64) -> usize {
    // SAFETY: as the caller guarantees.
    usize::try_from(unsafe { field(node, STATE) }).unwrap_or(0)
}

/// The shape of a node's elements.
///
/// # Safety
///
/// `node` is a live node.
unsafe fn shape(node: u64) -> Shape {
    // SAFETY: as the caller guarantees.
    Shape(unsafe { field(node, SHAPE) })
}

/// A new node of `kind`, whose elements have the shape `shape`, with the fields `A` to `D`,
/// of which those marked in `heap` are heap words whose references it takes: a new reference
/// to each, since a native borrows its arguments. `inner` are the nodes it reads, whose states
/// follow its own.
fn node(kind: Kind, shape: Shape, fields: [u64; 4], heap: [bool; 4], inner: &[u64]) -> Ret {
    // SAFETY: the inner nodes are fields of the new one, alive as the caller's arguments.
    let state = kind.own_state()
        + inner
            .iter()
            .map(|&n| unsafe { state_len(n) })
            .sum::<usize>();
    let object = alloc_data(FIELDS, 0);
    // SAFETY: the object was just allocated with `FIELDS` fields; each heap field is a live
    // argument, which gets a reference of its own.
    unsafe {
        let words = [kind as u64, state as u64, shape.0];
        for (i, w) in words.into_iter().chain(fields).enumerate() {
            *data_field(object, i) = w;
        }
        for (&w, &h) in fields.iter().zip(&heap) {
            if h {
                dup(w);
            }
        }
        let mask = heap
            .iter()
            .enumerate()
            .fold(0, |m, (i, &h)| m | u64::from(h) << (A + i));
        set_masks(object, |_| mask);
    }
    Ret::ok(object as u64)
}

/// `Iter.of(xs)`: the elements of `xs`, in order.
///
/// # Safety
///
/// `xs` is a live list.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_of(_loc: u64, shape: u64, xs: u64) -> Ret {
    // SAFETY: the caller guarantees the list.
    let len = unsafe { list::len(xs as *mut Header) } as u64;
    node(
        Kind::List,
        Shape(shape),
        [xs, 0, len, 0],
        [true, false, false, false],
        &[],
    )
}

/// `Iter.of_view(v)`: the elements of a view of a list, in order.
///
/// # Safety
///
/// `source` is a live list, and `start..end` in its bounds.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_of_view(
    _loc: u64,
    shape: u64,
    source: u64,
    start: u64,
    end: u64,
) -> Ret {
    let fields = [source, start, end, 0];
    node(
        Kind::List,
        Shape(shape),
        fields,
        [true, false, false, false],
        &[],
    )
}

/// `view.of_map(m)`: the entries of `m` as pairs, in insertion order (views.making-iterator). The
/// key's witness comes with its dictionaries of `Eq` and `Hash`, which the map already holds.
///
/// # Safety
///
/// `m` is a live map.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_of_map(
    _loc: u64,
    _key: u64,
    _eq: u64,
    _hash: u64,
    _value: u64,
    m: u64,
) -> Ret {
    // SAFETY: the caller guarantees the map.
    let (k, v) = unsafe { map::shapes(m as *mut Header) };
    let pair = values::tuple_shape(&[k, v]);
    node(
        Kind::Map,
        pair,
        [m, 0, 0, 0],
        [true, false, false, false],
        &[],
    )
}

/// `view.range(start, end)`: the integers from `start` up to but excluding `end`.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_view_range(_loc: u64, start: u64, end: u64) -> Ret {
    node(
        Kind::Range,
        Shape::word(false),
        [0, start, end, 0],
        [false; 4],
        &[],
    )
}

/// `view.chars(v)`: the Unicode scalar values of a view of a string, each a string.
///
/// # Safety
///
/// `source` is a live string, and `start..end` in its bounds, on UTF-8 boundaries.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_chars(
    _loc: u64,
    source: u64,
    start: u64,
    end: u64,
) -> Ret {
    let fields = [source, start, end, 0];
    node(
        Kind::Chars,
        crate::shape::STR,
        fields,
        [true, false, false, false],
        &[],
    )
}

/// `view.bytes(v)`: the bytes of a view of a string.
///
/// # Safety
///
/// `source` is a live string, and `start..end` in its bounds.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_bytes(
    _loc: u64,
    source: u64,
    start: u64,
    end: u64,
) -> Ret {
    let fields = [source, start, end, 0];
    node(
        Kind::Bytes,
        crate::shape::U8,
        fields,
        [true, false, false, false],
        &[],
    )
}

/// The character of a string that starts at byte `at`, before byte `end`, and its length.
///
/// # Safety
///
/// `s` is a live string, and `at` and `end` lie on UTF-8 boundaries in its bounds.
unsafe fn char_at(s: u64, at: usize, end: usize) -> Option<(u64, usize)> {
    // SAFETY: the caller guarantees the string and the boundaries.
    let c = unsafe { text::text(&s) }.get(at..end)?.chars().next()?;
    let mut buffer = [0; 4];
    Some((text::from(c.encode_utf8(&mut buffer)), c.len_utf8()))
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    let mut all = crate::exports![
        stilt_std_view_Iter_of,
        stilt_std_view_Iter_of_view,
        stilt_std_view_of_map,
        stilt_std_view_range,
        stilt_std_view_chars,
        stilt_std_view_bytes,
    ];
    all.extend(adapters::symbols());
    all.extend(consumers::symbols());
    all.extend(positions::symbols());
    all.extend(loops::symbols());
    all
}
