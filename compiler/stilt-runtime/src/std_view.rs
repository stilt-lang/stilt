//! The views of `std.view` (views.what-view-is, views.making-view and views.functions-of-views). A
//! view is the word of its source, a string or a list, with a reference of its own that keeps the
//! source's storage alive, and two offsets into it, counted as `slice` counts them: bytes of a
//! string, elements of a list (views.what-view-is). Compiled code holds the three
//! words inline, makes a view with [`stilt_rt_view_of`] and [`stilt_rt_view_part`], which check
//! its offsets, and computes its length itself; the natives here take a view as its three words.

mod traits;

use crate::abi::{NONE, Ret, some};
use crate::object::{Header, STR, dup};
use crate::support::out_of_bounds;
use crate::{list, panic, structural, text};

/// Whether a source is a string, rather than a list, which is always an object.
///
/// # Safety
///
/// `source` is a live string or list.
pub(super) unsafe fn is_str(source: u64) -> bool {
    // SAFETY: the caller guarantees the source is alive, so a word that isn't a string held in
    // it points to an object.
    text::is_inline(source) || unsafe { (*(source as *const Header)).kind == STR }
}

/// The length of a source: its bytes for a string, its elements for a list.
///
/// # Safety
///
/// `source` is a live string or list.
unsafe fn source_len(source: u64) -> usize {
    // SAFETY: the caller guarantees the object is alive.
    unsafe {
        if is_str(source) {
            text::len(source)
        } else {
            list::len(source as *mut Header)
        }
    }
}

/// The offsets `start..end` of a part of `len` bytes or elements, or a panic with `bounds` at
/// `loc` when `0 <= start <= end <= len` fails (views.making-view, as `slice` panics).
fn checked(loc: u64, start: i64, end: i64, len: usize, of: &str) -> (usize, usize) {
    let range = usize::try_from(start)
        .ok()
        .zip(usize::try_from(end).ok())
        .filter(|&(s, e)| s <= e && e <= len);
    range.unwrap_or_else(|| {
        panic::panic(
            loc,
            panic::BOUNDS,
            &format!("the range {start}..{end} is out of bounds for {of} of length {len}"),
        )
    })
}

/// Panics with `utf8_boundary` at `loc` when an offset of a string splits a UTF-8 sequence, as
/// `str.slice` does (std.str).
///
/// # Safety
///
/// `source` is a live string, and the offsets are in its bounds.
unsafe fn on_boundaries(loc: u64, source: u64, start: usize, end: usize) {
    // SAFETY: the caller guarantees the string is alive.
    let s = unsafe { text::text(&source) };
    if !s.is_char_boundary(start) || !s.is_char_boundary(end) {
        panic::panic(
            loc,
            panic::UTF8_BOUNDARY,
            &format!("the range {start}..{end} splits a UTF-8 sequence"),
        );
    }
}

/// `View.of(source, start, end)` (views.making-view): checks the offsets against the source, and
/// gives the source's word with a reference of its own, which the view holds.
///
/// # Safety
///
/// `source` is a live string or list.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_view_of(
    loc: u64,
    source: u64,
    start: i64,
    end: i64,
) -> u64 {
    // SAFETY: the caller guarantees the source is alive.
    unsafe {
        let (s, e) = checked(loc, start, end, source_len(source), "a source");
        if is_str(source) {
            on_boundaries(loc, source, s, e);
        }
        dup(source);
    }
    source
}

/// The length of a source, which `View.all` views the whole of.
///
/// # Safety
///
/// `source` is a live string or list.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_view_len(source: u64) -> u64 {
    // SAFETY: the caller guarantees the source is alive.
    unsafe { source_len(source) as u64 }
}

/// `v.view(s, e)` of the view `start..end` of `source` (views.making-view): checks `s..e`, counted
/// from the view's start, against the view, and gives the source's word with a reference of its
/// own.
///
/// # Safety
///
/// `source` is a live string or list, and `start..end` in its bounds.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_view_part(
    loc: u64,
    source: u64,
    start: u64,
    end: u64,
    s: i64,
    e: i64,
) -> u64 {
    let len = usize::try_from(end - start).unwrap_or(0);
    let (s, e) = checked(loc, s, e, len, "a view");
    // SAFETY: the caller guarantees the source is alive, and the part lies inside the view.
    unsafe {
        if is_str(source) {
            let base = usize::try_from(start).unwrap_or(0);
            on_boundaries(loc, source, base + s, base + e);
        }
        dup(source);
    }
    source
}

/// The index into a view's source of `v[i]`, for the view `start..end` of a list, or a panic
/// with `bounds` at `loc`, as `xs[i]` panics (views.functions-of-views).
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_view_index(loc: u64, start: u64, end: u64, i: i64) -> u64 {
    let len = usize::try_from(end - start).unwrap_or(0);
    match usize::try_from(i).ok().filter(|&i| i < len) {
        Some(i) => start + i as u64,
        None => out_of_bounds(loc, i, len),
    }
}

/// The viewed part of a source, as a new value: a string or a list (views.functions-of-views).
///
/// # Safety
///
/// `source` is a live string or list, and `start..end` in its bounds.
unsafe fn copy_part(source: u64, start: u64, end: u64) -> u64 {
    let (s, e) = (
        usize::try_from(start).unwrap_or(0),
        usize::try_from(end).unwrap_or(0),
    );
    // SAFETY: the caller guarantees the source is alive and the part in its bounds.
    unsafe {
        if is_str(source) {
            text::new(&text::bytes(&source)[s..e])
        } else {
            structural::slice(source as *mut Header, s, e) as u64
        }
    }
}

/// `v.copy()`: the viewed part as an owned value, which allocates (views.functions-of-views). It
/// takes the memory for a result of several words that a native whose result is a type parameter's
/// value is passed (`crate::abi`), which it doesn't use, since a copy is one word.
///
/// # Safety
///
/// As for [`copy_part`].
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_View_copy(
    _loc: u64,
    _shape: u64,
    source: u64,
    start: u64,
    end: u64,
    _out: u64,
) -> Ret {
    // SAFETY: as the caller guarantees.
    Ret::ok(unsafe { copy_part(source, start, end) })
}

/// `view.get(v, i)`: the element at `i` of a view of a list, with references of its own, and
/// `None` outside the view (views.functions-of-views).
///
/// # Safety
///
/// `source` is a live list, `start..end` in its bounds, and `out` points to room for the words
/// of an element of several words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_get(
    _loc: u64,
    _shape: u64,
    source: u64,
    start: u64,
    end: u64,
    i: i64,
    out: u64,
) -> Ret {
    let out = out as usize as *mut u64;
    let len = end - start;
    let Some(i) = u64::try_from(i).ok().filter(|&i| i < len) else {
        return NONE;
    };
    let at = usize::try_from(start + i).unwrap_or(usize::MAX);
    // SAFETY: the caller guarantees the list, and the index lies inside the view.
    some(unsafe { list::give_copy(source as *mut Header, at, out) })
}

/// `v[i] = x` through a writable view of a list of values of a type parameter
/// (projections.places-through-views): `i` is the index into the list, in bounds, and `x`
/// the one word that holds the value, which it consumes. The list's count isn't checked: a writable
/// binding's storage is unique, and the law of exclusivity keeps every other access away while it
/// lives (projections.reaching-written-source).
///
/// # Safety
///
/// `list` is a live list, `i` in its bounds, and `x` a live value of its elements' type, which
/// owns its references.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_view_put(_loc: u64, list: u64, i: u64, x: u64) {
    let list = list as *mut Header;
    let i = usize::try_from(i).unwrap_or(usize::MAX);
    // SAFETY: the caller guarantees the list and the index; the old element is released before
    // the new one counts its references.
    unsafe {
        list::release(list, i);
        list::write(list, i, x);
        if list::shape(list).heap() {
            crate::object::drop(x);
        }
    }
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    let mut all = crate::exports![
        stilt_rt_view_of,
        stilt_rt_view_len,
        stilt_rt_view_part,
        stilt_rt_view_index,
        stilt_rt_view_put,
        stilt_std_view_View_copy,
        stilt_std_view_get,
    ];
    all.extend(traits::symbols());
    all
}
