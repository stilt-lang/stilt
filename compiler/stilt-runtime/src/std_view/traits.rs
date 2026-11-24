//! `Eq`, `Ord`, `Hash` and `Show` on views (views.functions-of-views): the viewed parts compared,
//! hashed and shown in place, between their offsets, byte by byte for views of strings and
//! element by element, through the dictionaries of the elements, for views of lists, which a
//! view's structural environment holds (`stilt-mir`'s dictionaries), as [`crate::structural`]
//! does for whole strings and lists. A comparison or a hash allocates nothing; a view's hash is
//! that of the value `View.copy` would give, and its text that value's text.

use crate::abi::{COMPARE, EQ, EQUAL, HASH, SHOW_NESTED, method1, method2, ordering};
use crate::list::{self, Loan};
use crate::object::Header;
use crate::structural::{FNV, append_shown, mix};
use crate::text;

use super::is_str;

/// A view, as the source word and the offsets of its three words.
#[derive(Clone, Copy)]
struct Window {
    source: u64,
    start: usize,
    end: usize,
}

impl Window {
    fn new(source: u64, start: u64, end: u64) -> Self {
        let at = |o: u64| usize::try_from(o).unwrap_or(usize::MAX);
        Self {
            source,
            start: at(start),
            end: at(end),
        }
    }

    fn len(self) -> usize {
        self.end - self.start
    }

    /// The viewed bytes of a view of a string.
    ///
    /// # Safety
    ///
    /// The source is a live string, and the offsets are in its bounds.
    unsafe fn bytes(&self) -> &[u8] {
        // SAFETY: the caller guarantees the string and the offsets.
        unsafe { &text::bytes(&self.source)[self.start..self.end] }
    }

    /// The viewed element `i`, lent through `loan`, of a view of a list.
    ///
    /// # Safety
    ///
    /// The source is a live list, the offsets are in its bounds, and `i < self.len()`.
    unsafe fn lend(self, i: usize, loan: &mut Loan) -> u64 {
        // SAFETY: the caller guarantees the list and the index.
        unsafe { list::lend(self.source as *mut Header, self.start + i, loan) }
    }
}

/// `a == b` on the views `a_source[a_start..a_end]` and `b_source[b_start..b_end]`: the same
/// length, then each pair in turn, until one differs, through `eq`, the elements' `Eq`
/// dictionary, for views of lists, which a view of a string has no use for.
///
/// # Safety
///
/// Both sources are live strings, or live lists whose elements `eq` is the `Eq` of, and the
/// offsets are in their bounds.
#[unsafe(no_mangle)]
#[allow(clippy::too_many_arguments)]
pub(crate) unsafe extern "C" fn stilt_rt_view_eq(
    loc: u64,
    eq: u64,
    a_source: u64,
    a_start: u64,
    a_end: u64,
    b_source: u64,
    b_start: u64,
    b_end: u64,
) -> u64 {
    let (a, b) = (
        Window::new(a_source, a_start, a_end),
        Window::new(b_source, b_start, b_end),
    );
    // SAFETY: the caller guarantees the sources, the offsets and the dictionary.
    unsafe {
        if is_str(a.source) {
            return u64::from(a.bytes() == b.bytes());
        }
        let (mut left, mut right) = (Loan::new(), Loan::new());
        u64::from(
            a.len() == b.len()
                && (0..a.len()).all(|i| {
                    let (x, y) = (a.lend(i, &mut left), b.lend(i, &mut right));
                    method2(loc, eq, EQ, x, y).value != 0
                }),
        )
    }
}

/// The order of two views, as for [`stilt_rt_view_eq`]: by bytes for views of strings, and
/// lexicographically through `ord`, the elements' `Ord` dictionary, for views of lists.
///
/// # Safety
///
/// As for [`stilt_rt_view_eq`], with `ord` the elements' `Ord`.
#[unsafe(no_mangle)]
#[allow(clippy::too_many_arguments)]
pub(crate) unsafe extern "C" fn stilt_rt_view_compare(
    loc: u64,
    ord: u64,
    a_source: u64,
    a_start: u64,
    a_end: u64,
    b_source: u64,
    b_start: u64,
    b_end: u64,
) -> u64 {
    let (a, b) = (
        Window::new(a_source, a_start, a_end),
        Window::new(b_source, b_start, b_end),
    );
    // SAFETY: the caller guarantees the sources, the offsets and the dictionary.
    unsafe {
        if is_str(a.source) {
            return ordering(a.bytes().cmp(b.bytes()));
        }
        let (mut left, mut right) = (Loan::new(), Loan::new());
        for i in 0..a.len().min(b.len()) {
            let (x, y) = (a.lend(i, &mut left), b.lend(i, &mut right));
            let order = method2(loc, ord, COMPARE, x, y).value;
            if order != EQUAL {
                return order;
            }
        }
        ordering(a.len().cmp(&b.len()))
    }
}

/// The hash of the view `source[start..end]`: each viewed byte of a string mixed in turn, and
/// for a list, its length, then each viewed element's hash through `hash`, the elements' `Hash`
/// dictionary.
///
/// # Safety
///
/// `source` is a live string, or a live list whose elements `hash` is the `Hash` of, and the
/// offsets are in its bounds.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_view_hash(
    loc: u64,
    hash: u64,
    source: u64,
    start: u64,
    end: u64,
) -> u64 {
    let w = Window::new(source, start, end);
    // SAFETY: the caller guarantees the source, the offsets and the dictionary.
    unsafe {
        if is_str(w.source) {
            return w.bytes().iter().fold(FNV, |h, &b| mix(h, u64::from(b)));
        }
        let mut loan = Loan::new();
        (0..w.len()).fold(mix(FNV, w.len() as u64), |h, i| {
            mix(h, method1(loc, hash, HASH, w.lend(i, &mut loan)).value)
        })
    }
}

/// The text of the view `source[start..end]`, as `Show` gives it, or with `nested`, as a part
/// of an enclosing value's text gives it: a view of a string shows the viewed text, quoted when
/// nested, and a view of a list shows its viewed elements, through `show`, the elements' `Show`
/// dictionary, between `[` and `]`.
///
/// # Safety
///
/// `source` is a live string, or a live list whose elements `show` is the `Show` of, and the
/// offsets are in its bounds, on UTF-8 boundaries for a string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_view_show(
    loc: u64,
    show: u64,
    source: u64,
    start: u64,
    end: u64,
    nested: u64,
) -> u64 {
    let w = Window::new(source, start, end);
    // SAFETY: the caller guarantees the source, the offsets and the dictionary.
    unsafe {
        if is_str(w.source) {
            let viewed = &text::text(&w.source)[w.start..w.end];
            return if nested == 0 {
                text::from(viewed)
            } else {
                text::from(&text::quote(viewed))
            };
        }
        let mut out = vec![b'['];
        let mut loan = Loan::new();
        for i in 0..w.len() {
            if i > 0 {
                out.extend_from_slice(b", ");
            }
            let x = w.lend(i, &mut loan);
            append_shown(&mut out, method1(loc, show, SHOW_NESTED, x).value);
        }
        out.push(b']');
        text::new(&out)
    }
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_rt_view_eq,
        stilt_rt_view_compare,
        stilt_rt_view_hash,
        stilt_rt_view_show,
    ]
}
