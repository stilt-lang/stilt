//! The consumers of iterators (views.consumers): each pulls every element it needs, in order, with
//! a state of its own, so that it starts from the first element (views.laziness), and calls its
//! callback as `List`'s methods call theirs (std.callbacks), so that an error the callback raises
//! passes through: the consumer releases what it holds and raises it again, an error of several
//! words having gone to the memory `err` points to. Each takes the witness of its element type,
//! then of its own type parameters, and dictionaries for its bounds.

use super::pull::pull;
use super::values::{boxed, give, owned, release};
use super::{shape, state_len};
use crate::abi::{NONE, Ret, call1, call2, call2_out, immediate};
use crate::list::{box_of, new, push_value};
use crate::shape::Shape;

/// A run of an iterator by a consumer: the iterator, and the state of its pulls.
pub(super) struct Run {
    loc: u64,
    it: u64,
    state: Vec<u64>,
}

impl Run {
    /// A run from the iterator's first element.
    ///
    /// # Safety
    ///
    /// `it` is a live iterator, which outlives the run.
    pub(super) unsafe fn new(loc: u64, it: u64) -> Self {
        // SAFETY: as the caller guarantees.
        let state = vec![0; unsafe { state_len(it) }];
        Self { loc, it, state }
    }

    /// The next element, owning its references.
    pub(super) fn next(&mut self) -> Option<u64> {
        // SAFETY: `new`'s caller guarantees the iterator, and the state is its own.
        unsafe { pull(self.loc, self.it, &mut self.state) }
    }

    /// The shape of the iterator's elements.
    pub(super) fn shape(&self) -> Shape {
        // SAFETY: as for `next`.
        unsafe { shape(self.it) }
    }
}

/// An `Option` of an element, as a native gives it: in the two words it returns, or with the
/// element's words in `out` when it has several, or `always`.
///
/// # Safety
///
/// `x` owns its references, and `out` points to room for its words.
pub(super) unsafe fn option(x: Option<u64>, shape: Shape, out: *mut u64, always: bool) -> Ret {
    let Some(x) = x else {
        return NONE;
    };
    // SAFETY: as the caller guarantees.
    let word = unsafe { give(x, shape, out, always) };
    if boxed(shape) || always {
        Ret::ok(immediate(1))
    } else {
        crate::abi::some(word)
    }
}

/// `it.collect()`: every element, in a list of elements of the shape `elements`.
///
/// # Safety
///
/// `it` is a live iterator.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_collect(
    loc: u64,
    elements: u64,
    it: u64,
) -> Ret {
    let list = new(0, Shape(elements));
    // SAFETY: as the caller guarantees; the list is new, and each element is owned.
    unsafe {
        let mut run = Run::new(loc, it);
        while let Some(x) = run.next() {
            push_value(list, x);
        }
    }
    Ret::ok(list as u64)
}

/// `it.count()`: the number of elements.
///
/// # Safety
///
/// `it` is a live iterator.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_count(loc: u64, _shape: u64, it: u64) -> Ret {
    // SAFETY: as the caller guarantees.
    let mut run = unsafe { Run::new(loc, it) };
    let mut n = 0u64;
    while let Some(x) = run.next() {
        // SAFETY: the element is owned.
        unsafe { release(x, run.shape()) };
        n += 1;
    }
    Ret::ok(n)
}

/// `f(acc, x)` as a value of its own of the shape `a`.
///
/// # Safety
///
/// `f` is a live closure that takes `acc` and `x` and gives values of the shape `a`, and `err`
/// as for [`call2`].
unsafe fn step(loc: u64, f: u64, (acc, x): (u64, u64), a: Shape, err: *mut u64) -> Ret {
    // SAFETY: as the caller guarantees.
    unsafe {
        if !boxed(a) {
            return call2(loc, f, acc, x, err);
        }
        let mut words = vec![0; a.words()];
        let given = call2_out(loc, f, (acc, x), words.as_mut_ptr(), err);
        if given.raised != 0 {
            return given;
        }
        Ret::ok(box_of(&words, a))
    }
}

/// `it.fold(init, f)`: `f` applied to `init` and each element in turn.
///
/// # Safety
///
/// `it` is a live iterator, `init` a value of the shape `a`, `f` a live closure from it and an
/// element to such a value, `out` room for the words of one, and `err` as for [`call2`].
#[unsafe(no_mangle)]
#[allow(clippy::too_many_arguments)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_fold(
    loc: u64,
    _shape: u64,
    a: u64,
    it: u64,
    init: u64,
    f: u64,
    out: u64,
    err: u64,
) -> Ret {
    let out = out as usize as *mut u64;
    let err = err as usize as *mut u64;
    let a = Shape(a);
    // SAFETY: as the caller guarantees; the accumulator and each element are owned, and each is
    // released once `f` has read it.
    unsafe {
        let mut run = Run::new(loc, it);
        let mut acc = owned(init, a);
        while let Some(x) = run.next() {
            let given = step(loc, f, (acc, x), a, err);
            release(x, run.shape());
            release(acc, a);
            if given.raised != 0 {
                return given;
            }
            acc = given.value;
        }
        Ret::ok(give(acc, a, out, false))
    }
}

/// The first element that `p` gives `want` for, or the error it raises, with `None` when every
/// element has been asked.
///
/// # Safety
///
/// `it` is a live iterator, `p` a live closure from its elements to `bool`, and `err` as for
/// [`call1`].
unsafe fn search(loc: u64, it: u64, p: u64, want: bool, err: *mut u64) -> Result<Option<u64>, Ret> {
    // SAFETY: as the caller guarantees; each element is owned.
    unsafe {
        let mut run = Run::new(loc, it);
        while let Some(x) = run.next() {
            let given = call1(loc, p, x, err);
            if given.raised != 0 {
                release(x, run.shape());
                return Err(given);
            }
            if (given.value != 0) == want {
                return Ok(Some(x));
            }
            release(x, run.shape());
        }
        Ok(None)
    }
}

/// `it.any(p)` if `want`, and otherwise `it.all(p)`, which stop at the first element that
/// decides them.
///
/// # Safety
///
/// As for [`search`].
unsafe fn decide(loc: u64, it: u64, p: u64, want: bool, err: *mut u64) -> Ret {
    // SAFETY: as the caller guarantees.
    unsafe {
        match search(loc, it, p, want, err) {
            Err(raised) => raised,
            Ok(Some(x)) => {
                release(x, shape(it));
                Ret::ok(u64::from(want))
            }
            Ok(None) => Ret::ok(u64::from(!want)),
        }
    }
}

/// `it.any(p)`: whether `p` accepts some element.
///
/// # Safety
///
/// As for [`search`].
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_any(
    loc: u64,
    _shape: u64,
    it: u64,
    p: u64,
    err: u64,
) -> Ret {
    let err = err as usize as *mut u64;
    // SAFETY: as the caller guarantees.
    unsafe { decide(loc, it, p, true, err) }
}

/// `it.all(p)`: whether `p` accepts every element.
///
/// # Safety
///
/// As for [`search`].
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_all(
    loc: u64,
    _shape: u64,
    it: u64,
    p: u64,
    err: u64,
) -> Ret {
    let err = err as usize as *mut u64;
    // SAFETY: as the caller guarantees.
    unsafe { decide(loc, it, p, false, err) }
}

/// `it.find(p)`: the first element that `p` accepts. A native that can raise gives an `Option`
/// of a type parameter's value with its words in `out`, however many it has, since it returns
/// one word of its result beside the raised flag (`stilt_mir`'s natives).
///
/// # Safety
///
/// As for [`search`], and `out` points to room for the words of an element.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_view_Iter_find(
    loc: u64,
    _shape: u64,
    it: u64,
    p: u64,
    out: u64,
    err: u64,
) -> Ret {
    let out = out as usize as *mut u64;
    let err = err as usize as *mut u64;
    // SAFETY: as the caller guarantees.
    unsafe {
        match search(loc, it, p, true, err) {
            Err(raised) => raised,
            Ok(x) => option(x, shape(it), out, true),
        }
    }
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_std_view_Iter_collect,
        stilt_std_view_Iter_count,
        stilt_std_view_Iter_fold,
        stilt_std_view_Iter_any,
        stilt_std_view_Iter_all,
        stilt_std_view_Iter_find,
    ]
}
