//! The lazy values of `std.lazy` (polymorphism.lazy-values and polymorphism.lazy-implicit-effects).
//! A `Lazy<T>` is a data object, which every copy of the value shares: the closure that computes
//! the value, until it runs, then the value, in the one word that holds it where a type parameter
//! stands, its box for a value of several words, and whether it is computed. The closure performs
//! no effect, so computing the value on the first `get`, on any copy, is something no program can
//! observe.
//!
//! A lazy value that threads share (`crate::object::share`) is computed once, by the first
//! thread that claims it, while the others wait; its value is marked shared before they read
//! it. A computation waits for nothing: a `when` that runs while one runs, on its thread or on a
//! worker of a call of `std.par` it makes, panics with `deadlock`
//! (polymorphism.lazy-waits-for-nothing), so no closure reaches the lazy value it computes, which
//! only a shared value could hold.

use std::cell::Cell;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Condvar, Mutex, PoisonError};

use crate::abi::{Ret, address};
use crate::list::box_of;
use crate::map::{dup_words, words_of};
use crate::object::{Header, alloc_data, data_field, dup, is_shared, set_masks, share};
use crate::shape::Shape;

/// The fields of a lazy value.
const CLOSURE: usize = 0;
const VALUE: usize = 1;
const COMPUTED: usize = 2;
const FIELDS: usize = 3;

/// The states of a shared lazy value's field [`COMPUTED`]: not computed, computed, and claimed
/// by a thread that computes it.
const WAITING: u64 = 0;
const DONE: u64 = 1;
const CLAIMED: u64 = 2;

thread_local! {
    /// How many lazy values the current thread computes, one inside another's computation.
    static DEPTH: Cell<u32> = const { Cell::new(0) };
}

/// Whether the current thread runs the computation of a lazy value.
pub(crate) fn computing() -> bool {
    DEPTH.get() > 0
}

/// Runs `f` as part of the computation of a lazy value when `lazy` is set, as a worker runs a
/// part of a call of `std.par` that a computation made.
pub(crate) fn computing_as(lazy: bool, f: impl FnOnce()) {
    let depth = u32::from(lazy);
    DEPTH.set(DEPTH.get() + depth);
    f();
    DEPTH.set(DEPTH.get() - depth);
}

/// Where threads wait for a shared lazy value that another computes.
static COMPUTING: Mutex<()> = Mutex::new(());
static COMPUTED_ONE: Condvar = Condvar::new();

// Compiled code takes every argument as a word, an address among them (`crate::abi`).
type Code0 = unsafe extern "C" fn(u64, u64, u64) -> Ret;
type Code0Out = unsafe extern "C" fn(u64, u64, u64, u64) -> Ret;

/// `Lazy.new(f)`: a lazy value whose value is `f()`, which it keeps a reference to until it
/// runs.
///
/// # Safety
///
/// `f` is a live closure of no parameters.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_lazy_Lazy_new(_loc: u64, _shape: u64, f: u64) -> Ret {
    let object = alloc_data(FIELDS, 0);
    // SAFETY: the object was just allocated with `FIELDS` fields, and `f` is a live closure,
    // which gets a reference of its own.
    unsafe {
        *data_field(object, CLOSURE) = f;
        *data_field(object, VALUE) = 0;
        *data_field(object, COMPUTED) = 0;
        dup(f);
        set_masks(object, |_| 1 << CLOSURE);
    }
    Ret::ok(object as u64)
}

/// The value of `f()`, owned, in the one word that holds it where a type parameter stands: a
/// closure that a native calls gives a value of several words in the memory it is passed.
///
/// # Safety
///
/// `f` is a live closure of no parameters, which gives a value of shape `shape` and raises
/// nothing.
pub(crate) unsafe fn compute(loc: u64, f: u64, shape: Shape) -> u64 {
    // SAFETY: a closure's field 0 holds the address of its code's slot, which holds the
    // address of the code, which takes the closure, `out` for a result of several words, and
    // the memory for an error, which an empty row never raises.
    unsafe {
        let code = *(*data_field(f as *mut Header, 0) as *const u64) as *const ();
        // A panic ends the thread, which never counts again, so the count needs no guard.
        DEPTH.set(DEPTH.get() + 1);
        let value = if shape.words() > 1 {
            let mut words = vec![0u64; shape.words()];
            let call: Code0Out = std::mem::transmute(code);
            call(loc, f, address(words.as_mut_ptr()), 0);
            box_of(&words, shape)
        } else {
            let call: Code0 = std::mem::transmute(code);
            call(loc, f, 0).value
        };
        DEPTH.set(DEPTH.get() - 1);
        value
    }
}

/// `l.get()`: the value, computed by the first call on `l` or any copy of it, which then lets
/// its closure go. A value of several words goes to `out`, with references of its own.
///
/// # Safety
///
/// `l` is a live lazy value of the shape `shape`, and `out` points to room for the words of a
/// value of several words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_lazy_Lazy_get(
    loc: u64,
    shape: u64,
    l: u64,
    out: u64,
) -> Ret {
    let out = out as usize as *mut u64;
    let shape = Shape(shape);
    let object = l as *mut Header;
    // SAFETY: the caller guarantees the lazy value, whose fields are as `Lazy.new` made them,
    // and the room for a value of several words.
    unsafe {
        if is_shared(object) {
            computed_shared(loc, object, shape);
        } else if *data_field(object, COMPUTED) == WAITING {
            settle(
                object,
                compute(loc, *data_field(object, CLOSURE), shape),
                shape,
            );
            *data_field(object, COMPUTED) = DONE;
        }
        let value = *data_field(object, VALUE);
        if shape.words() > 1 {
            let words = words_of(&value, shape);
            dup_words(words, shape);
            std::ptr::copy_nonoverlapping(words.as_ptr(), out, words.len());
            return Ret::ok(0);
        }
        if shape.heap() {
            dup(value);
        }
        Ret::ok(value)
    }
}

/// Keeps a lazy value's computed value, which it takes, and lets its closure go.
///
/// # Safety
///
/// `object` is a live lazy value that isn't computed, which only the current thread writes,
/// and `value` a live value of the shape.
unsafe fn settle(object: *mut Header, value: u64, shape: Shape) {
    // SAFETY: as the caller guarantees.
    unsafe {
        let f = *data_field(object, CLOSURE);
        *data_field(object, VALUE) = value;
        *data_field(object, CLOSURE) = 0;
        let heap = shape.heap() || shape.words() > 1;
        set_masks(object, |_| u64::from(heap) << VALUE);
        crate::object::drop(f);
    }
}

/// Computes a lazy value that threads share, unless one has: the first thread to claim it
/// computes it, marks its value shared and says it is computed, while the others wait.
///
/// # Safety
///
/// `object` is a live lazy value marked shared, of values of the shape.
unsafe fn computed_shared(loc: u64, object: *mut Header, shape: Shape) {
    // SAFETY: the field is a word that, once the value is shared, only atomic instructions
    // change.
    let state = unsafe { AtomicU64::from_ptr(data_field(object, COMPUTED)) };
    match state.compare_exchange(WAITING, CLAIMED, Ordering::Acquire, Ordering::Acquire) {
        Ok(_) => {
            // SAFETY: the claim makes this thread the only one that writes the fields until it
            // says the value is computed; what it reaches is marked before others read it.
            unsafe {
                let value = compute(loc, *data_field(object, CLOSURE), shape);
                share(value, shape);
                settle(object, value, shape);
            }
            let _held = COMPUTING.lock().unwrap_or_else(PoisonError::into_inner);
            state.store(DONE, Ordering::Release);
            COMPUTED_ONE.notify_all();
        }
        Err(DONE) => {}
        Err(_) => {
            let mut held = COMPUTING.lock().unwrap_or_else(PoisonError::into_inner);
            while state.load(Ordering::Acquire) != DONE {
                held = COMPUTED_ONE
                    .wait(held)
                    .unwrap_or_else(PoisonError::into_inner);
            }
        }
    }
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![stilt_std_lazy_Lazy_new, stilt_std_lazy_Lazy_get]
}
