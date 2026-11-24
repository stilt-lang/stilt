//! The values that `when`s hold (shared.when-order;
//! shared.when-on-value-already-held).
//!
//! Each thread knows the handles that its running `when`s hold, those of the code it runs
//! where it starts included, as a task started inside a `when`'s block is: a `when` that names
//! one of them panics with `deadlock` before it holds anything. Under `task.threads()`, a
//! `when` then waits until no segment before its point in the sequential order blocks it (a
//! task that hasn't ended and holds handles, or may raise, `super::segments`), and until no
//! other thread holds one of its values, and holds them all at once. The blocks of one value
//! so run in the sequential order, and none runs in code that a raise before it cancels. A held
//! handle is marked so, and the collection of cycles doesn't look into its value, whose place
//! the block may be writing (`crate::object`'s `cycles`).

use std::cell::RefCell;
use std::thread;

thread_local! {
    /// The handles that the running `when`s of the current thread hold.
    static HELD: RefCell<Vec<u64>> = const { RefCell::new(Vec::new()) };
    /// The handles that the `when` being entered names.
    static NAMED: RefCell<Vec<u64>> = const { RefCell::new(Vec::new()) };
}

/// Whether a `when` of the current thread holds a value.
pub(crate) fn holding() -> bool {
    HELD.with_borrow(|held| !held.is_empty())
}

/// A name of the `when` at `loc` that is being entered, whose handle is `handle`: the `when`
/// panics if one around it holds the value, or if it runs while a lazy value is computed.
///
/// # Safety
///
/// `handle` is a live shared value.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_when_name(loc: u64, handle: u64) {
    // polymorphism.lazy-waits-for-nothing: a lazy value's computation waits for nothing.
    if crate::std_lazy::computing() {
        NAMED.with_borrow_mut(Vec::clear);
        let detail = "this `when` runs while a `Lazy` computes its value, which waits for nothing";
        crate::panic::panic(loc, crate::panic::DEADLOCK, detail);
    }
    if HELD.with_borrow(|held| held.contains(&handle)) {
        NAMED.with_borrow_mut(Vec::clear);
        crate::panic::panic(loc, crate::panic::DEADLOCK, "");
    }
    NAMED.with_borrow_mut(|named| named.push(handle));
}

/// Holds the values that the `when` being entered names, once it is its turn.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_when_hold() {
    let named = NAMED.take();
    if let Some(here) = super::here() {
        let me = thread::current().id();
        let mut tree = here.run.lock();
        loop {
            if tree.closed(here.seg) {
                drop(tree);
                super::abandon();
            }
            let taken = named
                .iter()
                .any(|h| tree.held.iter().any(|&(x, t)| x == *h && t != me));
            if !taken && !tree.blocked(here.seg) {
                break;
            }
            tree = here.run.wait(tree);
        }
        tree.held.extend(named.iter().map(|&h| (h, me)));
    }
    for &handle in &named {
        // SAFETY: a `when` names live shared values.
        unsafe { crate::object::hold(handle) };
    }
    HELD.with_borrow_mut(|held| held.extend(named));
}

/// The end of a `when`'s hold on the value `handle` reaches.
pub(crate) fn release(handle: u64) {
    let still = HELD.with_borrow_mut(|held| {
        if let Some(i) = held.iter().rposition(|&h| h == handle) {
            held.remove(i);
        }
        held.contains(&handle)
    });
    if !still {
        // SAFETY: the `when` that lets the handle go names a live shared value.
        unsafe { crate::object::unhold(handle) };
    }
    if let Some(here) = super::here() {
        let me = thread::current().id();
        let mut tree = here.run.lock();
        if let Some(i) = tree.held.iter().rposition(|&(h, t)| h == handle && t == me) {
            tree.held.remove(i);
        }
        drop(tree);
        here.run.changed();
    }
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![stilt_rt_when_name, stilt_rt_when_hold]
}
