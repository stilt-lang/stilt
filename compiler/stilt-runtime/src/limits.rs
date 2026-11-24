//! The check of `without alloc` in debug builds (facts.without-alloc): code that a `without alloc`
//! limits holds no operation that allocates, its own or one it inherits, so no allocation may
//! happen while it runs but in code that the limit doesn't cover, which a call through a function
//! value reaches (facts.calls-through-function-values). Compiled code counts, on each thread, the
//! frames of limited functions it is in, and every function that allocates sets the count to 0
//! while it runs. Every allocation of the heap's memory reads the count, and one made while it
//! isn't 0 ends the program: the facts said the code doesn't allocate, and it did.

use std::cell::Cell;

thread_local! {
    /// The frames of functions limited by `without alloc` that the thread is in, and that no
    /// function that allocates has entered since.
    static DEPTH: Cell<u32> = const { Cell::new(0) };
}

/// The entry of a function that `without alloc` limits.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_alloc_limit_enter() {
    DEPTH.with(|d| d.set(d.get().saturating_add(1)));
}

/// The return of a function that `without alloc` limits.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_alloc_limit_leave() {
    DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
}

/// The entry of a function that allocates, which the limits around it don't cover: the count it
/// found, which its return puts back.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_alloc_limit_suspend() -> u64 {
    u64::from(DEPTH.with(|d| d.replace(0)))
}

/// The return of a function that allocates: the count its entry found.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_alloc_limit_resume(depth: u64) {
    DEPTH.with(|d| d.set(u32::try_from(depth).unwrap_or(u32::MAX)));
}

/// Sets the count to 0 for code that ends the program, such as a panic's report, which may
/// allocate wherever it is reached.
pub(crate) fn lift() {
    DEPTH.with(|d| d.set(0));
}

/// Ends the program when memory is allocated while a function that `without alloc` limits runs.
#[inline]
pub(crate) fn allocating() {
    if DEPTH.with(Cell::get) != 0 {
        refused();
    }
}

#[cold]
#[inline(never)]
fn refused() {
    lift();
    crate::entry::fatal(
        "bug: code limited by `without alloc` allocated, which its facts say it can't",
    );
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_rt_alloc_limit_enter,
        stilt_rt_alloc_limit_leave,
        stilt_rt_alloc_limit_suspend,
        stilt_rt_alloc_limit_resume,
    ]
}
