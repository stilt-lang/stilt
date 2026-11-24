//! The constants of a program (declarations.constant-evaluation and
//! declarations.constant-expressions). Each is computed when the program first uses it, by the code
//! the compiler gives it, into a cell of words: its state, then its value's words. Several threads
//! may first use it at once, as the parts of a call of `std.par` do: one claims it and computes it
//! while the others wait. Every thread may read its value, so the value is marked shared
//! (`crate::object::share`) before its cell says it is computed, by a store that releases the
//! words, which compiled code reads with a load that acquires them.
//!
//! A thread that ends the program while it computes a constant, as one whose initializer panics
//! does (declarations.constant-evaluation), gives its claim back, so that a thread that runs a part
//! of a call before its own computes it in turn, and panics, if it does, in the order of the
//! sequential run (par.panics).

use std::cell::RefCell;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Condvar, Mutex, PoisonError};

use crate::shape::Shape;

/// The states of a constant's cell: not computed, computed, and claimed by a thread that
/// computes it.
const WAITING: u64 = 0;
const DONE: u64 = 1;
const CLAIMED: u64 = 2;

/// Where threads wait for a constant that another computes.
static LOCK: Mutex<()> = Mutex::new(());
static CHANGED: Condvar = Condvar::new();

thread_local! {
    /// The cells of the constants that the current thread computes.
    static CLAIMS: RefCell<Vec<usize>> = const { RefCell::new(Vec::new()) };
}

/// The state of a constant's cell.
///
/// # Safety
///
/// `cell` is a constant's cell, which lives as long as the program.
unsafe fn state<'a>(cell: *mut u64) -> &'a AtomicU64 {
    // SAFETY: as the caller guarantees: the state is a word aligned to 8, which only atomic
    // instructions change.
    unsafe { AtomicU64::from_ptr(cell) }
}

/// Sets a cell's state, and wakes the threads that wait for it.
///
/// # Safety
///
/// As for [`state`].
unsafe fn set(cell: *mut u64, to: u64) {
    // SAFETY: as the caller guarantees.
    unsafe { state(cell) }.store(to, Ordering::Release);
    let _held = LOCK.lock().unwrap_or_else(PoisonError::into_inner);
    CHANGED.notify_all();
}

/// Claims a constant that its cell doesn't say is computed: 1 when the current thread is to
/// compute it, and 0 when another has, once it has.
///
/// # Safety
///
/// `cell` is a constant's cell, which lives as long as the program.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_constant_claim(cell: u64) -> u64 {
    let cell = cell as usize as *mut u64;
    // SAFETY: as the caller guarantees.
    let state = unsafe { state(cell) };
    loop {
        match state.compare_exchange(WAITING, CLAIMED, Ordering::Acquire, Ordering::Acquire) {
            Ok(_) => {
                CLAIMS.with_borrow_mut(|claims| claims.push(cell as usize));
                return 1;
            }
            Err(DONE) => return 0,
            Err(_) => {
                let mut held = LOCK.lock().unwrap_or_else(PoisonError::into_inner);
                while state.load(Ordering::Acquire) == CLAIMED {
                    held = CHANGED.wait(held).unwrap_or_else(PoisonError::into_inner);
                }
            }
        }
    }
}

/// Marks what a heap word of a constant's value reaches shared.
///
/// # Safety
///
/// `word` is a live heap word of a constant's value, which only the current thread reaches.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_constant_share(word: u64) {
    // SAFETY: as the caller guarantees.
    unsafe { crate::object::share(word, Shape::word(true)) }
}

/// Says that the constant the current thread claimed is computed, its words written.
///
/// # Safety
///
/// `cell` is a constant's cell, which the current thread claimed.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_constant_done(cell: u64) {
    let cell = cell as usize as *mut u64;
    CLAIMS.with_borrow_mut(|claims| claims.retain(|&claimed| claimed != cell as usize));
    // SAFETY: as the caller guarantees.
    unsafe { set(cell, DONE) }
}

/// Gives back the constants that the current thread claimed, as it ends the program.
pub(crate) fn abandon() {
    for cell in CLAIMS.with_borrow_mut(std::mem::take) {
        // SAFETY: the thread claimed each cell, which lives as long as the program.
        unsafe { set(cell as *mut u64, WAITING) }
    }
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_rt_constant_claim,
        stilt_rt_constant_share,
        stilt_rt_constant_done,
    ]
}

#[cfg(test)]
mod tests {
    use super::{CLAIMED, DONE, abandon, stilt_rt_constant_claim, stilt_rt_constant_done};

    #[test]
    fn one_thread_computes_a_constant_and_the_others_wait_for_it() {
        let cell = Box::leak(Box::new([0u64; 2])).as_mut_ptr() as usize;
        let threads: Vec<_> = (0..8)
            .map(|_| {
                std::thread::spawn(move || {
                    let cell = cell as *mut u64;
                    // SAFETY: the cell lives as long as the process.
                    unsafe {
                        if stilt_rt_constant_claim(cell as usize as u64) == 1 {
                            std::thread::sleep(std::time::Duration::from_millis(10));
                            *cell.add(1) += 1;
                            stilt_rt_constant_done(cell as usize as u64);
                        }
                        *cell.add(1)
                    }
                })
            })
            .collect();
        for thread in threads {
            assert_eq!(thread.join().expect("the thread ends"), 1);
        }
    }

    #[test]
    fn a_claim_given_back_is_claimed_again() {
        let cell = Box::leak(Box::new([0u64; 2])).as_mut_ptr();
        // SAFETY: the cell lives as long as the process.
        unsafe {
            assert_eq!(stilt_rt_constant_claim(cell as usize as u64), 1);
            assert_eq!(*cell, CLAIMED);
            abandon();
            assert_eq!(stilt_rt_constant_claim(cell as usize as u64), 1);
            stilt_rt_constant_done(cell as usize as u64);
            assert_eq!(*cell, DONE);
            assert_eq!(stilt_rt_constant_claim(cell as usize as u64), 0);
        }
    }
}
