//! The shared values of `std.sync` (shared.std-sync, shared.when-order). A
//! `Shared<T>` is a data object of the words of its value, which every copy of the handle reaches:
//! no write makes it unique, so that it keeps one identity (values.shared). A `when` reads and
//! writes those words in place, through a pointer to them, so two names whose handles reach one
//! value are one place.
//!
//! A `when` names its handles, then holds their values (`crate::tasks`'s `order`): under
//! `task.threads()` it waits for its turn in the sequential order, so the blocks of one value run
//! one at a time in that order (shared.when-order). A shared value is marked shared, with
//! everything it reaches, so that its counts change by atomic instructions (Values and costs,
//! "Counts that are atomic only when shared"), and so is what a `when` leaves in it. A handle that
//! a value it reaches holds is a cycle, which the collection of cycles frees once nothing else
//! reaches it (cycles.freeing), at the points where every count is the program's: when a handle is
//! made, and when a `when` lets one go.

use crate::abi::Ret;
use crate::list::box_of;
use crate::map::{dup_words, words_of};
use crate::object::{HANDLE, Header, data_field, share};
use crate::shape::Shape;

/// `Shared.new(value)`: a shared value holding a copy of `value`'s words, with references of
/// their own, marked shared with everything they reach.
///
/// # Safety
///
/// `value` is a live value of the shape `shape`, a box of its words if it has several, which
/// the caller lends.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_sync_Shared_new(
    _loc: u64,
    shape: u64,
    value: u64,
) -> Ret {
    let shape = Shape(shape);
    // SAFETY: as the caller guarantees.
    unsafe {
        let words = words_of(&value, shape);
        dup_words(words, shape);
        let handle = box_of(words, shape);
        (*(handle as *mut Header)).tag = HANDLE;
        share(handle, Shape::word(true));
        crate::object::tick();
        Ret::ok(handle)
    }
}

/// A pointer to the words of the value a shared value holds, which a `when` reads and writes in
/// place.
///
/// # Safety
///
/// `handle` is a live shared value, which outlives the pointer's uses.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_shared_place(handle: u64) -> u64 {
    // SAFETY: as the caller guarantees: a shared value is a data object of its value's words.
    unsafe { data_field(handle as *mut Header, 0) as u64 }
}

/// The end of a `when`'s hold on the value a handle reaches, however its block ends, which marks
/// what the block left in the value shared and lets the next `when` on it hold it.
///
/// # Safety
///
/// `handle` is a live shared value.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_shared_leave(handle: u64) {
    // SAFETY: as the caller guarantees: a shared value is a data object of its value's words,
    // whose heap words its masks tell, and which only this block reaches meanwhile.
    unsafe {
        crate::object::share_held(handle as *mut Header);
    }
    crate::tasks::release(handle);
    crate::object::tick();
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_std_sync_Shared_new,
        stilt_rt_shared_place,
        stilt_rt_shared_leave,
    ]
}
