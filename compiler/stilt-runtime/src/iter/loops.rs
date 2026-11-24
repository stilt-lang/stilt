//! `for p in it` over an iterator (views.for-over-view), which pulls its elements one at a time as
//! the loop's body asks for them, as a consumer does (views.laziness). The loop keeps the state of
//! its pulls in a data object of its own, which compiled code makes with [`stilt_rt_iter_state`]
//! and releases as it releases any value: [`stilt_rt_iter_next`] pulls an element into the object,
//! and [`stilt_rt_iter_take`] gives it to the body.

use super::pull::pull;
use super::state_len;
use crate::object::{Header, alloc_data, data_field};

/// The fields of a loop's state before those of the pulls: whether an element waits, and the
/// element.
const WAITING: usize = 0;
const ELEMENT: usize = 1;
const PULLS: usize = 2;

/// The state of a loop over `it` from its first element: every field a scalar 0.
///
/// # Safety
///
/// `it` is a live iterator.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_iter_state(it: u64) -> u64 {
    // SAFETY: as the caller guarantees.
    let len = PULLS + unsafe { state_len(it) };
    let object = alloc_data(len, 0);
    for i in 0..len {
        // SAFETY: the object has `len` fields, which start unset.
        unsafe { *data_field(object, i) = 0 };
    }
    object as u64
}

/// Pulls the next element of `it` into the loop's state, and tells whether there was one.
///
/// # Safety
///
/// `it` is a live iterator and `state` the state that [`stilt_rt_iter_state`] made for it,
/// whose waiting element the loop took.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_iter_next(loc: u64, it: u64, state: u64) -> u64 {
    let object = state as *mut Header;
    // SAFETY: as the caller guarantees; the pulls' state follows the first fields.
    unsafe {
        let len = crate::object::data_len(object);
        let pulls = std::slice::from_raw_parts_mut(data_field(object, PULLS), len - PULLS);
        match pull(loc, it, pulls) {
            Some(x) => {
                *data_field(object, ELEMENT) = x;
                *data_field(object, WAITING) = 1;
                1
            }
            None => 0,
        }
    }
}

/// The element that [`stilt_rt_iter_next`] pulled, which the loop now owns.
///
/// # Safety
///
/// `state` is a loop's state with an element waiting.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_iter_take(state: u64) -> u64 {
    let object = state as *mut Header;
    // SAFETY: as the caller guarantees.
    unsafe {
        *data_field(object, WAITING) = 0;
        std::mem::take(&mut *data_field(object, ELEMENT))
    }
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![stilt_rt_iter_state, stilt_rt_iter_next, stilt_rt_iter_take]
}
