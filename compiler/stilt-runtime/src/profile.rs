//! The counts of a profiled run (builds.profiles): how often each body is entered, each arm of
//! an `if` or a `match` taken and each loop's body run, by the place in the program that the
//! code compiled for `stilt run --profile` and `stilt test --profile` names, and how often
//! each call through a function value or a dictionary reaches each function, by the call's
//! place and the function's address. Only a profiled run's code calls these, so a debug run
//! without `--profile` counts nothing (goal debug-speed); every thread of the run adds to the
//! same counts.

use std::collections::HashMap;
use std::sync::{Mutex, PoisonError};

/// A count of a function's entries.
pub const ENTRY: u64 = 0;
/// A count of the times an arm is taken.
pub const ARM: u64 = 1;
/// A count of the runs of a loop's body.
pub const LOOP: u64 = 2;
/// A count of the calls through a function value or a dictionary, by the function reached.
pub const CALL: u64 = 3;

/// A place that a profiled run counts: what it counts, the location word of its place, and for
/// a call, the address of the function reached.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Counted {
    /// [`ENTRY`], [`ARM`], [`LOOP`] or [`CALL`].
    pub kind: u64,
    /// The location word of the place.
    pub at: u64,
    /// For a call, the function reached.
    pub callee: Option<String>,
}

/// The counts of the run so far.
static COUNTS: Mutex<Option<HashMap<Counted, u64>>> = Mutex::new(None);

fn add(counted: Counted) {
    let mut counts = COUNTS.lock().unwrap_or_else(PoisonError::into_inner);
    *counts
        .get_or_insert_with(HashMap::new)
        .entry(counted)
        .or_insert(0) += 1;
}

/// Counts an entry, an arm or a loop's body at the place `at`.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_profile_count(kind: u64, at: u64) {
    add(Counted {
        kind,
        at,
        callee: None,
    });
}

/// Counts a call through a function value or a dictionary, at the place `at`, that reaches the
/// function whose address the string `callee` holds.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_profile_call(at: u64, callee: u64) {
    // SAFETY: compiled code passes a static string, which lives as long as the program.
    let callee = unsafe { crate::text::text(&callee) }.to_owned();
    add(Counted {
        kind: CALL,
        at,
        callee: Some(callee),
    });
}

/// The counts of the run so far, which it then forgets.
#[must_use]
pub fn take() -> Vec<(Counted, u64)> {
    let mut counts = COUNTS.lock().unwrap_or_else(PoisonError::into_inner);
    let mut all: Vec<(Counted, u64)> = counts.take().unwrap_or_default().into_iter().collect();
    all.sort();
    all
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![stilt_rt_profile_count, stilt_rt_profile_call]
}

#[cfg(test)]
mod tests {
    #[test]
    fn counts_add_up_and_are_taken_once() {
        for _ in 0..3 {
            super::stilt_rt_profile_count(super::LOOP, 7);
        }
        super::stilt_rt_profile_count(super::ENTRY, 7);
        let taken = super::take();
        let loops = taken
            .iter()
            .find(|(c, _)| c.kind == super::LOOP && c.at == 7);
        assert_eq!(loops.map(|(_, n)| *n), Some(3));
        assert_eq!(super::take().len(), 0);
    }
}
