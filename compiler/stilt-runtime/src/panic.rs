//! Panics, and the locations they are reported at (program.panic-location).
//!
//! A location is one word: a file's index among the program's files, a line and a column,
//! each counted from 1. The compiler computes it where it compiles the operation, and registers
//! the paths of the files when the program starts.

use std::io::Write;
use std::sync::{PoisonError, RwLock};

use crate::{io, text};

/// The kinds of panic of effects.panic-kinds, by the numbers the compiler passes.
const KINDS: [&str; 13] = [
    "overflow",
    "divide-by-zero",
    "bounds",
    "missing-key",
    "utf8-boundary",
    "unreachable",
    "assert",
    "explicit",
    "hole",
    "check-error",
    "deadlock",
    "unwrap",
    "nul-in-string",
];

/// The detail of each kind of panic that the compiler's own code raises, without one of its
/// own. program.panic-detail leaves its wording to the implementation.
const DETAILS: [&str; 13] = [
    "the result is out of range",
    "division by zero",
    "the index is out of bounds",
    "the key isn't in the map, which has no default",
    "the range splits a UTF-8 sequence",
    "reached unreachable()",
    "the assertion is false",
    "",
    "reached a hole",
    "the code has an error",
    "this `when` waits for a value that a `when` around it holds",
    "",
    "",
];

pub(crate) const OVERFLOW: u64 = 0;
pub(crate) const DIVIDE_BY_ZERO: u64 = 1;
pub(crate) const BOUNDS: u64 = 2;
pub(crate) const MISSING_KEY: u64 = 3;
pub(crate) const UTF8_BOUNDARY: u64 = 4;
pub(crate) const UNREACHABLE: u64 = 5;
pub(crate) const EXPLICIT: u64 = 7;
pub(crate) const DEADLOCK: u64 = 10;
pub(crate) const UNWRAP: u64 = 11;
pub(crate) const NUL_IN_STRING: u64 = 12;

static FILES: RwLock<Vec<String>> = RwLock::new(Vec::new());

/// Registers the paths of the program's files, by index, as program.report-paths reports them.
pub(crate) fn set_files(files: Vec<String>) {
    *FILES.write().unwrap_or_else(PoisonError::into_inner) = files;
}

/// The location of line `line`, column `col` of file `file`.
#[must_use]
pub const fn location(file: u32, line: u32, col: u32) -> u64 {
    (file as u64) << 44 | ((line as u64) & 0xff_ffff) << 20 | (col as u64) & 0xf_ffff
}

/// The three highest bits of a location word, which mark what a release build may drop of its
/// operation, as `stilt_mir::mir`'s `PROVED_CHECK`, `PROVED_OVERFLOW` and `UNIQUE_LIST` give
/// them: the checks that verification proves (facts.verification), and a list's count that the
/// compiler's facts prove. They name no place.
const MARKS: u64 = 7 << 61;

/// The path, line and column of a location, or `None` for one in no file of the program, as
/// an input of the REPL is (repl.running-inputs).
fn place(loc: u64) -> Option<(String, u64, u64)> {
    let loc = loc & !MARKS;
    let file = usize::try_from(loc >> 44).unwrap_or(usize::MAX);
    let path = FILES
        .read()
        .unwrap_or_else(PoisonError::into_inner)
        .get(file)
        .cloned()?;
    Some((path, loc >> 20 & 0xff_ffff, loc & 0xf_ffff))
}

/// Ends the program with a panic of kind `kind` at `loc` (program.panic-report): writes what it
/// printed, then the report, and ends with status 101. A task panics in its turn, where the
/// sequential run does, and never in code that the sequential run doesn't reach
/// (tasks.same-output-under-every-handler).
pub(crate) fn panic(loc: u64, kind: u64, detail: &str) -> ! {
    // The report may allocate wherever the panic is.
    crate::limits::lift();
    crate::workers::end(|| crate::workers::Ending::Panic {
        loc,
        kind,
        detail: detail.to_owned(),
    });
    crate::tasks::turn();
    io::flush();
    let index = usize::try_from(kind).unwrap_or(0).min(KINDS.len() - 1);
    let detail = if detail.is_empty() {
        DETAILS[index]
    } else {
        detail
    };
    if !crate::watch::property_panic(KINDS[index], detail) {
        let at = match place(loc) {
            Some((path, line, col)) => format!("  at {path}:{line}:{col}\n"),
            None => String::new(),
        };
        let report = format!("panic: {}: {detail}\n{at}", KINDS[index]);
        if !crate::watch::test_panic(&report) {
            let _ = std::io::stderr().write_all(report.as_bytes());
        }
    }
    crate::watch::panicked();
    crate::watch::end(crate::watch::Ended::Status(101))
}

/// A panic of kind `kind` at `loc`, whose detail is the string `detail`, or the kind's own
/// detail when `detail` is 0. The compiler calls it for the panics its own code raises.
///
/// # Safety
///
/// `detail` is 0 or a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_panic(loc: u64, kind: u64, detail: u64) -> ! {
    let detail = if detail == 0 {
        ""
    } else {
        // SAFETY: the caller guarantees a nonzero `detail` is a string.
        unsafe { text::text(&detail) }
    };
    panic(loc, kind, detail)
}

/// Ends the program as running out of memory does, where compiled code would hold a value larger
/// than any it holds, as an array past the sizes implementations support (generics.large-arrays;
/// program.exit-statuses).
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_out_of_memory() -> ! {
    crate::entry::fatal("out of memory")
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![stilt_rt_panic, stilt_rt_out_of_memory,]
}
