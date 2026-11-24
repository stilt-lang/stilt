//! The runtime of a library that `stilt build --lib` writes
//! (c.calls-from-c).
//!
//! A C program calls the library's exported functions on threads of its own, each call running
//! on the calling thread and its stack. The first call makes the runtime ready, as an
//! executable's start does, but for two things: a library has no arguments, so `cli.args()` is
//! the empty list, and it installs no handler of faults, so that a stack overflow ends the
//! process as the C program's own does. A panic reports, writes what the program wrote and ends
//! the process with status 101, as in a program, since no run is watched. Each call ends with
//! what it wrote written to its file.

use std::sync::Once;

/// Whether the runtime is ready, once the first call from C has made it so.
static READY: Once = Once::new();

/// Makes the runtime ready for a call from C. The first call registers the paths of the
/// program's files, which panics report, and an empty list of arguments; later calls, from any
/// thread, find it ready.
///
/// # Safety
///
/// `files` is a table of the program's files, each ended by a NUL and the whole by an empty
/// one.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_ready(files: u64) {
    let files = files as usize as *const libc::c_char;
    READY.call_once(|| {
        // SAFETY: the caller guarantees `files` is such a table.
        let paths = unsafe { crate::entry::file_table(files) };
        crate::panic::set_files(paths);
        crate::io::set_args(Vec::new());
    });
}

/// Ends a call from C: what the call wrote, a partial line included, reaches its file.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_returned() {
    crate::io::flush();
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![stilt_rt_ready, stilt_rt_returned]
}
