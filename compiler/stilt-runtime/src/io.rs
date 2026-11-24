//! The program's output streams, and its arguments (program.output-flushing; std.cli).
//!
//! Standard output is written a line at a time, as Rust's `LineWriter` writes it: each line
//! that `print` writes reaches it when `print` returns, in one write, and what `io.write`
//! writes after its last newline waits for the next newline, for `io.flush()`, for a read of
//! standard input or for the program's end, however it ends but by an abort
//! (program.output-flushing). Text that fills [`HELD`] without a newline is written out, so the
//! wait holds no more. Standard error is written at once.
//!
//! Under `task.threads()` a write of a task that isn't at the front of the run's order waits in
//! its segment (`crate::tasks`), which passes it on here, in that order, as [`emit`].

use std::io::Write;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Mutex, MutexGuard, OnceLock, PoisonError};

/// The most that standard output holds back while it waits for a newline.
const HELD: usize = 64 * 1024;

/// What the program wrote to standard output after its last newline, which waits for the
/// next one.
static PENDING: Mutex<Vec<u8>> = Mutex::new(Vec::new());

static ARGS: OnceLock<Vec<String>> = OnceLock::new();

/// Whether what the program prints goes to standard error, as it does under `stilt test`,
/// whose standard output holds only its report (program.running-tests).
static PRINT_TO_STDERR: AtomicBool = AtomicBool::new(false);

/// Sends what the program prints to standard error from now on.
pub(crate) fn print_to_stderr() {
    PRINT_TO_STDERR.store(true, Ordering::Relaxed);
}

fn pending() -> MutexGuard<'static, Vec<u8>> {
    PENDING.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Whether standard output was found closed, as a pipe is once the program reading it has
/// ended: what is written to it from then on is dropped.
static CLOSED: AtomicBool = AtomicBool::new(false);

/// The exit status of a program whose standard output is closed (program.exit-statuses): the
/// one a shell reports for a process that the signal of a broken pipe ends, 128 + 13.
const CLOSED_STATUS: i32 = 141;

/// Writes the first `end` bytes of `pending` to standard output, which Rust's own buffer
/// passes on at once, and keeps the rest. Tells whether this write found the output closed,
/// which ends the program once its caller lets go of the output ([`ended_if`]).
fn write_out(pending: &mut Vec<u8>, end: usize) -> bool {
    let closed = if CLOSED.load(Ordering::Relaxed) {
        false
    } else {
        let mut out = std::io::stdout().lock();
        let written = out.write_all(&pending[..end]).and_then(|()| out.flush());
        matches!(written, Err(e) if e.kind() == std::io::ErrorKind::BrokenPipe)
            && !CLOSED.swap(true, Ordering::Relaxed)
    };
    pending.drain(..end);
    if pending.is_empty() && pending.capacity() > HELD {
        pending.shrink_to(HELD);
    }
    closed
}

/// Ends the program with [`CLOSED_STATUS`] when a write found its output closed.
fn ended_if(closed: bool) {
    if closed {
        crate::entry::exit(CLOSED_STATUS);
    }
}

/// What a write does, which a task's segment keeps until it goes out.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Kind {
    Print,
    Write,
    Eprint,
    Ewrite,
    Flush,
}

/// Does what a write of `kind` does with `bytes`, now.
pub(crate) fn emit(kind: Kind, bytes: &[u8]) {
    match kind {
        Kind::Print => print_now(bytes),
        Kind::Write => write_now(bytes),
        Kind::Eprint => eprint_now(bytes),
        Kind::Ewrite => {
            let _ = std::io::stderr().write_all(bytes);
        }
        Kind::Flush => flush_now(),
    }
}

/// Does a write of `kind`, now or, for a task that isn't at the front, once it is.
fn routed(kind: Kind, bytes: &[u8]) {
    if !crate::tasks::out(kind, bytes) {
        emit(kind, bytes);
    }
}

/// Writes `bytes` and a newline to standard output.
pub(crate) fn print(bytes: &[u8]) {
    routed(Kind::Print, bytes);
}

/// Writes `bytes` to standard output, with no newline (std.io): the text up to its
/// last newline goes out now, and the rest waits for the next one.
pub(crate) fn write(bytes: &[u8]) {
    routed(Kind::Write, bytes);
}

/// Writes `bytes` and a newline to standard error.
pub(crate) fn eprint(bytes: &[u8]) {
    routed(Kind::Eprint, bytes);
}

/// Writes `bytes` to standard error, with no newline.
pub(crate) fn ewrite(bytes: &[u8]) {
    routed(Kind::Ewrite, bytes);
}

/// Writes out everything written to standard output so far.
pub(crate) fn flush() {
    routed(Kind::Flush, &[]);
}

fn print_now(bytes: &[u8]) {
    if PRINT_TO_STDERR.load(Ordering::Relaxed) {
        return eprint_now(bytes);
    }
    let closed = {
        let mut pending = pending();
        pending.extend_from_slice(bytes);
        pending.push(b'\n');
        let end = pending.len();
        write_out(&mut pending, end)
    };
    ended_if(closed);
}

fn write_now(bytes: &[u8]) {
    if PRINT_TO_STDERR.load(Ordering::Relaxed) {
        let _ = std::io::stderr().write_all(bytes);
        return;
    }
    let closed = {
        let mut pending = pending();
        let before = pending.len();
        pending.extend_from_slice(bytes);
        let end = match bytes.iter().rposition(|&b| b == b'\n') {
            Some(i) => before + i + 1,
            None if pending.len() >= HELD => pending.len(),
            None => return,
        };
        write_out(&mut pending, end)
    };
    ended_if(closed);
}

fn eprint_now(bytes: &[u8]) {
    let mut line = Vec::with_capacity(bytes.len() + 1);
    line.extend_from_slice(bytes);
    line.push(b'\n');
    let _ = std::io::stderr().write_all(&line);
}

fn flush_now() {
    let closed = {
        let mut pending = pending();
        let end = pending.len();
        end > 0 && write_out(&mut pending, end)
    };
    ended_if(closed);
}

/// Registers the program's arguments, without its name (std.cli).
pub(crate) fn set_args(args: Vec<String>) {
    let _ = ARGS.set(args);
}

/// The program's arguments.
pub(crate) fn args() -> &'static [String] {
    ARGS.get().map_or(&[], Vec::as_slice)
}
