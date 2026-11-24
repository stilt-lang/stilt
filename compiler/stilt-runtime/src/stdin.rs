//! Standard input, as `std.io` reads it (std.read-line; std.io).
//!
//! Every read goes through one buffer of the runtime's own, so that `poll_line` sees the bytes
//! already read from the system as well as those the system holds, which `poll(2)` sees, and a
//! line that one function reads is never read again by another. The REPL reads its inputs from
//! the same buffer ([`line`]), so that an input that reads a line reads the next one. Bytes come
//! from the system through Rust's `Stdin`, whose own buffer a read of [`CHUNK`] bytes passes by
//! while it is empty, as it always is, since nothing else reads it.

use std::io::{ErrorKind, Read};
#[cfg(unix)]
use std::os::fd::AsFd;
use std::sync::{Mutex, MutexGuard, PoisonError};

#[cfg(unix)]
use nix::errno::Errno;
#[cfg(unix)]
use nix::poll::{PollFd, PollFlags, PollTimeout, poll};
#[cfg(unix)]
use nix::sys::select::{FdSet, select};
#[cfg(unix)]
use nix::sys::time::{TimeVal, TimeValLike};

/// How much one read from the system asks for, more than Rust's `Stdin` buffers.
const CHUNK: usize = 64 * 1024;

/// The bytes read from standard input and not yet taken, from `start` on, of which those
/// before `scanned` hold no newline, and whether the input has ended. Input that can't be read
/// ends as the end of the input does.
struct Input {
    bytes: Vec<u8>,
    start: usize,
    scanned: usize,
    ended: bool,
}

static INPUT: Mutex<Input> = Mutex::new(Input {
    bytes: Vec::new(),
    start: 0,
    scanned: 0,
    ended: false,
});

fn input() -> MutexGuard<'static, Input> {
    INPUT.lock().unwrap_or_else(PoisonError::into_inner)
}

impl Input {
    /// Reads from standard input once, which waits unless something is waiting.
    fn fill(&mut self) {
        self.bytes.drain(..self.start);
        self.scanned -= self.start;
        self.start = 0;
        let len = self.bytes.len();
        self.bytes.resize(len + CHUNK, 0);
        let read = loop {
            match std::io::stdin().lock().read(&mut self.bytes[len..]) {
                Err(e) if e.kind() == ErrorKind::Interrupted => {}
                read => break read.unwrap_or(0),
            }
        };
        self.bytes.truncate(len + read);
        self.ended = read == 0;
    }

    /// Takes the bytes up to `end` and skips `skip` more.
    fn take(&mut self, end: usize, skip: usize) -> Vec<u8> {
        let taken = self.bytes[self.start..end].to_vec();
        self.start = end + skip;
        self.scanned = self.start;
        taken
    }

    /// What is waiting: a whole line, without its `\n`, or once the input has ended its last
    /// line, or its end.
    fn waiting(&mut self) -> Waiting {
        let from = self.scanned.max(self.start);
        match self.bytes[from..].iter().position(|&b| b == b'\n') {
            Some(i) => Waiting::Line(self.take(from + i, 1)),
            None if self.ended && self.start < self.bytes.len() => {
                Waiting::Line(self.take(self.bytes.len(), 0))
            }
            None if self.ended => Waiting::End,
            None => {
                self.scanned = self.bytes.len();
                Waiting::Nothing
            }
        }
    }
}

/// What standard input holds that a read can take without asking the system.
enum Waiting {
    Line(Vec<u8>),
    End,
    Nothing,
}

/// How long a read that waits for standard input waits before it looks whether its run must
/// stop, as a watched run's does when an edit changes the layout of its values.
const STOP_POLL_MS: u16 = 50;

/// The next line of standard input, without its `\n`, waiting for it, or `None` at the end of
/// the input. While it waits, it looks whether its run must stop, and stops it without holding
/// the input, which the next run reads.
pub(crate) fn read_line() -> Option<Vec<u8>> {
    loop {
        {
            let mut input = input();
            match input.waiting() {
                Waiting::Line(line) => return Some(line),
                Waiting::End => return None,
                Waiting::Nothing if readable_within(STOP_POLL_MS) => {
                    input.fill();
                    continue;
                }
                Waiting::Nothing => {}
            }
        }
        crate::watch::stilt_rt_poll();
    }
}

/// The next line of standard input, as [`read_line`] reads it, when a whole line, or the last
/// line before the end of the input, is waiting, and `None` otherwise, without waiting.
pub(crate) fn poll_line() -> Option<Vec<u8>> {
    let mut input = input();
    loop {
        match input.waiting() {
            Waiting::Line(line) => return Some(line),
            Waiting::End => return None,
            Waiting::Nothing => {}
        }
        if !readable() {
            return None;
        }
        input.fill();
    }
}

/// The rest of standard input.
pub(crate) fn read_all() -> Vec<u8> {
    let mut input = input();
    while !input.ended {
        input.fill();
    }
    let end = input.bytes.len();
    input.take(end, 0)
}

/// The next line of standard input, without its `\n`, with invalid UTF-8 replaced, or `None`
/// at its end: an input of the REPL, read from the buffer the program reads.
#[must_use]
pub fn line() -> Option<String> {
    read_line().map(|line| String::from_utf8_lossy(&line).into_owned())
}

/// Whether a read of standard input would return at once, as WASI polls it (wasm.what-std-reads).
#[cfg(target_os = "wasi")]
fn readable() -> bool {
    crate::wasm::stdin_readable()
}

/// Whether a read of standard input may wait: under WASI, where nothing stops a run, it always
/// may.
#[cfg(target_os = "wasi")]
fn readable_within(_: u16) -> bool {
    true
}

/// Whether a read of standard input would return at once: something is waiting, or the input
/// has ended or can't be read, which ends it.
#[cfg(unix)]
fn readable() -> bool {
    readable_within(0)
}

/// Whether a read of standard input would return at once, waiting up to `ms` milliseconds for
/// something to come.
#[cfg(unix)]
fn readable_within(ms: u16) -> bool {
    let stdin = std::io::stdin();
    let mut fds = [PollFd::new(stdin.as_fd(), PollFlags::POLLIN)];
    loop {
        match poll(&mut fds, PollTimeout::from(ms)) {
            Ok(0) => return false,
            // macOS's `poll` doesn't support devices, which it answers so, while its `select`
            // does, as a terminal needs.
            Ok(_) if fds[0].revents() == Some(PollFlags::POLLNVAL) => return selectable(ms),
            Err(Errno::EINTR) => {}
            Ok(_) | Err(_) => return true,
        }
    }
}

#[cfg(unix)]
/// Whether `select` finds standard input readable, or fails, as it does on a descriptor that
/// isn't open, whose read then ends the input.
fn selectable(ms: u16) -> bool {
    let stdin = std::io::stdin();
    loop {
        let mut set = FdSet::new();
        set.insert(stdin.as_fd());
        let mut wait = TimeVal::milliseconds(i64::from(ms));
        match select(None, &mut set, None, None, &mut wait) {
            Ok(n) => return n > 0,
            Err(Errno::EINTR) => {}
            Err(_) => return true,
        }
    }
}
