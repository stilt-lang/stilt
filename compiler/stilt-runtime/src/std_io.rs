//! The natives of `std.io`, `std.cli` and `std.fs` (std.io-errors, std.fs and std.cli; std.io and
//! std.cli).
//!
//! A failed file operation raises a `std.io.IoError` that names the path, as a variant of four
//! whose payload is the path's string: it writes the error's two words, its tag and the path, to
//! memory that its caller passes a pointer to, as its last argument (`crate::abi`).

use std::io::ErrorKind;

use crate::abi::{Ret, immediate, option};
use crate::object;
use crate::{io, list, stdin, text};

/// The variants of `std.io.IoError`, in their declaration order.
#[derive(Clone, Copy)]
pub(crate) enum IoError {
    NotFound = 0,
    PermissionDenied = 1,
    InvalidUtf8 = 2,
    Other = 3,
}

impl IoError {
    /// The variant for a failure of the operating system.
    pub(crate) fn of(error: &std::io::Error) -> Self {
        match error.raw_os_error() {
            Some(libc::ENOENT | libc::ENOTDIR) => IoError::NotFound,
            Some(libc::EACCES | libc::EPERM) => IoError::PermissionDenied,
            _ if error.kind() == ErrorKind::NotFound => IoError::NotFound,
            _ if error.kind() == ErrorKind::PermissionDenied => IoError::PermissionDenied,
            _ => IoError::Other,
        }
    }

    /// Raises the error, whose payload is a new reference to the path: writes its two words,
    /// the tag of its variant and the path, to the memory `err` points to. On WebAssembly, a path
    /// that the system finds nothing at outside the directories granted the module is refused
    /// (wasm.what-std-reads).
    ///
    /// # Safety
    ///
    /// `path` is a live string, and `err` points to room for two words.
    pub(crate) unsafe fn raise(self, path: u64, err: *mut u64) -> Ret {
        // SAFETY: the caller guarantees the string and the room.
        unsafe {
            #[cfg(target_os = "wasi")]
            let this = match self {
                IoError::NotFound if !crate::wasm::granted(text::text(&path)) => {
                    IoError::PermissionDenied
                }
                other => other,
            };
            #[cfg(not(target_os = "wasi"))]
            let this = self;
            object::dup(path);
            err.write(immediate(this as u64));
            err.add(1).write(path);
        }
        Ret::raise(0)
    }
}

/// The text of a file, or why it can't be read: a path that names a directory, or that holds
/// U+0000, is `Other`.
fn read_file(path: &str) -> Result<String, IoError> {
    if path.contains('\0') {
        return Err(IoError::Other);
    }
    let bytes = std::fs::read(path).map_err(|e| IoError::of(&e))?;
    String::from_utf8(bytes).map_err(|_| IoError::InvalidUtf8)
}

/// A line of standard input as `read_line` gives it: without a `\r` that ends it, and with
/// invalid UTF-8 replaced, each maximal subpart by one U+FFFD.
fn line_option(line: Option<Vec<u8>>) -> Ret {
    option(line.map(|mut line| {
        if line.last() == Some(&b'\r') {
            line.pop();
        }
        text::from(&String::from_utf8_lossy(&line))
    }))
}

/// `read_line()`: one line of standard input, without its `\n`, and without a `\r` that ends
/// what is left. `None` at the end of the input, or when it can't be read.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_io_read_line(_loc: u64) -> Ret {
    // A task reads in its turn (tasks.same-output-under-every-handler), and what the program wrote
    // shows before it waits (std.io).
    crate::tasks::turn();
    io::flush();
    line_option(stdin::read_line())
}

/// `poll_line()`: one line of standard input, read as `read_line` reads it, when a whole line,
/// or the last line before the end of the input, is waiting, and `None` otherwise, without
/// waiting (std.io).
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_io_poll_line(_loc: u64) -> Ret {
    crate::tasks::turn();
    io::flush();
    line_option(stdin::poll_line())
}

/// `io.flush()`: writes out what the program has written to standard output
/// (program.output-flushing).
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_io_flush(_loc: u64) -> Ret {
    io::flush();
    Ret::unit()
}

/// `io.write(s)`: writes `s` to standard output, with no newline.
///
/// # Safety
///
/// `s` is a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_io_write(_loc: u64, s: u64) -> Ret {
    // SAFETY: the caller guarantees the string is alive.
    io::write(unsafe { text::bytes(&s) });
    Ret::unit()
}

/// `io.ewrite(s)`: writes `s` to standard error, with no newline.
///
/// # Safety
///
/// `s` is a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_io_ewrite(_loc: u64, s: u64) -> Ret {
    // SAFETY: the caller guarantees the string is alive.
    io::ewrite(unsafe { text::bytes(&s) });
    Ret::unit()
}

/// `io.read_all()`: the rest of standard input, with invalid UTF-8 replaced, or `""` when it
/// can't be read.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_io_read_all(_loc: u64) -> Ret {
    crate::tasks::turn();
    io::flush();
    Ret::ok(text::from(&String::from_utf8_lossy(&stdin::read_all())))
}

/// `cli.env(name)`: the value of an environment variable, with invalid UTF-8 replaced, or
/// `None` when it isn't set or `name` couldn't name one.
///
/// # Safety
///
/// `name` is a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_cli_env(_loc: u64, name: u64) -> Ret {
    // SAFETY: the caller guarantees the string is alive.
    let name = unsafe { text::text(&name) };
    if name.is_empty() || name.contains(['=', '\0']) {
        return option(None);
    }
    let value = std::env::var_os(name).map(|v| text::from(&v.to_string_lossy()));
    option(value)
}

/// `args()`: the program's arguments, without its name.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_cli_args(_loc: u64) -> Ret {
    let words: Vec<u64> = io::args().iter().map(|a| text::from(a)).collect();
    Ret::ok(list::from_words(&words, crate::shape::STR) as u64)
}

/// `read(path)`: the file's contents.
///
/// # Safety
///
/// `path` is a live string, and `err` points to room for an error's two words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_fs_read(_loc: u64, path: u64, err: u64) -> Ret {
    let err = err as usize as *mut u64;
    // SAFETY: the caller guarantees the string is alive, and the room.
    match read_file(unsafe { text::text(&path) }) {
        Ok(contents) => Ret::ok(text::from(&contents)),
        // SAFETY: as above.
        Err(e) => unsafe { e.raise(path, err) },
    }
}

/// `read_lines(path)`: the file split as `str.lines` splits it.
///
/// # Safety
///
/// `path` is a live string, and `err` points to room for an error's two words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_fs_read_lines(loc: u64, path: u64, err: u64) -> Ret {
    let err = err as usize as *mut u64;
    // SAFETY: the caller guarantees the string is alive, and the room.
    match read_file(unsafe { text::text(&path) }) {
        Ok(contents) => {
            let contents = text::from(&contents);
            // SAFETY: `contents` is a live string, released once split.
            unsafe {
                let lines = crate::std_str::stilt_std_prelude_str_lines(loc, contents);
                object::drop(contents);
                lines
            }
        }
        // SAFETY: as above.
        Err(e) => unsafe { e.raise(path, err) },
    }
}

/// `write(path, text)`: creates or replaces the file, with `text` as its contents.
///
/// # Safety
///
/// `path` and `contents` are live strings, and `err` points to room for an error's two words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_fs_write(
    _loc: u64,
    path: u64,
    contents: u64,
    err: u64,
) -> Ret {
    let err = err as usize as *mut u64;
    // SAFETY: the caller guarantees the strings are alive, and the room.
    unsafe {
        let (name, bytes) = (text::text(&path), text::bytes(&contents));
        if name.contains('\0') {
            return IoError::Other.raise(path, err);
        }
        match std::fs::write(name, bytes) {
            Ok(()) => Ret::unit(),
            Err(e) => IoError::of(&e).raise(path, err),
        }
    }
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_std_io_read_line,
        stilt_std_io_poll_line,
        stilt_std_io_flush,
        stilt_std_io_write,
        stilt_std_io_ewrite,
        stilt_std_io_read_all,
        stilt_std_cli_args,
        stilt_std_cli_env,
        stilt_std_fs_read,
        stilt_std_fs_read_lines,
        stilt_std_fs_write,
    ]
}
