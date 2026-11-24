//! The natives of `std.fs` that std.fs adds: appending, bytes, existence, directories,
//! removal and renaming.
//!
//! A failed operation raises a `std.io.IoError` that names a path, as `std_io` raises it, and a
//! path that holds U+0000, which names no file, is `Other`.

use std::io::Write as _;
use std::path::Path;

use crate::abi::Ret;
use crate::object::Header;
use crate::std_io::IoError;
use crate::{list, text};

/// The path a live string names, or `Other` for one that holds U+0000.
///
/// # Safety
///
/// `path` holds a live string, which outlives the path.
unsafe fn named(path: &u64) -> Result<&str, IoError> {
    // SAFETY: the caller guarantees the string is alive.
    let name = unsafe { text::text(path) };
    if name.contains('\0') {
        Err(IoError::Other)
    } else {
        Ok(name)
    }
}

/// The result of an operation on the path `path`, or its error raised with that path.
///
/// # Safety
///
/// `path` is a live string, and `err` points to room for an error's two words.
unsafe fn done(path: u64, err: *mut u64, result: Result<u64, IoError>) -> Ret {
    match result {
        Ok(value) => Ret::ok(value),
        // SAFETY: the caller guarantees the string and the room.
        Err(e) => unsafe { e.raise(path, err) },
    }
}

/// The failure of a system operation, as `IoError`.
fn io<T>(result: std::io::Result<T>) -> Result<T, IoError> {
    result.map_err(|e| IoError::of(&e))
}

/// Defines natives of `std.fs` whose one path argument each failure names: each body takes the
/// path's text and the other arguments, and gives the word of its result or the failure.
macro_rules! natives {
    ($($(#[$doc:meta])* fn $name:ident($p:ident $(, $arg:ident)*) $body:block)*) => {
        $(
            $(#[$doc])*
            ///
            /// # Safety
            ///
            /// The path and every string or list argument are alive, and `err` points to room
            /// for an error's two words.
            #[unsafe(no_mangle)]
            pub(crate) unsafe extern "C" fn $name(_loc: u64, path: u64, $($arg: u64,)* err: u64) -> Ret {
                let err = err as usize as *mut u64;
                // SAFETY: the caller guarantees the path, the arguments and the room.
                unsafe {
                    let result = named(&path).and_then(|$p: &str| -> Result<u64, IoError> { $body });
                    done(path, err, result)
                }
            }
        )*
    };
}

/// Whether the file of `path` is a regular file or a directory, following symbolic links.
///
/// # Safety
///
/// `path` is a live string.
unsafe fn kind(path: u64) -> Option<std::fs::FileType> {
    // SAFETY: the caller guarantees the string is alive.
    let name = unsafe { named(&path) }.ok()?;
    std::fs::metadata(name).ok().map(|m| m.file_type())
}

natives! {
    /// `fs.append(path, text)`: adds `text` at the end of the file, creating it.
    fn stilt_std_fs_append(p, contents) {
        let mut file = io(std::fs::OpenOptions::new().append(true).create(true).open(p))?;
        if io(file.metadata())?.is_dir() {
            return Err(IoError::Other);
        }
        io(file.write_all(text::bytes(&contents)))?;
        Ok(0)
    }
    /// `fs.read_bytes(path)`: the file's bytes.
    fn stilt_std_fs_read_bytes(p) {
        Ok(list::of_bytes(&io(std::fs::read(p))?) as u64)
    }
    /// `fs.write_bytes(path, bytes)`: creates or replaces the file, with `bytes` as its contents.
    fn stilt_std_fs_write_bytes(p, bytes) {
        io(std::fs::write(p, list::as_bytes(bytes as *mut Header)))?;
        Ok(0)
    }
    /// `fs.list_dir(path)`: the names of the entries, sorted by their bytes.
    fn stilt_std_fs_list_dir(p) {
        if !io(std::fs::metadata(p))?.is_dir() {
            return Err(IoError::Other);
        }
        let mut names = Vec::new();
        for entry in io(std::fs::read_dir(p))? {
            names.push(io(entry)?.file_name().to_string_lossy().into_owned());
        }
        names.sort();
        let words: Vec<u64> = names.iter().map(|n| text::from(n)).collect();
        Ok(list::from_words(&words, crate::shape::STR) as u64)
    }
    /// `fs.create_dir(path)`: the directory and every missing directory on its path.
    fn stilt_std_fs_create_dir(p) {
        match std::fs::metadata(p) {
            Ok(m) if m.is_dir() => Ok(0),
            Ok(_) => Err(IoError::Other),
            Err(_) => io(std::fs::create_dir_all(p)).map(|()| 0),
        }
    }
    /// `fs.remove(path)`: the file, or the directory when it is empty.
    fn stilt_std_fs_remove(p) {
        if io(std::fs::symlink_metadata(p))?.is_dir() {
            io(std::fs::remove_dir(p))?;
        } else {
            io(std::fs::remove_file(p))?;
        }
        Ok(0)
    }
    /// `fs.remove_all(path)`: the file, or the directory and everything in it, never following
    /// a symbolic link.
    fn stilt_std_fs_remove_all(p) {
        if io(std::fs::symlink_metadata(p))?.is_dir() {
            io(std::fs::remove_dir_all(p))?;
        } else {
            io(std::fs::remove_file(p))?;
        }
        Ok(0)
    }
}

/// `fs.rename(from, to)`: moves `from` to `to`. A failure names `from` when it doesn't exist,
/// and otherwise `to`.
///
/// # Safety
///
/// `from` and `to` are live strings, and `err` points to room for an error's two words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_fs_rename(
    _loc: u64,
    from: u64,
    to: u64,
    err: u64,
) -> Ret {
    let err = err as usize as *mut u64;
    // SAFETY: the caller guarantees the strings and the room.
    unsafe {
        let source = named(&from).and_then(|f| io(std::fs::symlink_metadata(f)).map(|_| f));
        let Ok(source) = source else {
            return done(from, err, source.map(|_| 0));
        };
        let moved = named(&to).and_then(|t| io(std::fs::rename(Path::new(source), t)));
        done(to, err, moved.map(|()| 0))
    }
}

/// `fs.exists(path)`.
///
/// # Safety
///
/// `path` is a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_fs_exists(_loc: u64, path: u64) -> Ret {
    // SAFETY: the caller guarantees the string is alive.
    Ret::ok(u64::from(unsafe { kind(path) }.is_some()))
}

/// `fs.is_file(path)`.
///
/// # Safety
///
/// `path` is a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_fs_is_file(_loc: u64, path: u64) -> Ret {
    // SAFETY: the caller guarantees the string is alive.
    Ret::ok(u64::from(
        unsafe { kind(path) }.is_some_and(|k| k.is_file()),
    ))
}

/// `fs.is_dir(path)`.
///
/// # Safety
///
/// `path` is a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_fs_is_dir(_loc: u64, path: u64) -> Ret {
    // SAFETY: the caller guarantees the string is alive.
    Ret::ok(u64::from(unsafe { kind(path) }.is_some_and(|k| k.is_dir())))
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_std_fs_append,
        stilt_std_fs_read_bytes,
        stilt_std_fs_write_bytes,
        stilt_std_fs_exists,
        stilt_std_fs_is_file,
        stilt_std_fs_is_dir,
        stilt_std_fs_list_dir,
        stilt_std_fs_create_dir,
        stilt_std_fs_remove,
        stilt_std_fs_remove_all,
        stilt_std_fs_rename,
    ]
}
