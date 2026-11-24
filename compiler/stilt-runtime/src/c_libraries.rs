//! The C libraries that a program links, and the functions it calls of them and of the C library
//! (c.loading-libraries and c.calls): each library is loaded as the system's dynamic loader finds
//! `libNAME.dylib` on macOS and `libNAME.so` elsewhere, its functions visible to every later
//! lookup, and a foreign function is found by its name at its first call. A target whose
//! executables load no library, x86-64 Linux's static ones and WebAssembly's, links its foreign
//! functions instead, so this module is for the targets that load them.

use std::collections::HashMap;
use std::ffi::CString;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, PoisonError};

use crate::text;

/// The suffix of a shared library's file.
const SUFFIX: &str = if cfg!(target_os = "macos") {
    "dylib"
} else {
    "so"
};

/// Whether the system's dynamic loader finds the C library `name`, asked without loading it
/// (c.finding-libraries), so that no code of the library runs in the compiler, its engine or
/// its editor's server: the loader's directories are searched in its order for a bare name.
#[must_use]
pub fn finds(name: &str) -> bool {
    let file = format!("lib{name}.{SUFFIX}");
    !name.contains('/') && candidates(&file).iter().any(|path| loadable(path))
}

/// The directories that a variable of the environment lists, or `default` when it is unset.
fn listed(variable: &str, default: &str) -> Vec<PathBuf> {
    let value = std::env::var(variable).unwrap_or_else(|_| default.to_owned());
    value
        .split(':')
        .filter(|d| !d.is_empty())
        .map(PathBuf::from)
        .collect()
}

/// Where macOS's loader looks for a bare name: `DYLD_LIBRARY_PATH`, the working directory, then
/// `DYLD_FALLBACK_LIBRARY_PATH`, by default `/usr/local/lib` and `/usr/lib`.
#[cfg(target_os = "macos")]
fn candidates(file: &str) -> Vec<PathBuf> {
    let mut dirs = listed("DYLD_LIBRARY_PATH", "");
    dirs.extend(std::env::current_dir());
    dirs.extend(listed(
        "DYLD_FALLBACK_LIBRARY_PATH",
        "/usr/local/lib:/usr/lib",
    ));
    dirs.iter().map(|dir| dir.join(file)).collect()
}

/// Whether macOS's loader would load the file at `path`, asked of the loader itself, since its
/// system libraries live in a shared cache rather than in files.
#[cfg(target_os = "macos")]
fn loadable(path: &Path) -> bool {
    unsafe extern "C" {
        fn dlopen_preflight(path: *const libc::c_char) -> bool;
    }
    let Ok(path) = CString::new(path.as_os_str().as_encoded_bytes()) else {
        return false;
    };
    // SAFETY: the path is a C string; preflight runs no code of the library it finds.
    unsafe { dlopen_preflight(path.as_ptr()) }
}

/// Where the loader of Linux looks for a bare name: `LD_LIBRARY_PATH`, the libraries its cache
/// lists, then its default directories.
#[cfg(not(target_os = "macos"))]
fn candidates(file: &str) -> Vec<PathBuf> {
    let suffix = format!("/{file}");
    let cache = std::fs::read("/etc/ld.so.cache").unwrap_or_default();
    let cached = cache
        .split(|&b| b == 0)
        .filter_map(|entry| std::str::from_utf8(entry).ok())
        .filter(|entry| entry.starts_with('/') && entry.ends_with(&suffix))
        .map(PathBuf::from);
    let triple = format!("{}-linux-gnu", std::env::consts::ARCH);
    let defaults = ["/lib", "/usr/lib", "/lib64", "/usr/lib64"]
        .iter()
        .flat_map(|d| [PathBuf::from(d), Path::new(d).join(&triple)]);
    let listed = listed("LD_LIBRARY_PATH", "")
        .into_iter()
        .map(|dir| dir.join(file));
    listed
        .chain(cached)
        .chain(defaults.map(|dir| dir.join(file)))
        .collect()
}

/// Whether the file at `path` is an ELF object: a linker script named like a library, as
/// glibc's `libc.so` and `libm.so` are, isn't one the loader loads.
#[cfg(not(target_os = "macos"))]
fn loadable(path: &Path) -> bool {
    let mut magic = [0; 4];
    std::fs::File::open(path)
        .and_then(|mut file| std::io::Read::read_exact(&mut file, &mut magic))
        .is_ok_and(|()| magic == *b"\x7fELF")
}

/// Loads the C library `name`, and tells whether the loader found it (c.loading-libraries).
#[must_use]
pub fn load(name: &str) -> bool {
    let Ok(file) = CString::new(format!("lib{name}.{SUFFIX}")) else {
        return false;
    };
    // SAFETY: the file's name is a C string; the library stays loaded while the process runs.
    let handle = unsafe { libc::dlopen(file.as_ptr(), libc::RTLD_NOW | libc::RTLD_GLOBAL) };
    !handle.is_null()
}

/// Loads the libraries of a program, before any of its code runs: `names` is a string of
/// their names, each ended by a newline, in the order of c.linking.
///
/// # Safety
///
/// `names` is a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_c_load(names: u64) {
    // SAFETY: as the caller guarantees.
    let names = unsafe { text::text(&names) };
    for name in names.lines() {
        let _ = load(name);
    }
}

/// The address of each C function found so far, by its name.
static FOUND: Mutex<Option<HashMap<String, u64>>> = Mutex::new(None);

/// The address of the C function `name`, found among the C library and the libraries loaded at
/// its first call; a name that none of them defines ends the program, as running out of memory
/// does (c.finding-functions).
///
/// # Safety
///
/// `name` is a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_c_function(_loc: u64, name: u64) -> u64 {
    // SAFETY: as the caller guarantees.
    let name = unsafe { text::text(&name) };
    let mut found = FOUND.lock().unwrap_or_else(PoisonError::into_inner);
    let known = found.get_or_insert_with(HashMap::new);
    if let Some(&address) = known.get(name) {
        return address;
    }
    let address = CString::new(name).map_or(std::ptr::null_mut(), |c| {
        // SAFETY: the name is a C string, looked up among everything loaded.
        unsafe { libc::dlsym(libc::RTLD_DEFAULT, c.as_ptr()) }
    });
    if address.is_null() {
        drop(found);
        crate::entry::fatal(&format!("no C function {name}"));
    }
    known.insert(name.to_owned(), address as u64);
    address as u64
}

pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![stilt_rt_c_load, stilt_rt_c_function]
}

#[cfg(test)]
mod tests {
    use super::finds;

    #[test]
    fn finds_libraries_as_the_loader_does() {
        assert!(!finds("stilt-no-such-library"));
        assert!(!finds("../z"));
        // macOS keeps zlib in its shared cache, with no file of its own.
        #[cfg(target_os = "macos")]
        assert!(finds("z"));
    }
}
