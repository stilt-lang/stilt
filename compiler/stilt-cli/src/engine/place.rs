//! Where a program's engine listens, and which compiler it is. Each version of `stilt` has
//! engines of its own, so the names of an engine's socket and lock file are a hash of the
//! program's canonical path and the version (engines.toolchains).

use std::fs::{File, TryLockError};
use std::io;
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant, UNIX_EPOCH};

use super::private;

/// How long an engine that finds the lock file held waits for it before it yields.
const PATIENCE: Duration = Duration::from_millis(200);

/// The version that `stilt --version` prints.
const VERSION: &str = env!("STILT_VERSION");

/// The socket and the lock file of a program's engine.
#[derive(Clone, Debug)]
pub(super) struct Place {
    /// The program's canonical path.
    pub(super) program: PathBuf,
    pub(super) socket: PathBuf,
    lock: PathBuf,
    /// Where the engine writes its own errors, such as a panic's report.
    pub(super) log: PathBuf,
}

impl Place {
    /// The place of this version's engine of the program at `path`, if the path exists.
    pub(super) fn of(path: &Path) -> Option<Self> {
        Some(Self::named(path.canonicalize().ok()?, VERSION))
    }

    /// The place of the engine of version `version` of the program at the canonical path
    /// `program`.
    fn named(program: PathBuf, version: &str) -> Self {
        let mut hasher = blake3::Hasher::new();
        hasher.update(version.as_bytes());
        hasher.update(&[0]);
        hasher.update(program.as_os_str().as_encoded_bytes());
        let name = &hasher.finalize().to_hex()[..16];
        let dir = private::directory();
        Self {
            socket: dir.join(format!("{name}.sock")),
            lock: dir.join(format!("{name}.lock")),
            log: dir.join(format!("{name}.log")),
            program,
        }
    }

    /// Makes the directory of the user's engines private to the user, or says why it can't
    /// be ([`private::make_private`]).
    pub(super) fn private(&self) -> Result<(), String> {
        let dir = self.socket.parent().unwrap_or(Path::new("."));
        private::make_private(dir)
    }

    /// A connection to the engine that listens at the place, when one does and it runs as
    /// this user (engines.private).
    pub(super) fn connect(&self) -> Option<UnixStream> {
        let stream = UnixStream::connect(&self.socket).ok()?;
        private::same_user(&stream).then_some(stream)
    }

    /// The lock file, held, or `None` when another engine holds it. A command looking for an
    /// engine ([`Place::held`]) locks the file for an instant, so a refusal is tried again
    /// for [`PATIENCE`] before it counts.
    pub(super) fn hold(&self) -> io::Result<Option<File>> {
        self.private().map_err(io::Error::other)?;
        let since = Instant::now();
        loop {
            match self.try_hold()? {
                None if since.elapsed() < PATIENCE => std::thread::sleep(Duration::from_millis(5)),
                held => return Ok(held),
            }
        }
    }

    fn try_hold(&self) -> io::Result<Option<File>> {
        let file = File::create(&self.lock)?;
        match file.try_lock() {
            Ok(()) => Ok(Some(file)),
            Err(TryLockError::WouldBlock) => Ok(None),
            Err(TryLockError::Error(e)) => Err(e),
        }
    }

    /// Whether an engine holds the lock file.
    pub(super) fn held(&self) -> bool {
        File::open(&self.lock)
            .is_ok_and(|file| matches!(file.try_lock(), Err(TryLockError::WouldBlock)))
    }
}

/// Which compiler this is: its version, and the path and time of change of its executable, so
/// that a command never talks to an engine that another build of the compiler started
/// (engines.toolchains).
pub(crate) fn identity() -> String {
    let exe = std::env::current_exe().unwrap_or_default();
    let changed = std::fs::metadata(&exe)
        .and_then(|m| m.modified())
        .ok()
        .and_then(|t| t.duration_since(UNIX_EPOCH).ok())
        .map_or(0, |d| d.as_nanos());
    format!("stilt {VERSION} {} {changed}", exe.display())
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::Place;

    #[test]
    fn each_version_has_an_engine_of_its_own_for_a_program() {
        let program = PathBuf::from("/work/shapes");
        let one = Place::named(program.clone(), "2027.1.0 (abc 2027-01-04)");
        let again = Place::named(program.clone(), "2027.1.0 (abc 2027-01-04)");
        let other = Place::named(program, "2027.2.0 (def 2027-02-01)");
        assert_eq!(one.socket, again.socket);
        assert_eq!(one.lock, again.lock);
        assert_ne!(one.socket, other.socket);
        assert_ne!(one.lock, other.lock);
        assert_eq!(one.socket.parent(), other.socket.parent(), "one directory");
    }

    #[test]
    fn each_program_has_an_engine_of_its_own() {
        let one = Place::named(PathBuf::from("/work/shapes"), "2027.1.0");
        let other = Place::named(PathBuf::from("/work/shape"), "2027.1.0");
        assert_ne!(one.socket, other.socket);
    }
}
