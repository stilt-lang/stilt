//! A cache of the other implementation's commands, so that the reference interpreter runs each program once.
//!
//! The reference interpreter is deterministic, so what it prints for a command depends only on
//! its binary and on the command: the arguments, the standard input, the target and the
//! contents of the program's files. The key of a command hashes all of them (`SipHash`, 64 bits),
//! and its result is one file under the cache's directory. Only a command that exited is
//! stored, never a timeout or a signal, so a slow machine never leaves a failure behind. A new
//! binary changes every key, and a miss costs one run, so a stale entry can never be read.

use std::collections::hash_map::DefaultHasher;
use std::fs;
use std::hash::{Hash, Hasher};
use std::io;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use crate::discovery::{self, Test};
use crate::process::{Output, Status};

/// The commands of one implementation, stored under a directory.
#[derive(Debug)]
pub(crate) struct Cache {
    dir: PathBuf,
    /// The hash of the implementation's binary.
    binary: u64,
}

/// Distinguishes the temporary names of jobs that store at once.
static STORES: AtomicU64 = AtomicU64::new(0);

impl Cache {
    /// Opens the cache in `dir` for the implementation whose binary is `program`.
    pub(crate) fn open(dir: &Path, program: &Path) -> Result<Self, String> {
        fs::create_dir_all(dir)
            .map_err(|error| format!("cannot create {}: {error}", dir.display()))?;
        let bytes = fs::read(program)
            .map_err(|error| format!("cannot read {}: {error}", program.display()))?;
        let mut hasher = DefaultHasher::new();
        bytes.hash(&mut hasher);
        Ok(Self {
            dir: dir.to_owned(),
            binary: hasher.finish(),
        })
    }

    /// The key of a command on `test`, or an error when its program cannot be read.
    pub(crate) fn key(&self, test: &Test, args: &[&str], stdin: &[u8]) -> io::Result<String> {
        let mut hasher = DefaultHasher::new();
        self.binary.hash(&mut hasher);
        args.hash(&mut hasher);
        stdin.hash(&mut hasher);
        test.target.hash(&mut hasher);
        if test.target == "." {
            hash_tree(&test.dir, "", &mut hasher)?;
        } else {
            fs::read(test.dir.join(&test.target))?.hash(&mut hasher);
        }
        Ok(format!("{:016x}", hasher.finish()))
    }

    /// The stored result under `key`, if there is one.
    pub(crate) fn fetch(&self, key: &str) -> Option<Output> {
        decode(&fs::read(self.dir.join(key)).ok()?)
    }

    /// Stores `output` under `key`, unless the command timed out or was killed. Failing to
    /// store only costs a later run.
    pub(crate) fn store(&self, key: &str, output: &Output) {
        let Some(bytes) = encode(output) else {
            return;
        };
        let id = STORES.fetch_add(1, Ordering::Relaxed);
        let temporary = self
            .dir
            .join(format!("{key}.{}.{id}.tmp", std::process::id()));
        if fs::write(&temporary, bytes).is_err()
            || fs::rename(&temporary, self.dir.join(key)).is_err()
        {
            let _ = fs::remove_file(&temporary);
        }
    }
}

/// Hashes the files under `dir` in name order, each with its path from the program's root.
fn hash_tree(dir: &Path, prefix: &str, hasher: &mut DefaultHasher) -> io::Result<()> {
    for path in discovery::entries(dir)? {
        let name = path.file_name().unwrap_or_default().to_string_lossy();
        let relative = format!("{prefix}{name}");
        if path.is_dir() {
            hash_tree(&path, &format!("{relative}/"), hasher)?;
        } else {
            relative.hash(hasher);
            fs::read(&path)?.hash(hasher);
        }
    }
    Ok(())
}

/// A result as bytes: the exit status, then the lengths and contents of stdout and stderr.
fn encode(output: &Output) -> Option<Vec<u8>> {
    let Status::Exited(code) = output.status else {
        return None;
    };
    let mut bytes = code.to_le_bytes().to_vec();
    for stream in [&output.stdout, &output.stderr] {
        bytes.extend((stream.len() as u64).to_le_bytes());
        bytes.extend(stream);
    }
    Some(bytes)
}

fn decode(bytes: &[u8]) -> Option<Output> {
    let (code, rest) = bytes.split_first_chunk::<4>()?;
    let (stdout, rest) = take_stream(rest)?;
    let (stderr, rest) = take_stream(rest)?;
    rest.is_empty().then(|| Output {
        status: Status::Exited(i32::from_le_bytes(*code)),
        stdout,
        stderr,
    })
}

fn take_stream(bytes: &[u8]) -> Option<(Vec<u8>, &[u8])> {
    let (length, rest) = bytes.split_first_chunk::<8>()?;
    let length = usize::try_from(u64::from_le_bytes(*length)).ok()?;
    (rest.len() >= length).then(|| (rest[..length].to_vec(), &rest[length..]))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    /// A temporary directory, removed when dropped.
    struct Scratch(PathBuf);

    impl Scratch {
        fn new(name: &str) -> Self {
            let dir =
                std::env::temp_dir().join(format!("stilt-cache-{name}-{}", std::process::id()));
            let _ = fs::remove_dir_all(&dir);
            fs::create_dir_all(&dir).unwrap();
            Self(dir)
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn test(scratch: &Scratch, text: &str) -> Test {
        fs::write(scratch.0.join("main.lt"), text).unwrap();
        Test {
            name: "t".to_owned(),
            dir: scratch.0.clone(),
            target: "main.lt".to_owned(),
            header_file: "main.lt".to_owned(),
            files: Vec::new(),
        }
    }

    fn binary(scratch: &Scratch, text: &str) -> PathBuf {
        let path = scratch.0.join("impl");
        fs::write(&path, text).unwrap();
        path
    }

    fn exited(code: i32, stdout: &str) -> Output {
        Output {
            status: Status::Exited(code),
            stdout: stdout.into(),
            stderr: b"err".to_vec(),
        }
    }

    #[test]
    fn a_hit_returns_the_stored_output() {
        let scratch = Scratch::new("hit");
        let cache = Cache::open(&scratch.0.join("cache"), &binary(&scratch, "v1")).unwrap();
        let test = test(&scratch, "fn main() {}");
        let key = cache.key(&test, &["run", "."], b"in").unwrap();
        assert!(cache.fetch(&key).is_none());
        cache.store(&key, &exited(3, "out"));
        let stored = cache.fetch(&key).unwrap();
        assert_eq!(stored.status, Status::Exited(3));
        assert_eq!(stored.stdout, b"out");
        assert_eq!(stored.stderr, b"err");
        let again = cache.key(&test, &["run", "."], b"in").unwrap();
        assert_eq!(key, again);
    }

    #[test]
    fn a_change_to_the_program_the_args_or_the_binary_misses() {
        let scratch = Scratch::new("miss");
        let program = binary(&scratch, "v1");
        let cache = Cache::open(&scratch.0.join("cache"), &program).unwrap();
        let key = cache.key(&test(&scratch, "a"), &["run"], b"").unwrap();
        cache.store(&key, &exited(0, "x"));
        let edited = cache.key(&test(&scratch, "b"), &["run"], b"").unwrap();
        assert!(cache.fetch(&edited).is_none());
        let other_args = cache.key(&test(&scratch, "a"), &["check"], b"").unwrap();
        assert!(cache.fetch(&other_args).is_none());
        let other_stdin = cache.key(&test(&scratch, "a"), &["run"], b"s").unwrap();
        assert!(cache.fetch(&other_stdin).is_none());
        fs::write(&program, "v2").unwrap();
        let rebuilt = Cache::open(&scratch.0.join("cache"), &program).unwrap();
        let moved = rebuilt.key(&test(&scratch, "a"), &["run"], b"").unwrap();
        assert!(rebuilt.fetch(&moved).is_none());
    }

    #[test]
    fn a_directory_program_is_keyed_by_all_its_files() {
        let scratch = Scratch::new("tree");
        let cache = Cache::open(&scratch.0.join("cache"), &binary(&scratch, "v1")).unwrap();
        let mut test = test(&scratch, "a");
        test.target = ".".to_owned();
        let before = cache.key(&test, &["check"], b"").unwrap();
        fs::create_dir_all(scratch.0.join("sub")).unwrap();
        fs::write(scratch.0.join("sub/util.lt"), "b").unwrap();
        assert_ne!(before, cache.key(&test, &["check"], b"").unwrap());
    }

    #[test]
    fn a_timeout_or_a_signal_is_not_stored() {
        let scratch = Scratch::new("timeout");
        let cache = Cache::open(&scratch.0.join("cache"), &binary(&scratch, "v1")).unwrap();
        for status in [
            Status::TimedOut(Duration::from_secs(10)),
            Status::Signaled(9),
        ] {
            let output = Output {
                status,
                stdout: Vec::new(),
                stderr: Vec::new(),
            };
            cache.store("key", &output);
            assert!(cache.fetch("key").is_none());
        }
    }
}
