//! What the tests that run commands share. A command on a directory program starts the
//! program's engine (goal one-engine), which a test then stops, so that no engine outlives
//! the test.

#![allow(dead_code, reason = "each test uses some of these")]

pub(crate) mod editor;
pub(crate) mod suite;

use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

/// Stops the engine of the program at `path`, relative to `dir`, if one runs.
pub(crate) fn stop_engine(dir: &Path, path: &Path) {
    let _ = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .current_dir(dir)
        .args(["engine", "--stop"])
        .arg(path)
        .output();
}

/// The first four hexadecimal digits of the BLAKE3 digest of `canonical`, which is the hash
/// of a part with that canonical text (edits.hash).
pub(crate) fn hash(canonical: &str) -> String {
    let digest = blake3::hash(canonical.as_bytes());
    digest.to_hex().as_str()[..4].to_owned()
}

/// A directory of the test's own under `group`, emptied.
pub(crate) fn directory(group: &str, name: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(group)
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("the directory can be made");
    dir
}

/// A program of one file, which is module `main`, holding `source`.
pub(crate) fn file(group: &str, name: &str, source: &str) -> PathBuf {
    let path = directory(group, name).join("main.lt");
    fs::write(&path, source).expect("the program can be written");
    path
}

/// A directory program whose files are `files`, each a name and its text.
pub(crate) fn project(group: &str, name: &str, files: &[(&str, &str)]) -> PathBuf {
    let dir = directory(group, name);
    for (file, source) in files {
        fs::write(dir.join(file), source).expect("the file can be written");
    }
    dir
}

/// Runs `stilt` with `args`, giving `stdin` to it if there is any.
pub(crate) fn stilt(args: &[&str], stdin: Option<&str>) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(args)
        .stdin(if stdin.is_some() {
            Stdio::piped()
        } else {
            Stdio::null()
        })
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("stilt runs");
    if let Some(text) = stdin {
        child
            .stdin
            .take()
            .expect("a pipe")
            .write_all(text.as_bytes())
            .expect("stdin is writable");
    }
    child.wait_with_output().expect("stilt ends")
}

/// Stops the engine a command on the directory program `path` may have started.
pub(crate) fn finish(path: &Path) {
    if path.is_dir() {
        stop_engine(Path::new("."), path);
    }
}

/// A temporary directory in which the engines' directory can't be made, because a file has
/// its name, so that a command uses no engine and runs in its own process, after a line on
/// stderr that says so ([`without_engine_note`]; engines.private).
pub(crate) fn no_engine() -> PathBuf {
    let tmp = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("no_engine");
    fs::create_dir_all(&tmp).expect("the directory can be made");
    let file = tmp.join(format!("stilt-{}", user()));
    fs::write(&file, "").expect("the file can be written");
    tmp
}

/// The id of the user the tests run as, the owner of what they make.
pub(crate) fn user() -> u32 {
    use std::os::unix::fs::MetadataExt as _;
    let tmp = PathBuf::from(env!("CARGO_TARGET_TMPDIR"));
    fs::create_dir_all(&tmp).expect("the directory can be made");
    fs::metadata(&tmp).expect("the directory exists").uid()
}

/// What a command wrote to stderr, without the line in which it says that it runs without an
/// engine, as it does under [`no_engine`].
pub(crate) fn without_engine_note(stderr: &[u8]) -> Vec<u8> {
    let text = String::from_utf8_lossy(stderr);
    text.split_inclusive('\n')
        .filter(|line| !line.ends_with("so the command runs without an engine\n"))
        .collect::<String>()
        .into_bytes()
}

/// The text a command wrote to stdout.
pub(crate) fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

/// The text a command wrote to stderr.
pub(crate) fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}
