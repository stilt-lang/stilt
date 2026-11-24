//! `stilt run` on directory programs whose entries the conformance suite can't hold, made as the
//! test runs (program.module-names): links that would make cycles, which are skipped, and a named
//! pipe whose name ends in `.lt`, which isn't a regular file and so no module.

#![cfg(unix)]

mod common;

use std::fs;
use std::os::unix::fs::symlink;
use std::path::Path;
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

const MAIN: &str = "use a.util\n\nfn main() / io {\n  util.say(\"read\")\n}\n";
const UTIL: &str = "pub fn say(s: str) / io { print(s) }\n";

/// Runs the program at `dir`, killed after a minute so that a read that never ends fails the
/// test rather than hanging it.
fn run(dir: &Path) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(["run", "."])
        .current_dir(dir)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("stilt runs");
    let start = Instant::now();
    while child.try_wait().expect("stilt can be waited for").is_none() {
        if start.elapsed() > Duration::from_secs(60) {
            let _ = child.kill();
            break;
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    let output = child.wait_with_output().expect("stilt ends");
    common::stop_engine(dir, Path::new("."));
    output
}

fn program(name: &str) -> std::path::PathBuf {
    let dir = common::directory("program_files", name);
    fs::create_dir(dir.join("a")).expect("a directory");
    fs::write(dir.join("main.lt"), MAIN).expect("main.lt");
    fs::write(dir.join("a/util.lt"), UTIL).expect("a/util.lt");
    dir
}

fn runs_and_prints_read(output: &Output) {
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    assert_eq!(String::from_utf8_lossy(&output.stdout), "read\n");
}

#[test]
fn links_that_would_make_cycles_are_skipped() {
    let dir = program("cycles");
    symlink("..", dir.join("a/up")).expect("a link");
    symlink("../..", dir.join("far")).expect("a link");
    symlink("itself", dir.join("itself")).expect("a link");
    runs_and_prints_read(&run(&dir));
}

#[test]
fn a_named_pipe_is_no_module() {
    let dir = program("pipe");
    let made = Command::new("mkfifo").arg(dir.join("pipe.lt")).status();
    if !made.is_ok_and(|status| status.success()) {
        return;
    }
    runs_and_prints_read(&run(&dir));
}
