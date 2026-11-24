//! `stilt reduce`: a command that doesn't stop on an internal error has nothing to reduce, and
//! the command is refused, with what to give it. The search itself is tested in the binary's own
//! tests (`reduce::search`), on failures that a test can make up.

use std::process::Command;

mod common;

#[test]
fn a_command_that_doesnt_stop_on_an_internal_error_is_refused() {
    let file = common::file("reduce", "fine", "fn main() / io { print(\"fine\") }\n");
    let out = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(["reduce", "-o"])
        .arg(file.with_file_name("bug"))
        .arg("check")
        .arg(&file)
        .output()
        .expect("stilt runs");
    assert_eq!(out.status.code(), Some(2), "{out:?}");
    let stderr = common::stderr(&out);
    assert!(
        stderr.contains("doesn't stop on an internal error"),
        "{stderr}"
    );
    assert!(!file.with_file_name("bug").exists(), "nothing is written");
}
