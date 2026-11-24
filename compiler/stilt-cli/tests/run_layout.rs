//! An edit that changes the layout of a running program's values while the program waits for
//! standard input: the run stops first, and only then does the new code go in, so that no code of
//! the new layout ever runs on values of the old one (goal edit-to-running-program).

use std::fs;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// A program that holds a record while it waits for a line that never comes.
const WAITING: &str = "use std.io\n\ntype Point = { x: i64, y: i64 }\n\nfn main() / io {\n  let p = Point { x: 1, y: 2 }\n  print(\"waiting x={p.x}\")\n  if let Some(line) = io.read_line() {\n    print(\"read {line} y={p.y}\")\n  }\n}\n";

/// Waits until `seen` holds of the files `out` and `err`, and fails if it never does.
fn wait(out: &PathBuf, err: &PathBuf, what: &str, seen: impl Fn(&str, &str) -> bool) -> String {
    let since = Instant::now();
    loop {
        let o = fs::read_to_string(out).unwrap_or_default();
        let e = fs::read_to_string(err).unwrap_or_default();
        if seen(&o, &e) {
            return e;
        }
        assert!(
            since.elapsed() < Duration::from_secs(30),
            "never saw {what}\n--- stdout\n{o}\n--- stderr\n{e}"
        );
        std::thread::sleep(Duration::from_millis(20));
    }
}

#[test]
fn a_layout_edit_stops_a_run_waiting_for_input_before_its_new_code_goes_in() {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("run_layout");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("the directory can be made");
    fs::write(dir.join("main.lt"), WAITING).expect("the program can be written");
    let (out, err) = (dir.with_extension("out"), dir.with_extension("err"));
    let mut child = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .current_dir(&dir)
        .args(["run", "."])
        .stdin(Stdio::piped())
        .stdout(fs::File::create(&out).expect("stdout can be written"))
        .stderr(fs::File::create(&err).expect("stderr can be written"))
        .spawn()
        .expect("stilt runs");
    wait(&out, &err, "the first run", |o, _| {
        o.contains("waiting x=1")
    });
    let moved = WAITING
        .replace("{ x: i64, y: i64 }", "{ x: i64, y: i64, z: i64 }")
        .replace("Point { x: 1, y: 2 }", "Point { x: 1, y: 2, z: 3 }")
        .replace("waiting x={p.x}", "waiting z={p.z}");
    fs::write(dir.join("main.lt"), moved).expect("the program can be written");
    let stderr = wait(&out, &err, "the new run", |o, e| {
        o.contains("waiting z=3") && e.contains("so it starts again")
    });
    let _ = child.kill();
    let _ = child.wait();
    assert!(
        !stderr.contains("didn't stop"),
        "the run waiting for input stopped\n{stderr}"
    );
    let stdout = fs::read_to_string(&out).unwrap_or_default();
    assert_eq!(
        stdout, "waiting x=1\nwaiting z=3\n",
        "the old run printed nothing more"
    );
}
