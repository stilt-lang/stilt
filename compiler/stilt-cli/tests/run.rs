//! `stilt run` while the program runs: each edit of a running program's files is patched into it,
//! so that the next call of an edited function runs its new code while the program keeps its state.
//! An edit that changes which parameters a function consumes patches its callers too
//! (values.consumed-parameters), and one that makes a function reachable patches it in, with the
//! code it has then, however it was edited while unreached. An edit with errors patches nothing,
//! and one that changes the layout of the program's values starts the program again. When the
//! program ends, `run` ends with its status, 2 for a program that had errors when it started
//! (program.programs-with-errors).

mod common;

use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

/// How long a test waits for the run to show what it expects.
const PATIENCE: Duration = Duration::from_secs(30);

/// A run of a program, killed when it is dropped.
struct Run {
    child: Child,
    dir: PathBuf,
}

impl Run {
    fn start(name: &str, source: &str) -> Self {
        let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
            .join("run")
            .join(name);
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("the directory can be made");
        fs::write(dir.join("main.lt"), source).expect("the program can be written");
        let out = fs::File::create(dir.join("out.txt")).expect("stdout can be written");
        let err = fs::File::create(dir.join("err.txt")).expect("stderr can be written");
        let child = Command::new(env!("CARGO_BIN_EXE_stilt"))
            .arg("run")
            .arg(&dir)
            .stdin(Stdio::piped())
            .stdout(out)
            .stderr(err)
            .spawn()
            .expect("stilt runs");
        Self { child, dir }
    }

    fn edit(&self, from: &str, to: &str) {
        self.edits(&[(from, to)]);
    }

    /// Makes every replacement in one write, so that the run never sees the program halfway.
    fn edits(&self, replacements: &[(&str, &str)]) {
        let path = self.dir.join("main.lt");
        let mut text = fs::read_to_string(&path).expect("the program can be read");
        for (from, to) in replacements {
            assert!(text.contains(from), "the program holds {from:?}");
            text = text.replace(from, to);
        }
        fs::write(&path, text).expect("the program can be written");
    }

    /// Gives the program a line of input, and closes its input.
    fn input(&mut self, line: &str) {
        let mut stdin = self.child.stdin.take().expect("stdin is piped");
        writeln!(stdin, "{line}").expect("the program reads stdin");
    }

    fn stdout(&self) -> String {
        read(&self.dir.join("out.txt"))
    }

    fn stderr(&self) -> String {
        read(&self.dir.join("err.txt"))
    }

    /// Waits until `seen` holds of what the run printed, and fails the test if it never does.
    fn wait(&self, what: &str, seen: impl Fn(&str, &str) -> bool) {
        let start = Instant::now();
        while start.elapsed() < PATIENCE {
            if seen(&self.stdout(), &self.stderr()) {
                return;
            }
            std::thread::sleep(Duration::from_millis(20));
        }
        panic!(
            "never saw {what}\n--- stdout\n{}\n--- stderr\n{}",
            tail(&self.stdout()),
            self.stderr()
        );
    }

    /// The lines of what `run` reported that tell how many functions it patched.
    fn patches(&self) -> Vec<String> {
        let err = self.stderr();
        err.lines()
            .filter(|l| l.starts_with("stilt: patched"))
            .map(str::to_owned)
            .collect()
    }

    /// Waits until `run` has reported `n` patches.
    fn wait_patches(&self, n: usize) {
        self.wait(&format!("{n} patches"), |_, err| {
            err.lines()
                .filter(|l| l.starts_with("stilt: patched"))
                .count()
                >= n
        });
    }

    /// Waits for `run` to end, and fails the test if it never does.
    fn status(&mut self) -> ExitStatus {
        let start = Instant::now();
        while start.elapsed() < PATIENCE {
            if let Some(status) = self.child.try_wait().expect("the run can be waited for") {
                return status;
            }
            std::thread::sleep(Duration::from_millis(20));
        }
        panic!("the run never ended\n--- stderr\n{}", self.stderr());
    }
}

impl Drop for Run {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
        common::stop_engine(&self.dir, Path::new("."));
    }
}

fn read(path: &Path) -> String {
    fs::read_to_string(path).unwrap_or_default()
}

fn tail(text: &str) -> String {
    let lines: Vec<&str> = text.lines().collect();
    lines[lines.len().saturating_sub(5)..].join("\n")
}

/// A program that runs until it is stopped, printing a line every so often.
const FOREVER: &str = "type Point = { x: i64, y: i64 }\n\nfn greeting(n: i64) -> str { \"hello {n}\" }\n\nfn spin(k: i64) -> i64 {\n  var i = 0\n  var acc = 0\n  while i < k {\n    acc = acc + i % 7\n    i = i + 1\n  }\n  acc\n}\n\nfn main() / io {\n  let p = Point { x: 1, y: 2 }\n  var n = 0\n  while true {\n    if n % 2000 == 0 {\n      print(\"{greeting(n / 2000)} x={p.x}\")\n    }\n    let _ = spin(100)\n    n = n + 1\n  }\n}\n";

/// The number after the first word of a line of output, such as 3 in `hello 3 x=1`.
fn number(line: &str) -> Option<i64> {
    line.split(' ').nth(1)?.parse().ok()
}

#[test]
fn a_running_program_runs_the_new_code_of_an_edited_function() {
    let r = Run::start("patch", FOREVER);
    r.wait("the first output", |out, _| out.contains("hello 3 "));
    r.edit("\"hello {n}\"", "\"patched {n}\"");
    r.wait("the patched output", |out, _| out.contains("patched"));
    let out = r.stdout();
    let lines: Vec<&str> = out.lines().collect();
    let first = lines
        .iter()
        .position(|l| l.starts_with("patched"))
        .unwrap_or(0);
    let before = lines.get(first.wrapping_sub(1)).and_then(|l| number(l));
    let after = lines.get(first).and_then(|l| number(l));
    assert_eq!(
        after,
        before.map(|b| b + 1),
        "the program kept its state\n{}",
        tail(&out)
    );
    assert!(
        r.stderr().contains("stilt: patched 1 function"),
        "{}",
        r.stderr()
    );
}

/// A program whose `label` only reads its parameter `s`, called from a loop that never returns.
const LABELS: &str = "fn label(s: str, n: i64) -> str {\n  if s.len() > 9 { \"long\" } else { \"hello {n}\" }\n}\n\nfn spin(k: i64) -> i64 {\n  var i = 0\n  var acc = 0\n  while i < k {\n    acc = acc + i % 7\n    i = i + 1\n  }\n  acc\n}\n\nfn main() / io {\n  var n = 0\n  while true {\n    if n % 2000 == 0 {\n      print(label(\"x\", n / 2000))\n    }\n    let _ = spin(100)\n    n = n + 1\n  }\n}\n";

#[test]
fn an_edit_that_changes_what_a_function_consumes_patches_its_callers() {
    let r = Run::start("consumed", LABELS);
    r.wait("the first output", |out, _| out.contains("hello 3"));
    // `label` now returns `s` on one path, so it consumes it, and `main` gives it the string.
    r.edit(
        "{ \"long\" } else { \"hello {n}\" }",
        "{ s } else { \"hi {n}\" }",
    );
    r.wait("the patched output", |out, _| out.contains("hi "));
    let out = r.stdout();
    let lines: Vec<&str> = out.lines().collect();
    let first = lines.iter().position(|l| l.starts_with("hi ")).unwrap_or(0);
    let before = lines.get(first.wrapping_sub(1)).and_then(|l| number(l));
    let after = lines.get(first).and_then(|l| number(l));
    assert_eq!(
        after,
        before.map(|b| b + 1),
        "the program kept its state, and the loop already running reaches the new code\n{}",
        tail(&out)
    );
    assert!(
        r.stderr().contains("stilt: patched 2 functions"),
        "`label` and its caller `main` are patched\n{}",
        r.stderr()
    );
}

/// A program whose `greeting` is called from a loop that never returns, and whose `spare` no
/// code calls.
const SPARE: &str = "fn greeting(n: i64) -> str { \"hello {n}\" }\n\nfn spare(n: i64) -> str { \"spare {n}\" }\n\nfn spin(k: i64) -> i64 {\n  var i = 0\n  var acc = 0\n  while i < k {\n    acc = acc + i % 7\n    i = i + 1\n  }\n  acc\n}\n\nfn main() / io {\n  var n = 0\n  while true {\n    if n % 2000 == 0 {\n      print(greeting(n / 2000))\n    }\n    let _ = spin(100)\n    n = n + 1\n  }\n}\n";

/// The number after the first word of the first line that starts with `word`, and of the line
/// before it.
fn around(out: &str, word: &str) -> (Option<i64>, Option<i64>) {
    let lines: Vec<&str> = out.lines().collect();
    let first = lines.iter().position(|l| l.starts_with(word)).unwrap_or(0);
    let before = lines.get(first.wrapping_sub(1)).and_then(|l| number(l));
    (before, lines.get(first).and_then(|l| number(l)))
}

#[test]
fn an_edit_that_reaches_a_function_patches_it_in() {
    let r = Run::start("reaches", SPARE);
    r.wait("the first output", |out, _| out.contains("hello 3"));
    r.edit("{ \"hello {n}\" }", "{ spare(n) }");
    r.wait("the patched output", |out, _| out.contains("spare "));
    let (before, after) = around(&r.stdout(), "spare ");
    assert_eq!(after, before.map(|b| b + 1), "{}", tail(&r.stdout()));
    assert_eq!(
        r.patches(),
        ["stilt: patched 2 functions"],
        "`greeting` and `spare`, which it now calls, are patched"
    );
}

#[test]
fn a_function_edited_while_unreached_runs_its_new_code_once_reached_again() {
    let calling = SPARE.replace("{ \"hello {n}\" }", "{ spare(n) }");
    let r = Run::start("unreached", &calling);
    r.wait("the first output", |out, _| out.contains("spare 1"));
    r.edit("{ spare(n) }", "{ \"hello {n}\" }");
    r.wait_patches(1);
    r.edit("\"spare {n}\"", "\"again {n}\"");
    r.wait_patches(2);
    r.edit("{ \"hello {n}\" }", "{ spare(n) }");
    r.wait("the new code of `spare`", |out, _| out.contains("again "));
    let (before, after) = around(&r.stdout(), "again ");
    assert_eq!(after, before.map(|b| b + 1), "{}", tail(&r.stdout()));
    assert_eq!(
        r.patches(),
        [
            "stilt: patched 1 function",
            "stilt: patched 0 functions",
            "stilt: patched 2 functions"
        ],
        "an edit of `spare` while no code calls it patches nothing, and calling it again \
         patches its new code"
    );
}

#[test]
fn an_edit_with_errors_patches_nothing() {
    let r = Run::start("errors", FOREVER);
    r.wait("the first output", |out, _| out.contains("hello 1 "));
    r.edit("\"hello {n}\"", "\"hello {missing}\"");
    r.wait("the refusal", |_, err| {
        err.contains("so the edit isn't patched")
    });
    let seen = r.stdout().lines().count();
    r.wait("more output", |out, _| out.lines().count() > seen + 2);
    assert!(!r.stdout().contains("missing"));
}

#[test]
fn a_change_of_layout_starts_the_program_again() {
    let r = Run::start("layout", FOREVER);
    r.wait("the first output", |out, _| out.contains("hello 2 "));
    r.edits(&[
        ("{ x: i64, y: i64 }", "{ x: i64, y: i64, z: i64 }"),
        ("Point { x: 1, y: 2 }", "Point { x: 1, y: 2, z: 3 }"),
        ("x={p.x}", "z={p.z}"),
    ]);
    r.wait("the new run", |out, _| out.contains("hello 1 z=3"));
    let out = r.stdout();
    let first = out.lines().position(|l| l.contains("z=3")).unwrap_or(0);
    assert!(
        out.lines()
            .nth(first)
            .is_some_and(|l| l.starts_with("hello 0 z=3")),
        "{}",
        tail(&out)
    );
    assert!(
        out.lines().skip(first).all(|l| l.contains("z=3")),
        "the old run stopped"
    );
}

/// A program whose call of `std.par` runs forever on the pool's workers, its first element,
/// which the calling thread runs, ending at once, so that the calling thread waits for them.
const PARTS_FOREVER: &str = "use std.par\n\ntype Point = { x: i64, y: i64 }\n\nfn forever(i: i64) -> i64 {\n  var n = i\n  while n > 0 {\n    n = n % 1000 + 1\n  }\n  n\n}\n\nfn main() / io {\n  let p = Point { x: 1, y: 2 }\n  print(\"started x={p.x}\")\n  var xs = [0]\n  for i in 1..64 {\n    xs.push(i)\n  }\n  let ys = par.map(xs, |i| if i == 0 { 0 } else { forever(i) })\n  print(\"{ys.len()}\")\n}\n";

#[test]
fn a_run_whose_workers_run_its_code_stops_and_starts_again() {
    let r = Run::start("workers", PARTS_FOREVER);
    r.wait("the first run", |out, _| out.contains("started x=1"));
    // Let the workers take their parts, whose stop polls alone can end the run.
    std::thread::sleep(Duration::from_millis(200));
    r.edits(&[
        ("{ x: i64, y: i64 }", "{ x: i64, y: i64, z: i64 }"),
        ("Point { x: 1, y: 2 }", "Point { x: 1, y: 2, z: 3 }"),
        ("x={p.x}", "z={p.z}"),
    ]);
    r.wait("the new run", |out, _| out.contains("started z=3"));
}

/// A program that waits for a line of input, then answers it and ends.
const ANSWER: &str = "use std.io\n\nfn greeting() -> str { \"hello\" }\n\nfn main() / io {\n  print(\"ready\")\n  let line = io.read_line() else \"\"\n  print(\"{greeting()} {line}\")\n}\n";

#[test]
fn the_run_ends_with_the_program_and_its_status() {
    let mut r = Run::start("ends", ANSWER);
    r.wait("the program waiting", |out, _| out.contains("ready"));
    r.edit("\"hello\"", "\"patched\"");
    r.wait("the patch", |_, err| {
        err.contains("stilt: patched 1 function")
    });
    r.input("go");
    let status = r.status();
    assert_eq!(status.code(), Some(0), "{}", r.stderr());
    assert_eq!(r.stdout(), "ready\npatched go\n");
    assert!(
        !r.stderr().contains("never freed"),
        "every count is back to zero after the patch (no-leaks)\n{}",
        r.stderr()
    );
}

#[test]
fn a_run_that_started_with_errors_ends_with_status_2_once_they_are_fixed() {
    let source = ANSWER.replace(
        "fn greeting",
        "fn unused() -> i64 { missing }\n\nfn greeting",
    );
    let mut r = Run::start("fixed", &source);
    r.wait("the program waiting", |out, _| out.contains("ready"));
    assert!(r.stderr().contains("E0211"), "{}", r.stderr());
    r.edit("{ missing }", "{ 0 }");
    r.wait("the patch", |_, err| err.contains("stilt: patched"));
    r.input("go");
    let status = r.status();
    assert_eq!(status.code(), Some(2), "{}", r.stderr());
    assert_eq!(r.stdout(), "ready\nhello go\n");
}

#[test]
fn every_argument_after_the_path_is_the_programs() {
    let dir = std::env::temp_dir().join(format!("stilt-run-args-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("the directory");
    let main = "use std.cli\n\nfn main() / io { print(\"{cli.args()}\") }\n";
    std::fs::write(dir.join("main.lt"), main).expect("the program");
    let out = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(["run", ".", "--help", "-x", "--", "y"])
        .current_dir(&dir)
        .output()
        .expect("stilt runs");
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "[\"--help\", \"-x\", \"--\", \"y\"]\n",
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
}
