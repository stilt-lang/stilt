//! The engine (goal one-engine): `stilt check` and `stilt build` answered by a process
//! that holds the program's query database, with the reports they give in their own process,
//! and `stilt run` given its code by it, with the run it gives alone. A build or a run right
//! after a check runs no query of the front end again, the engine takes in each edit of the
//! program's files, its manifests included, and patches a running program's, answers several
//! commands and runs at once, and stops once idle.

use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::time::{Duration, Instant};

mod common;

use common::no_engine;

const MAIN: &str =
    "use shapes\n\nfn main() / io {\n  print(\"{shapes.area(shapes.Square(3))}\")\n}\n";
const SHAPES: &str = "pub type Shape = | Square(i64) | Rect(i64, i64)\n\npub fn area(s: Shape) -> i64 {\n  match s {\n    Square(n) => n * n\n    Rect(w, h) => w * h\n  }\n}\n";

/// A program in a directory of its own, with its engine, stopped when this is dropped.
struct Engine {
    dir: PathBuf,
    child: Child,
}

impl Engine {
    fn start(name: &str, idle: u64) -> Self {
        Self::with(name, idle, &[("main.lt", MAIN), ("shapes.lt", SHAPES)])
    }

    /// The engine of a program of `files`, each a name and a text.
    fn with(name: &str, idle: u64, files: &[(&str, &str)]) -> Self {
        let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
            .join("engine")
            .join(name);
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("the directory can be made");
        for (file, text) in files {
            write(&dir.join(file), text);
        }
        let child = stilt(&dir)
            .args(["engine", "--record", "--idle", &idle.to_string(), "."])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .expect("the engine starts");
        let engine = Self { dir, child };
        let since = Instant::now();
        while !engine.ran().status.success() {
            assert!(
                since.elapsed() < Duration::from_secs(30),
                "the engine listens"
            );
            std::thread::sleep(Duration::from_millis(10));
        }
        engine
    }

    /// The queries the engine ran since this was last asked.
    fn ran(&self) -> Output {
        stilt(&self.dir)
            .args(["engine", "--ran", "."])
            .output()
            .expect("stilt runs")
    }

    fn queries(&self) -> HashSet<String> {
        let output = self.ran();
        assert!(output.status.success(), "{output:?}");
        String::from_utf8_lossy(&output.stdout)
            .lines()
            .map(str::to_owned)
            .collect()
    }

    /// `stilt ARGS` on the program, answered by the engine, and in its own process.
    fn both(&self, args: &[&str]) -> (Output, Output) {
        let engine = stilt(&self.dir).args(args).output().expect("stilt runs");
        let mut alone = stilt(&self.dir)
            .env("TMPDIR", no_engine())
            .args(args)
            .output()
            .expect("stilt runs");
        alone.stderr = common::without_engine_note(&alone.stderr);
        (engine, alone)
    }

    fn write(&self, file: &str, text: &str) {
        write(&self.dir.join(file), text);
    }
}

impl Drop for Engine {
    fn drop(&mut self) {
        let _ = stilt(&self.dir).args(["engine", "--stop", "."]).output();
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn write(path: &Path, text: &str) {
    fs::create_dir_all(path.parent().expect("a file has a directory")).expect("it can be made");
    fs::write(path, text).expect("the program can be written");
}

fn stilt(dir: &Path) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_stilt"));
    command.current_dir(dir);
    command
}

#[test]
fn a_build_after_a_check_runs_no_query_again() {
    let engine = Engine::start("again", 60);
    engine.queries();
    let (checked, _) = engine.both(&["check", "."]);
    assert!(checked.status.success(), "{checked:?}");
    let by_check = engine.queries();
    assert!(by_check.iter().any(|q| q.starts_with("body_diagnostics(")));
    let (built, _) = engine.both(&["build", "-o", "program", "."]);
    assert!(built.status.success(), "{built:?}");
    let by_build = engine.queries();
    let again: Vec<&String> = by_build.intersection(&by_check).collect();
    assert!(again.is_empty(), "the build ran again {again:?}");
    for front in ["parse(", "resolve_module(", "body_diagnostics(", "check("] {
        assert!(
            !by_build.iter().any(|q| q.starts_with(front)),
            "the build ran {front}: {by_build:?}"
        );
    }
    let run = Command::new(engine.dir.join("program"))
        .output()
        .expect("the program runs");
    assert_eq!(String::from_utf8_lossy(&run.stdout), "9\n");
}

fn same(both: &(Output, Output)) {
    let (engine, alone) = both;
    assert_eq!(engine.status.code(), alone.status.code(), "{both:?}");
    assert_eq!(engine.stdout, alone.stdout, "{both:?}");
    assert_eq!(engine.stderr, alone.stderr, "{both:?}");
}

#[test]
fn the_engine_reports_what_the_command_alone_does() {
    let engine = Engine::start("same", 60);
    same(&engine.both(&["check", "."]));
    engine.write("shapes.lt", &SHAPES.replace("w * h", "w * \"h\""));
    for args in [
        &["check", "."][..],
        &["check", "--json", "."],
        &["build", "."],
    ] {
        let both = engine.both(args);
        assert!(!both.0.status.success(), "{both:?}");
        same(&both);
    }
    engine.write("extra.lt", "pub fn unused() -> i64 {\n  true\n}\n");
    same(&engine.both(&["check", "--json", "."]));
    fs::remove_file(engine.dir.join("extra.lt")).expect("the file can be removed");
    engine.write("shapes.lt", SHAPES);
    let program = || fs::read(engine.dir.join("program")).expect("the program was built");
    let build = |tmp: Option<&Path>| {
        let mut command = stilt(&engine.dir);
        if let Some(tmp) = tmp {
            command.env("TMPDIR", tmp);
        }
        let output = command
            .args(["build", "-o", "program", "."])
            .output()
            .expect("stilt runs");
        assert!(output.status.success(), "{output:?}");
        program()
    };
    assert!(
        build(None) == build(Some(&no_engine())),
        "the executables differ"
    );
}

/// The manifests of the root and of its path dependencies are inputs of the engine's database, so
/// an edit of one gives the next check what a check alone gives (packages.dependencies and
/// packages.grants).
#[test]
fn the_engine_takes_in_each_edit_of_a_manifest() {
    let csv = "csv = { path = \"deps/csv\" }\n";
    let engine = Engine::with(
        "manifest",
        60,
        &[
            ("stilt.toml", &format!("[dependencies]\n{csv}")),
            (
                "src/main.lt",
                "use csv\n\nfn main() / io { csv.report(3) }\n",
            ),
            ("deps/csv/stilt.toml", "[package]\nname = \"csv\"\n"),
            (
                "deps/csv/src/main.lt",
                "pub fn report(n: i64) / io { print(\"{n} rows\") }\n",
            ),
            ("deps/json/stilt.toml", "[package]\nname = \"json\"\n"),
            (
                "deps/json/src/main.lt",
                "pub fn parse(s: str) -> i64 { 1 }\n",
            ),
        ],
    );
    let check = |code: Option<&str>| {
        let both = engine.both(&["check", "--json", "."]);
        same(&both);
        let found = String::from_utf8_lossy(&both.0.stdout).into_owned();
        match code {
            Some(code) => assert!(found.contains(&format!("\"code\":\"{code}\"")), "{found}"),
            None => assert!(both.0.status.success(), "{found}"),
        }
    };
    check(Some("E0608"));
    let granted = csv.replace(" }", ", may = [\"io\"] }");
    engine.write("stilt.toml", &format!("[dependencies]\n{granted}"));
    check(None);
    let main = "use csv\nuse json\n\nfn main() / io { csv.report(json.parse(\"3\")) }\n";
    engine.write("src/main.lt", main);
    check(Some("E0205"));
    let json = "json = { path = \"deps/json\" }\n";
    engine.write("stilt.toml", &format!("[dependencies]\n{granted}{json}"));
    check(None);
    engine.write("deps/json/stilt.toml", "[package]\nname = \"jsn\"\n");
    check(Some("E0603"));
}

#[test]
fn commands_at_once_each_get_their_report() {
    let engine = Engine::start("at_once", 60);
    let (_, expected) = engine.both(&["check", "--json", "."]);
    let commands: Vec<Child> = (0..6)
        .map(|_| {
            stilt(&engine.dir)
                .args(["check", "--json", "."])
                .stdout(Stdio::piped())
                .spawn()
                .expect("stilt runs")
        })
        .collect();
    for command in commands {
        let output = command.wait_with_output().expect("stilt runs");
        assert_eq!(output.stdout, expected.stdout);
    }
}

#[test]
fn an_idle_engine_stops() {
    let mut engine = Engine::start("idle", 1);
    let since = Instant::now();
    while engine
        .child
        .try_wait()
        .expect("the engine can be waited for")
        .is_none()
    {
        assert!(
            since.elapsed() < Duration::from_secs(30),
            "the engine stops"
        );
        std::thread::sleep(Duration::from_millis(100));
    }
    assert!(!engine.ran().status.success(), "no engine runs");
}

#[test]
fn a_run_by_way_of_the_engine_gives_what_a_run_alone_does() {
    let engine = Engine::start("run_same", 60);
    let both = engine.both(&["run", "."]);
    assert_eq!(String::from_utf8_lossy(&both.0.stdout), "9\n", "{both:?}");
    same(&both);
    assert!(
        engine.queries().iter().any(|q| q.starts_with("functions(")),
        "the engine lowered the program"
    );
    // A program with errors runs all the same, after its diagnostics
    // (program.programs-with-errors).
    engine.write("extra.lt", "pub fn unused() -> i64 {\n  true\n}\n");
    let both = engine.both(&["run", "."]);
    assert_eq!(both.0.status.code(), Some(2), "{both:?}");
    same(&both);
    fs::remove_file(engine.dir.join("extra.lt")).expect("the file can be removed");
    engine.write("main.lt", "fn start() {}\n");
    same(&engine.both(&["run", "."]));
}

#[test]
fn a_run_after_a_check_runs_no_query_of_the_front_end_again() {
    let engine = Engine::start("run_again", 60);
    engine.queries();
    let (checked, _) = engine.both(&["check", "."]);
    assert!(checked.status.success(), "{checked:?}");
    let by_check = engine.queries();
    let run = stilt(&engine.dir)
        .args(["run", "."])
        .output()
        .expect("stilt runs");
    assert_eq!(String::from_utf8_lossy(&run.stdout), "9\n", "{run:?}");
    let by_run = engine.queries();
    assert!(
        by_run.iter().any(|q| q.starts_with("functions(")),
        "the engine lowered the program: {by_run:?}"
    );
    let again: Vec<&String> = by_run.intersection(&by_check).collect();
    assert!(again.is_empty(), "the run ran again {again:?}");
    for front in ["parse(", "resolve_module(", "body_diagnostics(", "check("] {
        assert!(
            !by_run.iter().any(|q| q.starts_with(front)),
            "the run ran {front}: {by_run:?}"
        );
    }
}

/// A program that runs until it is stopped, printing a line every so often.
const FOREVER: &str = "type Point = { x: i64, y: i64 }\n\nfn greeting(n: i64) -> str { \"hello {n}\" }\n\nfn spin(k: i64) -> i64 {\n  var i = 0\n  var acc = 0\n  while i < k {\n    acc = acc + i % 7\n    i = i + 1\n  }\n  acc\n}\n\nfn main() / io {\n  let p = Point { x: 1, y: 2 }\n  var n = 0\n  while true {\n    if n % 2000 == 0 {\n      print(\"{greeting(n / 2000)} x={p.x}\")\n    }\n    let _ = spin(100)\n    n = n + 1\n  }\n}\n";

/// A run of the engine's program, its output written to files of its own, killed when this is
/// dropped.
struct Running {
    child: Child,
    out: PathBuf,
    err: PathBuf,
}

impl Running {
    fn start(engine: &Engine, name: &str) -> Self {
        let out = engine.dir.with_extension(format!("{name}.out"));
        let err = engine.dir.with_extension(format!("{name}.err"));
        let child = stilt(&engine.dir)
            .args(["run", "."])
            .stdout(fs::File::create(&out).expect("stdout can be written"))
            .stderr(fs::File::create(&err).expect("stderr can be written"))
            .spawn()
            .expect("stilt runs");
        Self { child, out, err }
    }

    /// Waits until `seen` holds of the run's stdout and stderr, and fails if it never does.
    fn wait(&self, what: &str, seen: impl Fn(&str, &str) -> bool) {
        let since = Instant::now();
        loop {
            let out = fs::read_to_string(&self.out).unwrap_or_default();
            let err = fs::read_to_string(&self.err).unwrap_or_default();
            if seen(&out, &err) {
                return;
            }
            assert!(
                since.elapsed() < Duration::from_secs(30),
                "never saw {what}\n--- stderr\n{err}"
            );
            std::thread::sleep(Duration::from_millis(20));
        }
    }
}

impl Drop for Running {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

#[test]
fn an_edit_made_while_a_run_runs_is_patched_in_by_the_engine() {
    let engine = Engine::with("run_patch", 60, &[("main.lt", FOREVER)]);
    engine.queries();
    let run = Running::start(&engine, "run");
    run.wait("the first output", |out, _| out.contains("hello 2 "));
    let started = engine.queries();
    assert!(
        started.iter().any(|q| q.starts_with("functions(")),
        "the engine lowered the program: {started:?}"
    );
    let main = fs::read_to_string(engine.dir.join("main.lt")).expect("the program can be read");
    let patched = main.replace("\"hello {n}\"", "\"patched {n}\"");
    engine.write("main.lt", &patched);
    run.wait("the patched output", |out, err| {
        out.contains("patched") && err.contains("stilt: patched 1 function")
    });
    assert!(
        engine.queries().iter().any(|q| q.starts_with("parse(")),
        "the engine took the edit in"
    );
    let moved = patched
        .replace("{ x: i64, y: i64 }", "{ x: i64, y: i64, z: i64 }")
        .replace("Point { x: 1, y: 2 }", "Point { x: 1, y: 2, z: 3 }")
        .replace("x={p.x}", "z={p.z}");
    engine.write("main.lt", &moved);
    run.wait("the new run", |out, err| {
        out.contains("patched 0 z=3") && err.contains("so it starts again")
    });
}

/// A program whose `label` only reads its parameter `s`, called from a loop that never returns.
const LABELS: &str = "fn label(s: str, n: i64) -> str {\n  if s.len() > 9 { \"long\" } else { \"hello {n}\" }\n}\n\nfn main() / io {\n  var n = 0\n  while true {\n    if n % 20000 == 0 {\n      print(label(\"x\", n / 20000))\n    }\n    n = n + 1\n  }\n}\n";

#[test]
fn an_edit_that_changes_what_a_function_consumes_patches_its_callers_by_way_of_the_engine() {
    let engine = Engine::with("run_consumed", 60, &[("main.lt", LABELS)]);
    let run = Running::start(&engine, "run");
    run.wait("the first output", |out, _| out.contains("hello 2"));
    // `label` now returns `s` on one path, so it consumes it, and `main` gives it the string
    // (values.consumed-parameters): the engine sends both, and the loop already running in `main`'s
    // old code reaches `label`'s new code through a bridge.
    let consumed = LABELS.replace(
        "{ \"long\" } else { \"hello {n}\" }",
        "{ s } else { \"hi {n}\" }",
    );
    engine.write("main.lt", &consumed);
    run.wait("the patched output", |out, err| {
        out.contains("hi ") && err.contains("stilt: patched 2 functions")
    });
}

#[test]
fn runs_and_a_check_at_once_each_work() {
    let engine = Engine::with("run_at_once", 60, &[("main.lt", FOREVER)]);
    let runs: Vec<Running> = (0..2)
        .map(|i| Running::start(&engine, &format!("run{i}")))
        .collect();
    for run in &runs {
        run.wait("the first output", |out, _| out.contains("hello 1 "));
    }
    engine.write("main.lt", &FOREVER.replace("\"hello {n}\"", "\"hi {n}\""));
    let checks: Vec<Child> = (0..2)
        .map(|_| {
            stilt(&engine.dir)
                .args(["check", "--json", "."])
                .stdout(Stdio::piped())
                .spawn()
                .expect("stilt runs")
        })
        .collect();
    for run in &runs {
        run.wait("the patched output", |out, err| {
            out.contains("hi ") && err.contains("stilt: patched 1 function")
        });
    }
    let (_, alone) = engine.both(&["check", "--json", "."]);
    for check in checks {
        let output = check.wait_with_output().expect("stilt runs");
        assert_eq!(output.stdout, alone.stdout);
    }
}
