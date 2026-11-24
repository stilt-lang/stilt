//! Engines that commands start (goal one-engine): the first command on a directory program
//! starts its engine and the next uses it, a program of one file has none, commands that
//! start at once start one, and an engine that ends before the command that started it, as the
//! language server's ends once idle, leaves no process behind.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::time::{Duration, Instant};

const MAIN: &str =
    "use shapes\n\nfn main() / io {\n  print(\"{shapes.area(shapes.Square(3))}\")\n}\n";
const SHAPES: &str = "pub type Shape = | Square(i64) | Rect(i64, i64)\n\npub fn area(s: Shape) -> i64 {\n  match s {\n    Square(n) => n * n\n    Rect(w, h) => w * h\n  }\n}\n";
/// A program of one file.
const ONE_FILE: &str = "fn main() / io {\n  print(\"9\")\n}\n";

fn stilt(dir: &Path) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_stilt"));
    command.current_dir(dir);
    command
}

/// A program in a directory of its own, with no engine, whose commands start one; the engines
/// of the program are stopped when this is dropped.
struct Fresh {
    dir: PathBuf,
}

impl Fresh {
    fn new(name: &str, files: &[(&str, &str)]) -> Self {
        let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
            .join("engine")
            .join(name);
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("the directory can be made");
        for (file, text) in files {
            fs::write(dir.join(file), text).expect("the program can be written");
        }
        Self {
            dir: dir.canonicalize().expect("the directory exists"),
        }
    }

    /// The processes of the engines that hold the program, by id.
    fn engines(&self) -> Vec<String> {
        let listing = Command::new("ps")
            .args(["-axo", "pid=,command="])
            .output()
            .expect("ps runs");
        let mark = format!(" engine {}", self.dir.display());
        String::from_utf8_lossy(&listing.stdout)
            .lines()
            .filter(|line| line.contains(&mark))
            .map(|line| {
                line.split_whitespace()
                    .next()
                    .unwrap_or_default()
                    .to_owned()
            })
            .collect()
    }

    fn run(&self, args: &[&str]) -> Output {
        let output = stilt(&self.dir).args(args).output().expect("stilt runs");
        assert!(output.status.success(), "{output:?}");
        output
    }
}

impl Drop for Fresh {
    fn drop(&mut self) {
        let _ = stilt(&self.dir).args(["engine", "--stop", "."]).output();
    }
}

#[test]
fn a_command_on_a_directory_program_starts_an_engine_that_the_next_uses() {
    let program = Fresh::new("started", &[("main.lt", MAIN), ("shapes.lt", SHAPES)]);
    assert_eq!(program.engines().len(), 0);
    program.run(&["check", "."]);
    let engines = program.engines();
    assert_eq!(engines.len(), 1, "the check started an engine");
    program.run(&["build", "-o", "program", "."]);
    program.run(&["show", "shapes.area", "."]);
    program.run(&["run", "."]);
    assert_eq!(program.engines(), engines, "every command used that engine");
    let stopped = stilt(&program.dir)
        .args(["engine", "--stop", "."])
        .output()
        .expect("stilt runs");
    assert!(stopped.status.success(), "{stopped:?}");
    assert!(program.engines().is_empty(), "the engine stopped");
}

#[test]
fn a_program_of_one_file_starts_no_engine() {
    let program = Fresh::new("one_file", &[("main.lt", ONE_FILE)]);
    program.run(&["check", "main.lt"]);
    program.run(&["build", "-o", "program", "main.lt"]);
    program.run(&["show", "main", "main.lt"]);
    let run = program.run(&["run", "main.lt"]);
    assert_eq!(String::from_utf8_lossy(&run.stdout), "9\n");
    assert_eq!(program.engines().len(), 0, "no engine runs");
    let stopped = stilt(&program.dir)
        .args(["engine", "--stop", "main.lt"])
        .output()
        .expect("stilt runs");
    assert!(!stopped.status.success(), "no engine holds the file");
}

/// The processes whose parent is `parent` and that have ended without being waited for.
fn ended_children(parent: u32) -> usize {
    let listing = Command::new("ps")
        .args(["-axo", "ppid=,stat="])
        .output()
        .expect("ps runs");
    String::from_utf8_lossy(&listing.stdout)
        .lines()
        .filter(|line| {
            let mut fields = line.split_whitespace();
            fields.next() == Some(&parent.to_string())
                && fields.next().is_some_and(|s| s.starts_with('Z'))
        })
        .count()
}

#[test]
fn an_engine_that_ends_before_the_command_that_started_it_leaves_nothing_behind() {
    const WAITS: &str = "use std.io\n\nfn main() / io {\n  print(\"started\")\n  let _ = io.read_line()\n  print(\"done\")\n}\n";
    let program = Fresh::new("ends_first", &[("main.lt", WAITS), ("shapes.lt", SHAPES)]);
    let mut run = stilt(&program.dir)
        .args(["run", "."])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("stilt runs");
    let since = Instant::now();
    while program.engines().is_empty() {
        assert!(
            since.elapsed() < Duration::from_secs(30),
            "the run starts an engine"
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    let stopped = stilt(&program.dir)
        .args(["engine", "--stop", "."])
        .output()
        .expect("stilt runs");
    assert!(stopped.status.success(), "{stopped:?}");
    // The engine has ended; the run, which started it, goes on, and has waited for it.
    let since = Instant::now();
    while ended_children(run.id()) > 0 {
        assert!(
            since.elapsed() < Duration::from_secs(10),
            "the run waits for its engine"
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    drop(run.stdin.take());
    let output = run.wait_with_output().expect("the run ends");
    assert_eq!(String::from_utf8_lossy(&output.stdout), "started\ndone\n");
}

#[test]
fn commands_that_start_at_once_start_one_engine() {
    let program = Fresh::new("start_at_once", &[("main.lt", MAIN), ("shapes.lt", SHAPES)]);
    let commands: Vec<Child> = ["check", "check", "build", "run", "check", "show"]
        .iter()
        .map(|&command| {
            let mut args = vec![command];
            match command {
                "build" => args.extend(["-o", "program"]),
                "show" => args.push("shapes.area"),
                _ => {}
            }
            args.push(".");
            stilt(&program.dir)
                .args(args)
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .spawn()
                .expect("stilt runs")
        })
        .collect();
    for mut command in commands {
        assert!(command.wait().expect("stilt ends").success());
    }
    // An engine that lost the lock ends at once; the one that holds it stays.
    let since = Instant::now();
    while program.engines().len() > 1 {
        assert!(since.elapsed() < Duration::from_secs(10), "one engine runs");
        std::thread::sleep(Duration::from_millis(20));
    }
    assert_eq!(program.engines().len(), 1, "an engine runs");
}
