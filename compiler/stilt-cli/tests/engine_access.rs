//! Who an engine answers (engines.private and engines.toolchains): the user who started it,
//! through a directory and a socket that no other user may open, and commands of its own build
//! of the compiler. Each test's commands find their engines' directory in a temporary directory
//! of the test's own.

use std::fs::{self, Permissions};
use std::os::unix::fs::{FileTypeExt as _, MetadataExt as _, PermissionsExt as _};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{Duration, Instant};

mod common;

const MAIN: &str =
    "use shapes\n\nfn main() / io {\n  print(\"{shapes.area(shapes.Square(3))}\")\n}\n";
const SHAPES: &str = "pub type Shape = | Square(i64) | Rect(i64, i64)\n\npub fn area(s: Shape) -> i64 {\n  match s {\n    Square(n) => n * n\n    Rect(w, h) => w * h\n  }\n}\n";

/// The compiler under test.
const STILT: &str = env!("CARGO_BIN_EXE_stilt");

/// A directory program with a temporary directory of its own, whose engines, started by any
/// of `exes`, are stopped when this is dropped.
struct Program {
    dir: PathBuf,
    tmp: PathBuf,
    exes: Vec<PathBuf>,
}

impl Program {
    /// The paths are kept short, since a socket's path is limited to about a hundred bytes.
    fn new(name: &str) -> Self {
        let dir = common::project("access", name, &[("main.lt", MAIN), ("shapes.lt", SHAPES)]);
        let tmp = common::directory("access", &format!("{name}.t"));
        Self {
            dir: dir.canonicalize().expect("the directory exists"),
            tmp,
            exes: vec![PathBuf::from(STILT)],
        }
    }

    /// The directory of the user's engines that the program's commands use.
    fn engines_dir(&self) -> PathBuf {
        self.tmp.join(format!("stilt-{}", common::user()))
    }

    /// `exe ARGS` on the program, with the test's temporary directory.
    fn command(&self, exe: &Path, args: &[&str]) -> Output {
        Command::new(exe)
            .current_dir(&self.dir)
            .env("TMPDIR", &self.tmp)
            .args(args)
            .output()
            .expect("stilt runs")
    }

    /// The command lines of the engines that hold the program.
    fn engines(&self) -> Vec<String> {
        let listing = Command::new("ps")
            .args(["-axo", "command="])
            .output()
            .expect("ps runs");
        let mark = format!(" engine {}", self.dir.display());
        String::from_utf8_lossy(&listing.stdout)
            .lines()
            .filter(|line| line.ends_with(&mark))
            .map(str::to_owned)
            .collect()
    }

    /// Waits until `done` holds of the engines that hold the program.
    fn wait_for(&self, what: &str, done: impl Fn(&[String]) -> bool) {
        let since = Instant::now();
        while !done(&self.engines()) {
            assert!(since.elapsed() < Duration::from_secs(10), "{what}");
            std::thread::sleep(Duration::from_millis(20));
        }
    }
}

impl Drop for Program {
    fn drop(&mut self) {
        for exe in &self.exes {
            let _ = self.command(exe, &["engine", "--stop", "."]);
        }
    }
}

fn mode(path: &Path) -> u32 {
    fs::symlink_metadata(path).expect("the entry exists").mode() & 0o777
}

#[test]
fn the_engines_directory_and_socket_are_open_to_the_user_alone() {
    let program = Program::new("closed");
    let checked = program.command(Path::new(STILT), &["check", "."]);
    assert!(checked.status.success(), "{checked:?}");
    assert_eq!(program.engines().len(), 1, "the check started an engine");
    let dir = program.engines_dir();
    let meta = fs::symlink_metadata(&dir).expect("the directory exists");
    assert!(meta.is_dir());
    assert_eq!(meta.uid(), common::user(), "the user owns it");
    assert_eq!(mode(&dir), 0o700, "no other user may open it");
    let sockets: Vec<PathBuf> = fs::read_dir(&dir)
        .expect("the directory can be read")
        .map(|entry| entry.expect("an entry").path())
        .filter(|path| fs::symlink_metadata(path).is_ok_and(|meta| meta.file_type().is_socket()))
        .collect();
    assert_eq!(sockets.len(), 1, "one engine listens: {sockets:?}");
    assert_eq!(mode(&sockets[0]), 0o600, "the socket is the user's alone");
}

#[test]
fn a_directory_that_others_may_open_is_closed_before_an_engine_listens_there() {
    let program = Program::new("open");
    let dir = program.engines_dir();
    fs::create_dir(&dir).expect("the directory can be made");
    fs::set_permissions(&dir, Permissions::from_mode(0o777)).expect("it can be opened");
    let ran = program.command(Path::new(STILT), &["run", "."]);
    assert!(ran.status.success(), "{ran:?}");
    assert_eq!(common::stdout(&ran), "9\n");
    assert_eq!(mode(&dir), 0o700, "the command closed it");
    assert_eq!(program.engines().len(), 1, "an engine answered the run");
}

#[test]
fn a_command_uses_no_engine_where_the_directory_is_a_link() {
    let program = Program::new("link");
    let elsewhere = program.tmp.join("elsewhere");
    fs::create_dir(&elsewhere).expect("the directory can be made");
    fs::set_permissions(&elsewhere, Permissions::from_mode(0o700)).expect("it can be closed");
    let dir = program.engines_dir();
    std::os::unix::fs::symlink(&elsewhere, &dir).expect("the link can be made");
    let ran = program.command(Path::new(STILT), &["run", "."]);
    assert!(ran.status.success(), "{ran:?}");
    assert_eq!(
        common::stdout(&ran),
        "9\n",
        "the command ran in its own process"
    );
    assert_eq!(
        common::stderr(&ran),
        format!(
            "stilt: {} isn't a directory, so the command runs without an engine\n",
            dir.display()
        )
    );
    assert!(program.engines().is_empty(), "no engine started");
    let listed = fs::read_dir(&elsewhere).expect("it can be read").count();
    assert_eq!(listed, 0, "nothing was made through the link");
    let served = program.command(Path::new(STILT), &["engine", "."]);
    assert!(!served.status.success(), "{served:?}");
    assert!(
        common::stderr(&served).contains("isn't a directory"),
        "{served:?}"
    );
}

#[test]
fn a_command_of_another_build_runs_alone_and_stops_the_engine() {
    let mut program = Program::new("twin");
    // A second link to the executable is another build to the engine: the same version, at
    // another path.
    let twin = program.tmp.join("stilt-twin");
    fs::hard_link(STILT, &twin).expect("the executable can be linked");
    program.exes.push(twin.clone());
    let checked = program.command(Path::new(STILT), &["check", "."]);
    assert!(checked.status.success(), "{checked:?}");
    assert_eq!(program.engines().len(), 1, "the check started an engine");
    let ran = program.command(&twin, &["run", "."]);
    assert!(ran.status.success(), "{ran:?}");
    assert_eq!(common::stdout(&ran), "9\n");
    assert_eq!(common::stderr(&ran), "", "the command says nothing of it");
    program.wait_for("the engine stops", <[String]>::is_empty);
    let checked = program.command(&twin, &["check", "."]);
    assert!(checked.status.success(), "{checked:?}");
    let started = format!("{} engine ", twin.display());
    program.wait_for(
        "the next command starts an engine of its build",
        |engines| engines.len() == 1 && engines[0].starts_with(&started),
    );
}
