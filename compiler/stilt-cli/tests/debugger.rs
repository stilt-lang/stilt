//! Debuggers (goal debuggable-builds): lldb and gdb show the source lines and the local variables
//! of a program built by `stilt build`, and of one that `stilt run` compiles in memory, whose
//! code reaches them through the GDB JIT interface. Each test stops at two lines, and checks the
//! locals, the calls under way and a string's contents; others stop at a line of a function
//! inlined, of an instance, and of arrays held in memory, whose elements they show.
//!
//! The tests drive lldb on macOS and gdb on Linux, where `just debuggers` runs them in Docker,
//! with one more that builds the program for x86-64 Linux and runs it under QEMU's emulation,
//! which gdb drives through QEMU's stub.
//!
//! A process that a debugger launches answers for its own file accesses, so on macOS it would
//! ask for access to a protected folder such as the Desktop if the repository lives there. Each
//! test therefore works in the system's temporary directory, which no such rule protects, and
//! runs a copy of `stilt` made there, and removes what it made there when it ends.

use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

/// How long a debugging session may take.
const PATIENCE: Duration = Duration::from_secs(120);

/// A program with a recursive function, whose locals a debugger shows at line 5, and a `main`
/// whose locals of each kind it shows at line 17: a computed `f64` among them, which lives in a
/// float register from its first use on line 16, and a record and an option, each held inline in a
/// local per word (facts.native-allocation), which shows a variant's tag by the variant's name.
const PROGRAM: &str = "fn fib(n: i64) -> i64 {
  if n < 2 { return n }
  let a = fib(n - 1)
  let b = fib(n - 2)
  a + b
}

fn main() / io {
  let name = \"fib\"
  let ratio = 1.5
  let big = true
  let r = fib(10)
  let half = r.to_f64() / 110.0
  let point = Point { x: r, y: 2 }
  let found = [r].get(0)
  print(\"{half}\")
  print(\"{name} {r} {ratio} {big} {half} {point.y} {found else 0}\")
}

type Point = { x: i64, y: i64 }
";

/// A program whose `offset` is small and not recursive, so that a build runs its body in
/// `main`: a debugger stops at line 3 in `main`'s code, on the line of `offset`'s source, and
/// shows `offset`'s local there, since lowering gives each local its name and the line table
/// maps the inlined code to its own lines (goals debug-speed and debuggable-builds).
const INLINED: &str = "fn offset(x: i64) -> i64 {
  let doubled = x * 2
  doubled + 1
}

fn main() / io {
  let a = offset(20)
  let b = offset(a)
  print(\"{a} {b}\")
}
";

/// A program whose generic `pick` is compiled for the layout of a `Point`, two words: a debugger
/// stops at line 3 in that instance and shows its local of the type parameter by the positions
/// of its words (goal inline-values).
const GENERIC: &str = "fn pick<T>(first: bool, a: T, b: T) -> T {
  let chosen = if first { a } else { b }
  chosen
}

fn main() / io {
  let p = pick(false, Point { x: 1, y: 2 }, Point { x: 3, y: 4 })
  print(\"{p.x}\")
}

type Point = { x: i64, y: i64 }
";

/// A program whose arrays are held in memory, one local each (generics.large-arrays): a debugger
/// stops at line 7 and shows an element of each, by its index, and an element's parts.
const ARRAYS: &str = "use std.array

fn main() / io {
  var big: array.Array<i64, 65536> = array.fill(3)
  big[65535] = 9
  let pairs: array.Array<(i64, bool), 10> = array.fill((4, true))
  print(\"{big[65535]} {pairs[2].0}\")
}
";

/// The debugger of the host.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Debugger {
    Lldb,
    Gdb,
}

impl Debugger {
    fn host() -> Self {
        if cfg!(target_os = "macos") {
            Self::Lldb
        } else {
            Self::Gdb
        }
    }

    /// The arguments that run the session's commands, `commands` being the debugger's own.
    fn arguments(self, commands: &[&str]) -> Vec<OsString> {
        let flag = match self {
            Self::Lldb => "-o",
            Self::Gdb => "-ex",
        };
        let mut out: Vec<OsString> = vec!["-batch".into()];
        for c in commands {
            out.push(flag.into());
            out.push((*c).into());
        }
        out
    }

    /// The commands of the session: stop at line 5 and show the locals and the calls under
    /// way, then stop at line 17 and show the locals and a string.
    fn commands(self) -> Vec<&'static str> {
        match self {
            Self::Lldb => vec![
                "settings set plugin.jit-loader.gdb.enable on",
                "breakpoint set --file main.lt --line 5",
                "run",
                "frame variable",
                "bt 3",
                "breakpoint delete 1",
                "breakpoint set --file main.lt --line 17",
                "continue",
                "frame variable",
                "print *name",
                "kill",
            ],
            Self::Gdb => vec![
                "set breakpoint pending on",
                "break main.lt:5",
                "run",
                "info locals",
                "bt 3",
                "delete",
                "break main.lt:17",
                "continue",
                "info locals",
                "print *name",
                "kill",
            ],
        }
    }

    /// What the session must show: the lines it stopped at, each local's value, the caller
    /// with its argument, and the string's bytes.
    fn expected(self) -> &'static [&'static str] {
        match self {
            Self::Lldb => &[
                "at main.lt:5",
                "(i64) a = 1",
                "(i64) b = 0",
                "main.fib(n=3) at main.lt:3",
                "at main.lt:17",
                "(f64) ratio = 1.5",
                "(f64) half = 0.5",
                "(bool) big = true",
                "(i64) r = 55",
                "(i64) point.x = 55",
                "(i64) point.y = 2",
                "(Option<i64>) found = Some",
                "(i64) found.0 = 55",
                "size = 3, bytes = \"fib\"",
            ],
            Self::Gdb => &[
                "main.lt:5",
                "a = 1",
                "b = 0",
                "main.fib (n=3) at",
                "main.lt:17",
                "ratio = 1.5",
                "half = 0.5",
                "big = true",
                "r = 55",
                "point.x = 55",
                "point.y = 2",
                "found = Some",
                "found.0 = 55",
                "size = 3, bytes = ",
                "\"fib\"",
            ],
        }
    }
}

/// A path of this run's in the system's temporary directory, removed with all it holds when
/// dropped, so that a test leaves nothing there, whether it passes or fails.
struct Scratch(PathBuf);

impl Scratch {
    fn new(name: &str) -> Self {
        let id = std::process::id();
        Scratch(std::env::temp_dir().join(format!("stilt-debugger-{id}-{name}")))
    }
}

impl std::ops::Deref for Scratch {
    type Target = Path;
    fn deref(&self) -> &Path {
        &self.0
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0).or_else(|_| fs::remove_file(&self.0));
    }
}

/// Writes the program to a directory of its own, and returns the directory.
fn program(name: &str) -> Scratch {
    program_of(name, PROGRAM)
}

/// Writes `source` as the program in a directory of its own, and returns the directory.
fn program_of(name: &str, source: &str) -> Scratch {
    let dir = Scratch::new(name);
    let _ = fs::remove_dir_all(&*dir);
    fs::create_dir_all(&*dir).expect("the directory can be made");
    fs::write(dir.join("main.lt"), source).expect("the program can be written");
    dir
}

/// Runs `command`, and returns what it printed, or fails the test when it takes too long. Each
/// session logs to a file of its own, numbered, since tests run in parallel and two can start
/// at the same instant.
fn output(mut command: Command) -> String {
    static SESSIONS: AtomicUsize = AtomicUsize::new(0);
    let session = SESSIONS.fetch_add(1, Ordering::Relaxed);
    let log = Scratch::new(&format!("session-{session}.log"));
    let file = fs::File::create(&*log).expect("the log can be written");
    let mut child = command
        .stdin(Stdio::null())
        .stdout(file.try_clone().expect("the log can be shared"))
        .stderr(file)
        .spawn()
        .expect("the debugger runs");
    wait(&mut child);
    fs::read_to_string(&*log).unwrap_or_default()
}

fn wait(child: &mut Child) {
    let start = Instant::now();
    while start.elapsed() < PATIENCE {
        if child.try_wait().ok().flatten().is_some() {
            return;
        }
        std::thread::sleep(Duration::from_millis(50));
    }
    let _ = child.kill();
    panic!("the debugging session took over {PATIENCE:?}");
}

fn shows(session: &str, expected: &[&str]) {
    for e in expected {
        assert!(
            session.contains(e),
            "the session doesn't show {e:?}:\n{session}"
        );
    }
}

/// Builds the program at `dir` with `args`, and returns the executable.
fn build(dir: &Path, args: &[&str]) -> PathBuf {
    let exe = dir.join("program");
    let built = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .arg("build")
        .args(args)
        .arg("-o")
        .arg(&exe)
        .arg(dir.join("main.lt"))
        .output()
        .expect("stilt runs");
    assert!(built.status.success(), "{built:?}");
    exe
}

#[test]
#[cfg_attr(
    not(any(
        all(target_os = "macos", target_arch = "aarch64"),
        all(target_os = "linux", target_arch = "x86_64")
    )),
    ignore = "this machine isn't a target of `stilt build`"
)]
fn a_built_program_shows_its_lines_and_locals() {
    let dir = program("built");
    let exe = build(&dir, &[]);
    let debugger = Debugger::host();
    let mut command = Command::new(if debugger == Debugger::Lldb {
        "lldb"
    } else {
        "gdb"
    });
    command
        .args(debugger.arguments(&debugger.commands()))
        .arg(&exe);
    shows(&output(command), debugger.expected());
}

#[test]
fn a_program_run_in_memory_shows_its_lines_and_locals() {
    let dir = program("jit");
    let debugger = Debugger::host();
    let mut command = Command::new(if debugger == Debugger::Lldb {
        "lldb"
    } else {
        "gdb"
    });
    command.args(debugger.arguments(&debugger.commands()));
    match debugger {
        Debugger::Lldb => command.arg("--"),
        Debugger::Gdb => command.arg("--args"),
    };
    // The debugger launches `stilt` itself, so it runs a copy beside the program. The
    // standard library is built into it, so the copy reads nothing else.
    let stilt = dir.join("stilt");
    fs::copy(env!("CARGO_BIN_EXE_stilt"), &stilt).expect("stilt can be copied");
    command.arg(&stilt).arg("run").arg(dir.join("main.lt"));
    shows(&output(command), debugger.expected());
}

/// The program built for x86-64 Linux, run under QEMU's emulation, which gdb drives through
/// QEMU's stub, on a Linux machine of another architecture.
#[test]
#[ignore = "it needs QEMU and gdb-multiarch, which the Linux machine of `just debuggers` has, and runs there"]
fn a_program_built_for_x86_64_linux_shows_its_lines_and_locals_under_emulation() {
    let dir = program("qemu");
    let exe = build(&dir, &["--target", "x86_64-linux"]);
    let port = 20000 + std::process::id() % 20000;
    let mut qemu = Command::new("qemu-x86_64")
        .arg("-g")
        .arg(port.to_string())
        .arg(&exe)
        .stdout(Stdio::null())
        .spawn()
        .expect("QEMU runs");
    std::thread::sleep(Duration::from_secs(1));
    // The program waits for gdb at its first instruction, so `continue` replaces `run`.
    let target = format!("target remote :{port}");
    let mut commands = vec![target.as_str()];
    commands.extend(
        Debugger::Gdb
            .commands()
            .into_iter()
            .map(|c| if c == "run" { "continue" } else { c }),
    );
    let mut command = Command::new("gdb-multiarch");
    command.args(Debugger::Gdb.arguments(&commands)).arg(&exe);
    let session = output(command);
    let _ = qemu.kill();
    let _ = qemu.wait();
    shows(&session, Debugger::Gdb.expected());
}

#[test]
#[cfg_attr(
    not(any(
        all(target_os = "macos", target_arch = "aarch64"),
        all(target_os = "linux", target_arch = "x86_64")
    )),
    ignore = "this machine isn't a target of `stilt build`"
)]
fn a_built_program_stops_at_the_lines_of_a_function_it_inlined() {
    let dir = program_of("inlined", INLINED);
    let exe = build(&dir, &[]);
    let debugger = Debugger::host();
    let (tool, commands, expected): (&str, &[&str], &[&str]) = match debugger {
        Debugger::Lldb => (
            "lldb",
            &[
                "breakpoint set --file main.lt --line 3",
                "run",
                "frame variable",
                "kill",
            ],
            &["at main.lt:3", "(i64) doubled = 40"],
        ),
        Debugger::Gdb => (
            "gdb",
            &["break main.lt:3", "run", "info locals", "kill"],
            &["main.lt:3", "doubled = 40"],
        ),
    };
    let mut command = Command::new(tool);
    command.args(debugger.arguments(commands)).arg(&exe);
    shows(&output(command), expected);
}

#[test]
fn an_instance_run_in_memory_shows_its_locals_by_position() {
    let dir = program_of("instance", GENERIC);
    let debugger = Debugger::host();
    let (tool, commands, expected): (&str, &[&str], &[&str]) = match debugger {
        Debugger::Lldb => (
            "lldb",
            &[
                "settings set plugin.jit-loader.gdb.enable on",
                "breakpoint set --file main.lt --line 3",
                "run",
                "frame variable",
                "bt 1",
                "kill",
            ],
            &[
                "at main.lt:3",
                "chosen.0 = 3",
                "chosen.1 = 4",
                "main.pick<ss>(",
            ],
        ),
        Debugger::Gdb => (
            "gdb",
            &[
                "set breakpoint pending on",
                "break main.lt:3",
                "run",
                "info locals",
                "bt 1",
                "kill",
            ],
            &["main.lt:3", "chosen.0 = 3", "chosen.1 = 4", "main.pick<ss>"],
        ),
    };
    let mut command = Command::new(tool);
    command.args(debugger.arguments(commands));
    match debugger {
        Debugger::Lldb => command.arg("--"),
        Debugger::Gdb => command.arg("--args"),
    };
    let stilt = dir.join("stilt");
    fs::copy(env!("CARGO_BIN_EXE_stilt"), &stilt).expect("stilt can be copied");
    command.arg(&stilt).arg("run").arg(dir.join("main.lt"));
    shows(&output(command), expected);
}

#[test]
fn an_array_held_in_memory_shows_its_elements() {
    let dir = program_of("arrays", ARRAYS);
    let debugger = Debugger::host();
    let (tool, commands, expected): (&str, &[&str], &[&str]) = match debugger {
        Debugger::Lldb => (
            "lldb",
            &[
                "settings set plugin.jit-loader.gdb.enable on",
                "breakpoint set --file main.lt --line 7",
                "run",
                "frame variable big[65535]",
                "frame variable pairs[2]",
                "kill",
            ],
            &[
                "at main.lt:7",
                "big[65535] = 9",
                "pairs[2] = (0 = 4, 1 = true)",
            ],
        ),
        Debugger::Gdb => (
            "gdb",
            &[
                "set breakpoint pending on",
                "break main.lt:7",
                "run",
                "print big[65535]",
                "print pairs[2]",
                "kill",
            ],
            &["main.lt:7", "= 9", "0 = 4, 1 = true"],
        ),
    };
    let mut command = Command::new(tool);
    command.args(debugger.arguments(commands));
    match debugger {
        Debugger::Lldb => command.arg("--"),
        Debugger::Gdb => command.arg("--args"),
    };
    let stilt = dir.join("stilt");
    fs::copy(env!("CARGO_BIN_EXE_stilt"), &stilt).expect("stilt can be copied");
    command.arg(&stilt).arg("run").arg(dir.join("main.lt"));
    shows(&output(command), expected);
}
