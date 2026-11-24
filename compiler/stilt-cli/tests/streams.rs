//! A program's streams, read and written through pipes while it runs (program.output-flushing;
//! std.io), which the conformance suite can't see, since its protocol gives stdin whole and
//! captures stdout whole. A line that a program prints reaches its reader when `print` returns, and
//! text that `io.flush()` writes out when it returns, while the program goes on; and
//! `io.poll_line()` gives `None` while no line waits on standard input, without waiting, and each
//! line once it is written, the lines that one read of the system brought among them. `stilt run`
//! and an executable that `stilt build` writes behave alike, and so does `stilt test`, whose
//! tests print to standard error (program.running-tests). A program whose standard output is
//! closed ends with status 141 (program.exit-statuses).

use std::fs;
use std::io::{Read, Write as _};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

/// How long a test waits for the program to write what it expects.
const PATIENCE: Duration = Duration::from_secs(30);

/// The least time between two pieces of output that a program writes 500 ms apart: a piece
/// that arrives closer to the next was held back.
const APART: Duration = Duration::from_millis(250);

/// How a program is run.
#[derive(Clone, Copy)]
enum How {
    Run,
    Built,
    Test,
}

/// The program `source`, written to a file of its own.
fn program(name: &str, source: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("streams")
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("the directory can be made");
    let file = dir.join("main.lt");
    fs::write(&file, source).expect("the program can be written");
    file
}

/// Starts the program at `file` as `how` says, with its standard input piped, and the stream
/// its output goes to: standard output, or under `stilt test` standard error.
fn start(file: &Path, how: How) -> (Child, Box<dyn Read + Send>) {
    let stilt = env!("CARGO_BIN_EXE_stilt");
    let mut command = match how {
        How::Run | How::Test => {
            let mut command = Command::new(stilt);
            command.arg(if matches!(how, How::Run) {
                "run"
            } else {
                "test"
            });
            command.arg(file);
            command
        }
        How::Built => {
            let exe = file.with_file_name("program");
            let built = Command::new(stilt)
                .arg("build")
                .arg("-o")
                .arg(&exe)
                .arg(file)
                .output()
                .expect("stilt runs");
            assert!(built.status.success(), "{built:?}");
            Command::new(exe)
        }
    };
    command.stdin(Stdio::piped());
    if matches!(how, How::Test) {
        command.stdout(Stdio::null()).stderr(Stdio::piped());
    } else {
        command.stdout(Stdio::piped()).stderr(Stdio::inherit());
    }
    let mut child = command.spawn().expect("the program runs");
    let stream: Box<dyn Read + Send> = match how {
        How::Test => Box::new(child.stderr.take().expect("stderr is piped")),
        How::Run | How::Built => Box::new(child.stdout.take().expect("stdout is piped")),
    };
    (child, stream)
}

/// What a stream gives, with the time each piece of it arrived.
struct Arrivals {
    pieces: mpsc::Receiver<(Instant, Vec<u8>)>,
    seen: Vec<u8>,
    /// Where each piece ends in `seen`, and when it arrived.
    ends: Vec<(usize, Instant)>,
    /// Where the text that the next [`Arrivals::until`] looks for may start.
    mark: usize,
}

impl Arrivals {
    fn read(mut stream: Box<dyn Read + Send>) -> Self {
        let (send, pieces) = mpsc::channel();
        thread::spawn(move || {
            let mut buf = [0; 4096];
            while let Ok(n @ 1..) = stream.read(&mut buf) {
                if send.send((Instant::now(), buf[..n].to_vec())).is_err() {
                    break;
                }
            }
        });
        Self {
            pieces,
            seen: Vec::new(),
            ends: Vec::new(),
            mark: 0,
        }
    }

    /// When `text` arrived, after the text the last call found, which fails the test if it
    /// never does.
    fn until(&mut self, text: &str) -> Instant {
        let deadline = Instant::now() + PATIENCE;
        loop {
            let found = self.seen[self.mark..]
                .windows(text.len())
                .position(|w| w == text.as_bytes());
            if let Some(at) = found {
                let last = self.mark + at + text.len() - 1;
                self.mark = last + 1;
                let (_, time) = self
                    .ends
                    .iter()
                    .find(|(end, _)| *end > last)
                    .expect("a piece");
                return *time;
            }
            let left = deadline.saturating_duration_since(Instant::now());
            let Ok((time, piece)) = self.pieces.recv_timeout(left) else {
                panic!(
                    "never saw {text:?}, only {:?}",
                    String::from_utf8_lossy(&self.seen)
                );
            };
            self.seen.extend(piece);
            self.ends.push((self.seen.len(), time));
        }
    }
}

/// A search that reports each depth as it finishes it, the second without a newline.
const SEARCH: &str = "  print(\"depth 1\")\n  clock.sleep_ms(500)\n  io.write(\"depth 2\")\n  io.flush()\n  clock.sleep_ms(500)\n  print(\" done\")\n";

/// Runs [`SEARCH`] as `how` says, and checks that each depth arrives while the program sleeps.
fn progress_arrives_while_the_program_sleeps(name: &str, how: How) {
    let head = "use std.clock\nuse std.io\n\n";
    let source = match how {
        How::Test => format!("{head}test \"searches\" {{\n{SEARCH}}}\n"),
        How::Run | How::Built => format!("{head}fn main() / io {{\n{SEARCH}}}\n"),
    };
    let (mut child, stream) = start(&program(name, &source), how);
    let mut out = Arrivals::read(stream);
    let first = out.until("depth 1\n");
    let second = out.until("depth 2");
    let last = out.until(" done\n");
    assert!(
        second.duration_since(first) >= APART,
        "the line printed before the sleep arrived {:?} before the next output",
        second.duration_since(first)
    );
    assert!(
        last.duration_since(second) >= APART,
        "the text written out by `io.flush()` arrived {:?} before the next output",
        last.duration_since(second)
    );
    assert!(child.wait().expect("the program ends").success());
}

#[test]
fn a_line_printed_before_a_sleep_arrives_while_the_run_sleeps() {
    progress_arrives_while_the_program_sleeps("run", How::Run);
}

#[test]
fn a_line_printed_before_a_sleep_arrives_while_the_built_program_sleeps() {
    progress_arrives_while_the_program_sleeps("built", How::Built);
}

#[test]
fn a_line_a_test_prints_before_a_sleep_arrives_while_the_test_sleeps() {
    progress_arrives_while_the_program_sleeps("test", How::Test);
}

/// A program that polls standard input until it reads `stop`, printing each line it gets, and
/// once that nothing was waiting.
const POLL: &str = "use std.clock\nuse std.io\n\nfn main() / io {\n  var waited = false\n  loop {\n    match io.poll_line() {\n      Some(line) => {\n        print(\"got {line}\")\n        if line == \"stop\" { break }\n      }\n      None => {\n        if !waited {\n          print(\"nothing yet\")\n          waited = true\n        }\n        clock.sleep_ms(5)\n      }\n    }\n  }\n}\n";

/// Runs [`POLL`] as `how` says: it gets `None` while nothing is written to it and while only
/// part of a line is, and then each line, those that arrived together among them, with its
/// standard input still open.
fn poll_line_gets_each_line_once_written(name: &str, how: How) {
    let (mut child, stream) = start(&program(name, POLL), how);
    let mut stdin = child.stdin.take().expect("stdin is piped");
    let mut out = Arrivals::read(stream);
    out.until("nothing yet\n");
    stdin.write_all(b"par").expect("the program reads stdin");
    stdin.flush().expect("the program reads stdin");
    thread::sleep(Duration::from_millis(300));
    stdin
        .write_all(b"tial\none\nstop\n")
        .expect("the program reads stdin");
    stdin.flush().expect("the program reads stdin");
    out.until("got partial\ngot one\ngot stop\n");
    assert!(child.wait().expect("the program ends").success());
    assert_eq!(
        String::from_utf8_lossy(&out.seen),
        "nothing yet\ngot partial\ngot one\ngot stop\n"
    );
    drop(stdin);
}

#[test]
fn poll_line_gives_none_until_a_line_is_written_to_the_run() {
    poll_line_gets_each_line_once_written("poll-run", How::Run);
}

#[test]
fn poll_line_gives_none_until_a_line_is_written_to_the_built_program() {
    poll_line_gets_each_line_once_written("poll-built", How::Built);
}

/// A program that prints a line every 10 ms forever, after starting a child when `spawns` is
/// set, which makes the runtime ignore the signal of a broken pipe.
fn printer(name: &str, spawns: bool) -> PathBuf {
    let child = if spawns {
        "  let _ = Result.of(|| try process.run(\"true\", []))\n"
    } else {
        ""
    };
    program(
        name,
        &format!(
            "use std.clock\nuse std.process\n\nfn main() / io {{\n{child}  var n = 0\n  loop {{\n    print(\"{{n}}\")\n    n += 1\n    clock.sleep_ms(10)\n  }}\n}}\n"
        ),
    )
}

/// A program whose standard output is closed while it prints ends with status 141, however it
/// runs (program.exit-statuses).
fn a_closed_output_ends_the_program(name: &str, how: How, spawns: bool) {
    let (mut child, mut stream) = start(&printer(name, spawns), how);
    let mut first = [0; 2];
    stream.read_exact(&mut first).expect("the program prints");
    drop(stream);
    let deadline = Instant::now() + PATIENCE;
    let status = loop {
        if let Some(status) = child.try_wait().expect("the program can be waited for") {
            break status;
        }
        assert!(Instant::now() < deadline, "the program went on printing");
        thread::sleep(Duration::from_millis(10));
    };
    assert_eq!(status.code(), Some(141), "{status:?}");
}

#[test]
fn a_run_whose_output_is_closed_ends_with_141() {
    a_closed_output_ends_the_program("closed_run", How::Run, false);
}

#[test]
fn a_built_program_whose_output_is_closed_ends_with_141() {
    a_closed_output_ends_the_program("closed_built", How::Built, false);
    a_closed_output_ends_the_program("closed_built_spawning", How::Built, true);
}
