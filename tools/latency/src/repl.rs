//! `repl`: a session of the REPL on a project, through `stilt run` in the project's directory, as
//! a person types it (goal interactive-evaluation). Its inputs are the `let`s of the project's
//! `main` that name none of `main`'s variables, each timed from the end of its line to the first
//! line of its answer, on stdout or stderr, by the cycles of the session and the engine (Goals,
//! Timing). After each, an input that answers a string of its own
//! tells where its answer ends, untimed, as does one before the first, which waits for the session
//! to start.

use std::io::{BufRead, BufReader, Read, Write as _};
use std::path::Path;
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{Receiver, Sender, channel};
use std::time::Duration;

use crate::clock::Clock;

/// How long the harness waits for an answer.
const PATIENCE: Duration = Duration::from_secs(300);

/// A line the session wrote, and whether on stdout.
type Line = (bool, String);

/// A session of `stilt repl`.
struct Session {
    child: Child,
    input: ChildStdin,
    lines: Receiver<Line>,
}

impl Session {
    fn start(stilt: &Path, project: &Path) -> Result<Self, String> {
        // The session runs in the project's directory, which a relative path doesn't name from.
        let stilt = stilt
            .canonicalize()
            .map_err(|e| format!("{}: {e}", stilt.display()))?;
        let mut child = Command::new(&stilt)
            .arg("repl")
            .current_dir(project)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| format!("cannot start {}: {e}", stilt.display()))?;
        let input = child.stdin.take().ok_or("no stdin")?;
        let (to_out, lines) = channel();
        let out = child.stdout.take().ok_or("no stdout")?;
        let err = child.stderr.take().ok_or("no stderr")?;
        let to_err = to_out.clone();
        std::thread::spawn(move || read_all(out, true, &to_out));
        std::thread::spawn(move || read_all(err, false, &to_err));
        Ok(Self {
            child,
            input,
            lines,
        })
    }

    /// Writes an input.
    fn write(&mut self, line: &str) -> Result<(), String> {
        writeln!(self.input, "{line}")
            .and_then(|()| self.input.flush())
            .map_err(|e| format!("cannot write to the session: {e}"))
    }

    /// The next line the session writes.
    fn next(&self) -> Result<Line, String> {
        self.lines
            .recv_timeout(PATIENCE)
            .map_err(|_| "the session stopped answering".to_owned())
    }

    /// Writes the input that answers the string `#sync{n}`, and reads every line up to its
    /// answer.
    fn sync(&mut self, n: usize) -> Result<(), String> {
        let answer = format!("\"#sync{n}\": str");
        self.write(&format!("\"#sync{n}\""))?;
        while self.next()?.1 != answer {}
        Ok(())
    }
}

fn read_all(stream: impl Read, out: bool, send: &Sender<Line>) {
    for line in BufReader::new(stream).lines() {
        let Ok(line) = line else { return };
        if send.send((out, line)).is_err() {
            return;
        }
    }
}

/// The `let`s of the project's `main` that name none of its variables, at most `count`.
fn inputs(project: &Path, count: usize) -> Result<Vec<String>, String> {
    let path = project.join("main.lt");
    let text = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    let inputs = text
        .lines()
        .filter_map(|line| line.strip_prefix("  let "))
        .filter(|rest| {
            let value = rest.split_once(" = ").map_or("", |(_, v)| v);
            !value.contains("inout ") && !names_a_variable(value)
        })
        .map(|rest| format!("let {rest}"))
        .take(count)
        .collect();
    Ok(inputs)
}

/// Whether the text names one of `main`'s variables, which the generator names `vN`, `aN` and
/// `rN`.
fn names_a_variable(text: &str) -> bool {
    text.split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        .any(|word| {
            let digits = word.get(1..).unwrap_or("");
            matches!(word.chars().next(), Some('v' | 'a' | 'r'))
                && !digits.is_empty()
                && digits.bytes().all(|b| b.is_ascii_digit())
        })
}

/// Times a session of the REPL on the project, prints the times, and gives the target they miss:
/// interactive-evaluation, an answer under 100 ms at the 95th percentile.
pub(crate) fn measure(stilt: &Path, project: &Path, count: usize) -> Result<Vec<String>, String> {
    let mut times = replay(stilt, project, count)?;
    times.sort();
    let Some(&slowest) = times.last() else {
        return Err(format!("{} has no input to time", project.display()));
    };
    let p95 = crate::percentile(&times, 95);
    println!(
        "a session of the REPL on {}: {} inputs, answered in {:.1} ms at the median, {:.1} ms \
         at the 95th percentile and {:.1} ms at most",
        project.display(),
        times.len(),
        crate::millis(crate::percentile(&times, 50)),
        crate::millis(p95),
        crate::millis(slowest),
    );
    if p95 >= crate::INTERACTIVE_EVALUATION {
        let p95 = crate::millis(p95);
        return Ok(vec![format!(
            "interactive-evaluation: an input takes {p95:.1} ms to answer at the 95th percentile"
        )]);
    }
    Ok(Vec::new())
}

/// Times each input of a session on the project, and gives each time, in order.
fn replay(stilt: &Path, project: &Path, count: usize) -> Result<Vec<Duration>, String> {
    let inputs = inputs(project, count)?;
    let mut session = Session::start(stilt, project)?;
    session.sync(0)?;
    let mut times = Vec::new();
    for (n, input) in (1..).zip(inputs) {
        let clock = Clock::of_client(session.child.id(), project);
        session.write(&input)?;
        session.next()?;
        times.push(clock.elapsed());
        session.sync(n)?;
    }
    drop(session.input);
    let _ = session.child.wait();
    let _ = Command::new(stilt)
        .args(["engine", "--stop"])
        .arg(project)
        .output();
    Ok(times)
}
