//! A command's side: it finds the program's engine, or starts one, and asks it.

use std::io;
use std::os::unix::net::UnixStream;
use std::os::unix::process::CommandExt as _;
use std::path::Path;
use std::process::{Child, ExitCode, Stdio};
use std::time::{Duration, Instant};

use super::place::{Place, identity};
use super::wire::{Look, Reply, Request, receive, send, send_request};
use super::{Answer, Command, Query};
use crate::repl::{self, Ask, Opened};
use crate::report::Report;
use crate::run::{Start, Update};
use crate::test::Plan;

/// How long a command waits for an engine it started to listen.
const START: Duration = Duration::from_secs(30);

/// How many engines a command starts, when each ends before it listens.
const STARTS: usize = 3;

/// How long `stilt engine --stop` waits for the engine to end.
const STOP: Duration = Duration::from_secs(10);

/// The report of `command` on the program at `path`, from the program's engine, or `None`
/// when no engine answers it, so that the command runs in this process.
pub(crate) fn ask(path: &Path, command: &Command) -> Option<Report> {
    match exchange(&connect(path)?, command) {
        Some(Reply::Report(report)) => Some(report),
        _ => None,
    }
}

/// The answer of the program's engine to the language server's `query`, a program of one file
/// included, with the engine's process id, or `None` when no engine answers.
pub(crate) fn language(path: &Path, query: &Query) -> Option<(u32, Answer)> {
    match exchange(&open(path)?, &Command::Language(query.clone())) {
        Some(Reply::Language { engine, answer }) => Some((engine, answer)),
        _ => None,
    }
}

/// A run's connection to the program's engine, which answers each look at the program's
/// files with what the edits since the last look change in the run.
#[derive(Debug)]
pub(crate) struct Remote {
    stream: UnixStream,
}

impl Remote {
    /// What starting the program at `path` needs, from the program's engine, with the
    /// connection that takes the run's looks, or `None` when no engine answers, so that the
    /// run holds the program itself.
    pub(crate) fn start(path: &Path) -> Option<(Self, Start)> {
        let stream = connect(path)?;
        match exchange(&stream, &Command::Run) {
            Some(Reply::Started(start)) => Some((Self { stream }, start)),
            _ => None,
        }
    }

    /// What the edits since the last look change in the run, or an error once the engine is
    /// gone.
    pub(crate) fn look(&self) -> io::Result<Update> {
        send(&self.stream, &Look)?;
        receive(&self.stream)
    }
}

/// A session of the REPL's connection to the program's engine, which holds the session's front
/// and answers each of its asks (`crate::repl`).
#[derive(Debug)]
pub(crate) struct Repl {
    stream: UnixStream,
}

impl Repl {
    /// What the session on the program at `path` reports first, from the program's engine,
    /// with the connection that takes its asks, or `None` when no engine answers, so that the
    /// session holds the program itself.
    pub(crate) fn open(path: &Path) -> Option<(Self, Opened)> {
        let stream = connect(path)?;
        match exchange(&stream, &Command::Repl) {
            Some(Reply::Opened(opened)) => Some((Self { stream }, opened)),
            _ => None,
        }
    }

    /// The front's answer to `ask`, or an error once the engine is gone.
    pub(crate) fn ask(&self, ask: &Ask) -> io::Result<repl::Answer> {
        send(&self.stream, ask)?;
        receive(&self.stream)
    }
}

/// A run of tests' connection to the program's engine, which takes the tests' results.
#[derive(Debug)]
pub(crate) struct Tests {
    stream: UnixStream,
}

impl Tests {
    /// What running the tests of the program at `path` needs, from the program's engine, a
    /// program of one file included, with the connection that takes their results, or `None`
    /// when no engine answers, so that `test` holds the program itself.
    pub(crate) fn plan(path: &Path, json: bool) -> Option<(Self, Plan)> {
        let stream = open(path)?;
        match exchange(&stream, &Command::Test { json }) {
            Some(Reply::Tested(plan)) => Some((Self { stream }, plan)),
            _ => None,
        }
    }

    /// Tells the engine the result of each case, and waits until it remembers them.
    pub(crate) fn record(&self, results: &[crate::test::Ran]) {
        if send(&self.stream, &results).is_ok() {
            let _ = receive::<Reply>(&self.stream);
        }
    }
}

/// A connection to the engine of the program at `path`: to the one that runs, or to one
/// started for it. A program of one file has none for the commands but `test` (goal
/// one-engine), and neither has a program whose engine can't start.
fn connect(path: &Path) -> Option<UnixStream> {
    if !path.is_dir() {
        return None;
    }
    open(path)
}

/// A connection to the engine of the program at `path`, of one file or not. A command whose
/// user's directory of engines can't be made private uses none, and says why
/// (engines.private).
fn open(path: &Path) -> Option<UnixStream> {
    let place = Place::of(path)?;
    if let Err(why) = place.private() {
        eprintln!("stilt: {why}, so the command runs without an engine");
        return None;
    }
    place.connect().or_else(|| start(&place))
}

fn exchange(stream: &UnixStream, command: &Command) -> Option<Reply> {
    let request = Request {
        identity: identity(),
        command: command.clone(),
    };
    send_request(stream, &request).ok()?;
    receive(stream).ok()
}

/// Starts an engine for the program, in a process group of its own so that it outlives the
/// command and a terminal's interrupt, and connects to it once it listens. Several commands
/// may start an engine at once: the lock file lets one engine hold the program, the others
/// end at once, and every command connects to the one that holds it. A command that finds no
/// engine, none starting and the last one gone, as when the one it found was ending, starts
/// another, up to [`STARTS`] in all.
fn start(place: &Place) -> Option<UnixStream> {
    let mut started = Vec::new();
    let stream = start_into(place, &mut started);
    reap(started);
    stream
}

fn start_into(place: &Place, started: &mut Vec<Child>) -> Option<UnixStream> {
    let since = Instant::now();
    loop {
        if let Some(stream) = place.connect() {
            return Some(stream);
        }
        let loading = started
            .last_mut()
            .is_some_and(|child| child.try_wait().is_ok_and(|status| status.is_none()));
        if !loading && !place.held() {
            if started.len() == STARTS {
                return None;
            }
            started.push(spawn(place)?);
        }
        if since.elapsed() > START {
            return None;
        }
        std::thread::sleep(Duration::from_millis(5));
    }
}

/// Waits for the engines a command started, on a thread of its own, so that an engine that
/// ends while the command goes on, as the language server's does once it has idled, leaves
/// no process behind for the system to keep.
fn reap(started: Vec<Child>) {
    if !started.is_empty() {
        std::thread::spawn(move || {
            for mut child in started {
                let _ = child.wait();
            }
        });
    }
}

/// Starts the engine of `place`, its errors written to the place's log, which a bug's note
/// names (`crate::bug`).
fn spawn(place: &Place) -> Option<Child> {
    let log = std::fs::File::create(&place.log).map_or_else(|_| Stdio::null(), Stdio::from);
    std::process::Command::new(std::env::current_exe().ok()?)
        .arg("engine")
        .arg(&place.program)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(log)
        .process_group(0)
        .spawn()
        .ok()
}

/// Stops the engine of the program at `path`, and waits for it to end. The status is 1 when
/// no engine runs.
pub(crate) fn stop(path: &Path) -> ExitCode {
    let Some(place) = Place::of(path) else {
        return Report::refuse(&format!("{} doesn't exist", path.display())).print();
    };
    let Some(stream) = place.connect() else {
        eprintln!("stilt: no engine holds {}", path.display());
        return ExitCode::from(1);
    };
    let _ = exchange(&stream, &Command::Stop);
    let since = Instant::now();
    while place.held() && since.elapsed() < STOP {
        std::thread::sleep(Duration::from_millis(5));
    }
    ExitCode::SUCCESS
}

/// Prints the queries that the engine of the program at `path` has run since this was last
/// asked, one a line. The status is 1 when no engine runs.
pub(crate) fn ran(path: &Path) -> ExitCode {
    let stream = Place::of(path).and_then(|place| place.connect());
    if let Some(Reply::Ran(queries)) = stream.and_then(|stream| exchange(&stream, &Command::Ran)) {
        for query in queries {
            println!("{query}");
        }
        ExitCode::SUCCESS
    } else {
        eprintln!("stilt: no engine holds {}", path.display());
        ExitCode::from(1)
    }
}
