//! Code lenses and the jobs they run. A lens runs a job, the program's tests or its `main`, as a
//! process the backend gives, read on threads of its own so the server answers as it runs; the
//! lens of the job running stops it instead. When the process ends, its results show at their
//! lines, beside the lenses, until a file changes, and the run's summary is shown as a message.

use std::collections::HashMap;
use std::io::{self, Read, Write};
use std::path::PathBuf;
use std::process::{Child, Stdio};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use serde_json::{Value, json};

use crate::server::{Incoming, Server};
use crate::text::range;
use crate::{Job, Outcome, Output};

/// The commands of the lenses, which `workspace/executeCommand` runs.
pub(crate) const COMMANDS: [&str; 3] = [RUN, STOP, SHOW];
const RUN: &str = "stilt.lens.run";
const STOP: &str = "stilt.lens.stop";
const SHOW: &str = "stilt.lens.show";

/// How often the thread that waits on a job's process looks whether it has ended.
const POLL: Duration = Duration::from_millis(20);

/// A job's process that has ended, with what it gave.
pub(crate) struct Finished {
    job: Job,
    output: Output,
}

/// The job running, and the results of the last run of each job.
#[derive(Default)]
pub(crate) struct Jobs {
    running: Option<(Job, Arc<Mutex<Child>>)>,
    /// The results of cases, by their file and line, from 1.
    cases: HashMap<(PathBuf, u32), Outcome>,
    /// The result of each job as a whole.
    whole: HashMap<Job, Outcome>,
    /// The number of the next request the server sends.
    next: u64,
    /// Whether the editor asks for the lenses again when the server says they changed.
    pub(crate) refreshes: bool,
}

impl Jobs {
    /// Forgets every result, since a file changed.
    pub(crate) fn changed(&mut self) {
        self.cases.clear();
        self.whole.clear();
    }
}

fn command(title: &str, name: &str, arguments: &Value) -> Value {
    json!({ "title": title, "command": name, "arguments": arguments })
}

/// What a lens shows of a result: a mark and its label.
fn shown(o: &Outcome) -> Value {
    let mark = if o.passed { "✓" } else { "✗" };
    command(&format!("{mark} {}", o.label), SHOW, &json!([o.detail]))
}

impl<W: Write> Server<'_, W> {
    /// The lenses of a file: each job's, or its stop while it runs, and the results beside them.
    pub(crate) fn lenses(&mut self, params: &Value) -> Value {
        let (file, _, text) = self.document(params);
        let running = self.jobs.running.as_ref().map(|(job, _)| *job);
        let mut found = Vec::new();
        for lens in self.backend.lenses(&file, &text) {
            let at = range(&text, lens.at, lens.at);
            let line = at["start"]["line"].as_u64().unwrap_or(0);
            let start = json!({ "line": line, "character": 0 });
            let here = json!({ "start": start, "end": start });
            let run = if running == Some(lens.job) {
                command("■ Stop", STOP, &json!([]))
            } else {
                let title = match lens.job {
                    Job::Tests => "▶ Run tests",
                    Job::Main => "▶ Run",
                };
                command(title, RUN, &json!([lens.job]))
            };
            found.push(json!({ "range": here, "command": run }));
            let line = u32::try_from(line + 1).unwrap_or(u32::MAX);
            let outcome = match lens.job {
                Job::Tests => self.jobs.cases.get(&(file.clone(), line)),
                Job::Main => self.jobs.whole.get(&Job::Main),
            };
            if let Some(o) = outcome {
                found.push(json!({ "range": here, "command": shown(o) }));
            }
        }
        Value::Array(found)
    }

    /// Runs a lens's command: starts a job, stops the one running, or shows a result's detail.
    pub(crate) fn execute(&mut self, params: &Value) -> io::Result<()> {
        let argument = &params["arguments"][0];
        match params["command"].as_str().unwrap_or_default() {
            RUN => match serde_json::from_value::<Job>(argument.clone()) {
                Ok(job) => self.start(job),
                Err(_) => self.message(1, "stilt: a lens names no job"),
            },
            STOP => {
                if let Some((_, child)) = &self.jobs.running {
                    let _ = child.lock().unwrap_or_else(PoisonError::into_inner).kill();
                }
                Ok(())
            }
            SHOW => self.message(3, argument.as_str().unwrap_or_default()),
            other => self.message(1, &format!("stilt: no command `{other}`")),
        }
    }

    fn start(&mut self, job: Job) -> io::Result<()> {
        if self.jobs.running.is_some() {
            return self.message(2, "stilt: a job is running; its lens stops it");
        }
        let started = self.backend.job(job).and_then(|command| {
            spawn(command, job, self.incoming.clone())
                .map_err(|e| format!("cannot run the job: {e}"))
        });
        match started {
            Ok(child) => {
                self.jobs.running = Some((job, child));
                self.refresh()
            }
            Err(e) => self.message(1, &format!("stilt: {e}")),
        }
    }

    /// Takes in what a job found, and shows its summary.
    pub(crate) fn finished(&mut self, finished: &Finished) -> io::Result<()> {
        self.jobs.running = None;
        let ran = self.backend.ran(finished.job, &finished.output);
        if finished.job == Job::Tests {
            self.jobs.cases.clear();
        }
        let failed = ran.outcomes.iter().any(|o| !o.passed);
        for o in ran.outcomes {
            match o.at.clone() {
                Some(at) => self.jobs.cases.insert(at, o),
                None => self.jobs.whole.insert(finished.job, o),
            };
        }
        self.message(if failed { 2 } else { 3 }, &ran.summary)?;
        self.refresh()
    }

    /// Asks the editor for the lenses again, if it can be asked.
    fn refresh(&mut self) -> io::Result<()> {
        if !self.jobs.refreshes {
            return Ok(());
        }
        self.jobs.next += 1;
        let id = format!("stilt-{}", self.jobs.next);
        let method = "workspace/codeLens/refresh";
        self.send(&json!({ "jsonrpc": "2.0", "id": id, "method": method }))
    }

    /// Shows `text` in the editor, as an error, 1, a warning, 2, or information, 3.
    fn message(&mut self, kind: u8, text: &str) -> io::Result<()> {
        let params = json!({ "type": kind, "message": text });
        self.send(&json!({ "jsonrpc": "2.0", "method": "window/showMessage", "params": params }))
    }
}

/// Starts `command` with an empty standard input, its output read on threads, and a thread
/// that sends what it gave once it ends.
fn spawn(
    mut command: std::process::Command,
    job: Job,
    send: std::sync::mpsc::Sender<Incoming>,
) -> io::Result<Arc<Mutex<Child>>> {
    command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = command.spawn()?;
    let stdout = read(child.stdout.take());
    let stderr = read(child.stderr.take());
    let child = Arc::new(Mutex::new(child));
    let held = Arc::clone(&child);
    std::thread::spawn(move || {
        let status = loop {
            let waited = held
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .try_wait();
            match waited {
                Ok(None) => std::thread::sleep(POLL),
                Ok(Some(status)) => break Some(status),
                Err(_) => break None,
            }
        };
        let text = |t: std::thread::JoinHandle<Vec<u8>>| {
            String::from_utf8_lossy(&t.join().unwrap_or_default()).into_owned()
        };
        let output = Output {
            code: status.and_then(|s| s.code()),
            stdout: text(stdout),
            stderr: text(stderr),
        };
        let _ = send.send(Incoming::Finished(Finished { job, output }));
    });
    Ok(child)
}

/// A thread that reads a pipe to its end.
fn read(pipe: Option<impl Read + Send + 'static>) -> std::thread::JoinHandle<Vec<u8>> {
    std::thread::spawn(move || {
        let mut bytes = Vec::new();
        if let Some(mut pipe) = pipe {
            let _ = pipe.read_to_end(&mut bytes);
        }
        bytes
    })
}
