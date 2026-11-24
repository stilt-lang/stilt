//! Running one command under the environment of conformance.environment.

use std::ffi::OsStr;
use std::fmt;
use std::io::{self, Read, Write};
use std::path::Path;
use std::process::{Child, ExitStatus, Stdio};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

/// The limit on each command of a conformance test, on the processor: its cycles on a performance
/// core at the reference clock, or its CPU time where the system counts no cycles
/// ([`stilt_meter::Counts::time`]), which other programs on the machine barely change.
pub(crate) const TIME_LIMIT: Duration = Duration::from_secs(10);

/// How many times its limit on the processor a command may take in all, waiting included, before
/// it is killed: a command that waits forever spends nothing on the processor.
const WAIT_FACTOR: u32 = 12;

/// How a command ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Status {
    Exited(i32),
    Signaled(i32),
    /// Killed once it ran on the processor for as long as this limit allows, or waited for
    /// [`WAIT_FACTOR`] times as long.
    TimedOut(Duration),
}

impl fmt::Display for Status {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Status::Exited(code) => write!(f, "exited with status {code}"),
            Status::Signaled(signal) => write!(f, "killed by signal {signal}"),
            Status::TimedOut(limit) => write!(
                f,
                "killed after {} s on the processor or {} s in all",
                limit.as_secs(),
                (*limit * WAIT_FACTOR).as_secs()
            ),
        }
    }
}

/// Everything a command produced.
#[derive(Debug)]
pub(crate) struct Output {
    pub(crate) status: Status,
    pub(crate) stdout: Vec<u8>,
    pub(crate) stderr: Vec<u8>,
}

/// A command to run in a clean environment.
#[derive(Debug)]
pub(crate) struct Command<'a> {
    pub(crate) program: &'a Path,
    pub(crate) args: &'a [&'a str],
    pub(crate) dir: &'a Path,
    pub(crate) stdin: &'a [u8],
    /// The only variable inherited from the runner's environment.
    pub(crate) path_env: &'a OsStr,
    /// How long the command may run on the processor.
    pub(crate) time_limit: Duration,
}

impl fmt::Display for Command<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "(cd {} && {}",
            self.dir.display(),
            self.program.display()
        )?;
        for arg in self.args {
            if arg.is_empty() || arg.contains([' ', '"', '\'', '\\']) {
                write!(f, " {arg:?}")?;
            } else {
                write!(f, " {arg}")?;
            }
        }
        write!(f, ")")
    }
}

/// Runs `command` to completion, or kills it once it exceeds its time limit.
pub(crate) fn run(command: &Command<'_>) -> io::Result<Output> {
    let mut child = std::process::Command::new(command.program)
        .args(command.args)
        .current_dir(command.dir)
        .env_clear()
        .env("PATH", command.path_env)
        .env("LC_ALL", "C")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let (Some(mut stdin), Some(stdout), Some(stderr)) =
        (child.stdin.take(), child.stdout.take(), child.stderr.take())
    else {
        unreachable!("all three streams are piped");
    };
    // A program may exit without reading its input, so a failed write is not an error.
    let input = command.stdin.to_vec();
    thread::spawn(move || stdin.write_all(&input));
    let (sent, streams) = mpsc::channel();
    let readers: [Box<dyn Read + Send>; 2] = [Box::new(stdout), Box::new(stderr)];
    for (i, stream) in readers.into_iter().enumerate() {
        let sent = sent.clone();
        thread::spawn(move || sent.send((i, read_all(stream))));
    }
    drop(sent);
    let mut read = [Vec::new(), Vec::new()];
    let status = watch(&mut child, &streams, &mut read, command.time_limit)?;
    // A process that the command started can hold its streams and outlive it, so what it wrote
    // is kept only if its streams close soon after, and the runner never waits on it for long.
    let linger = match status {
        Status::TimedOut(_) => LINGER,
        Status::Exited(_) | Status::Signaled(_) => DRAIN,
    };
    collect(&streams, &mut read, Instant::now() + linger);
    let [stdout, stderr] = read;
    Ok(Output {
        status,
        stdout,
        stderr,
    })
}

/// How long the runner waits, once it has killed a command, for the streams it left open.
const LINGER: Duration = Duration::from_secs(1);

/// How long the runner waits, once a command has ended by itself, for its streams to close. They
/// close as it ends, but their readers are threads of the runner, which a busy machine may not
/// run for a while, so only a process that the command started and that holds them makes the
/// runner wait this long.
const DRAIN: Duration = Duration::from_secs(10);

/// Takes into `read` what each stream's reader read, as each closes, until both have or
/// `until` passes.
fn collect(streams: &mpsc::Receiver<(usize, Vec<u8>)>, read: &mut [Vec<u8>; 2], until: Instant) {
    while let Ok((i, bytes)) = streams.recv_timeout(until.saturating_duration_since(Instant::now()))
    {
        read[i] = bytes;
    }
}

/// Reads a stream to its end, keeping whatever arrived before a read error.
fn read_all(mut stream: impl Read) -> Vec<u8> {
    let mut bytes = Vec::new();
    let _ = stream.read_to_end(&mut bytes);
    bytes
}

/// Waits for the command to exit, taking into `read` what its streams send meanwhile, or kills it
/// once it has run on the processor for `limit` or taken [`WAIT_FACTOR`] times as long in all.
fn watch(
    child: &mut Child,
    streams: &mpsc::Receiver<(usize, Vec<u8>)>,
    read: &mut [Vec<u8>; 2],
    limit: Duration,
) -> io::Result<Status> {
    let deadline = Instant::now() + limit * WAIT_FACTOR;
    let mut pause = Duration::from_micros(100);
    loop {
        if let Some(status) = child.try_wait()? {
            return Ok(status_of(status));
        }
        if Instant::now() >= deadline || spent(child.id()) >= limit {
            child.kill()?;
            child.wait()?;
            return Ok(Status::TimedOut(limit));
        }
        match streams.recv_timeout(pause) {
            Ok((i, bytes)) => read[i] = bytes,
            Err(mpsc::RecvTimeoutError::Timeout) => {}
            Err(mpsc::RecvTimeoutError::Disconnected) => thread::sleep(pause),
        }
        pause = (pause * 2).min(Duration::from_millis(20));
    }
}

/// What the running process `pid` has spent on the processor so far, or nothing if the system
/// won't tell, which leaves only the limit in all.
fn spent(pid: u32) -> Duration {
    stilt_meter::of(pid).map_or(Duration::ZERO, stilt_meter::Counts::time)
}

#[cfg(unix)]
fn status_of(status: ExitStatus) -> Status {
    use std::os::unix::process::ExitStatusExt;
    match (status.code(), status.signal()) {
        (Some(code), _) => Status::Exited(code),
        (None, Some(signal)) => Status::Signaled(signal),
        (None, None) => unreachable!("a finished process either exited or was killed"),
    }
}

#[cfg(not(unix))]
fn status_of(status: ExitStatus) -> Status {
    Status::Exited(status.code().unwrap_or(-1))
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    fn sh(script: &str, stdin: &[u8]) -> Output {
        sh_within(script, stdin, TIME_LIMIT)
    }

    fn sh_within(script: &str, stdin: &[u8], time_limit: Duration) -> Output {
        let path_env = std::env::var_os("PATH").unwrap_or_default();
        let command = Command {
            program: Path::new("/bin/sh"),
            args: &["-c", script],
            dir: Path::new("/"),
            stdin,
            path_env: &path_env,
            time_limit,
        };
        run(&command).unwrap()
    }

    #[test]
    fn captures_streams_and_status() {
        let output = sh("cat; echo err >&2; exit 3", b"input");
        assert_eq!(output.status, Status::Exited(3));
        assert_eq!(output.stdout, b"input");
        assert_eq!(output.stderr, b"err\n");
    }

    #[test]
    fn clears_the_environment() {
        let output = sh("echo \"$LC_ALL:$HOME\"", b"");
        assert_eq!(output.stdout, b"C:\n");
    }

    #[test]
    fn tolerates_a_program_that_ignores_its_input() {
        let output = sh("exit 0", &vec![b'x'; 1 << 20]);
        assert_eq!(output.status, Status::Exited(0));
    }

    #[test]
    fn reports_signals() {
        let output = sh("kill -9 $$", b"");
        assert_eq!(output.status, Status::Signaled(9));
    }

    #[test]
    fn kills_a_command_at_its_limit() {
        let limit = Duration::from_millis(200);
        let output = sh_within("echo started; exec sleep 5", b"", limit);
        assert_eq!(output.status, Status::TimedOut(limit));
        assert_eq!(output.stdout, b"started\n");
    }

    #[test]
    fn stops_waiting_for_streams_that_a_process_it_started_holds() {
        let limit = Duration::from_millis(200);
        let start = Instant::now();
        let output = sh_within("sleep 10 & exec sleep 10", b"", limit);
        assert_eq!(output.status, Status::TimedOut(limit));
        assert!(start.elapsed() < Duration::from_secs(5));
    }

    #[test]
    fn kills_a_command_that_computes_forever() {
        let limit = Duration::from_millis(300);
        let output = sh_within("while :; do :; done", b"", limit);
        assert_eq!(output.status, Status::TimedOut(limit));
    }

    #[test]
    fn reads_what_a_running_command_spent_on_the_processor() {
        let mut child = std::process::Command::new("/bin/sh")
            .args(["-c", "while :; do :; done"])
            .spawn()
            .unwrap();
        let start = Instant::now();
        let enough = Duration::from_millis(50);
        while spent(child.id()) < enough && start.elapsed() < Duration::from_secs(60) {
            thread::sleep(Duration::from_millis(10));
        }
        let spent = spent(child.id());
        child.kill().unwrap();
        child.wait().unwrap();
        assert!(spent >= enough, "{spent:?}");
    }

    #[test]
    fn kills_a_command_that_closed_its_streams_at_its_limit() {
        let limit = Duration::from_millis(200);
        let output = sh_within("exec sleep 5 > /dev/null 2>&1", b"", limit);
        assert_eq!(output.status, Status::TimedOut(limit));
    }
}
