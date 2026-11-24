//! The runs of `std.process` (std.process-starting, std.process-runs and std.children): a
//! command's program looked up in the `PATH` of its environment, its runs to their end with
//! their streams captured or the program's own, and the children that run beside the program,
//! with their standard input and output piped to it.

use std::collections::HashMap;
use std::io::{BufRead, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, ExitStatus, Stdio};
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::{Arc, LazyLock, Mutex, MutexGuard, PoisonError};

use crate::std_io::IoError;

/// Why a command didn't start, or a write to a child failed: the variant of `IoError`, and
/// the path it names.
pub(super) type Failure = (IoError, String);

/// What a command is: its program as written, its arguments, the variables it sets, as names
/// and values in pairs, the ones it removes, and its working directory, `""` for the program's
/// own.
pub(super) struct Spec<'a> {
    pub(super) program: &'a str,
    pub(super) args: Vec<&'a str>,
    pub(super) set: Vec<&'a str>,
    pub(super) removed: Vec<&'a str>,
    pub(super) dir: &'a str,
}

/// How a command runs: to its end with `input` as its standard input and its output
/// captured, to its end with the program's own streams, or beside the program.
#[derive(Clone, Copy)]
pub(super) enum Mode<'a> {
    Captured(&'a str),
    Inherited,
    Piped,
}

/// A run: the program it was started as, the child while it runs, its standard input while
/// it is open, its standard output while it is read from it, then what [`Run::keep`] read of
/// it ahead, and once it has ended its status and what a captured run wrote.
pub(super) struct Run {
    program: String,
    child: Option<Child>,
    input: Option<ChildStdin>,
    output: Option<BufReader<ChildStdout>>,
    kept: Vec<u8>,
    at: usize,
    status: Option<i64>,
    pub(super) captured: (String, String),
}

/// The runs, by their numbers, each behind its own lock, so that a read from one child
/// waits for no other.
static RUNS: LazyLock<Mutex<HashMap<i64, Arc<Mutex<Run>>>>> = LazyLock::new(Mutex::default);

/// The number of the latest run.
static COUNT: AtomicI64 = AtomicI64::new(0);

fn locked<T>(m: &Mutex<T>) -> MutexGuard<'_, T> {
    m.lock().unwrap_or_else(PoisonError::into_inner)
}

/// The run of number `id`, which [`start`] gave.
pub(super) fn run(id: i64) -> Arc<Mutex<Run>> {
    let runs = locked(&RUNS);
    Arc::clone(runs.get(&id).expect("a run that `start` gave"))
}

/// Calls `f` on the run of number `id`.
pub(super) fn with<T>(id: i64, f: impl FnOnce(&mut Run) -> T) -> T {
    let run = run(id);
    let mut run = locked(&run);
    f(&mut run)
}

fn register(run: Run) -> i64 {
    let id = COUNT.fetch_add(1, Ordering::Relaxed) + 1;
    locked(&RUNS).insert(id, Arc::new(Mutex::new(run)));
    id
}

/// Whether a name can be set in an environment: it isn't empty and holds no `=` or NUL.
fn valid(name: &str) -> bool {
    !name.is_empty() && !name.contains(['=', '\0'])
}

/// The environment that the command's changes make of the program's own, or `None` when a
/// name or a value can't be set.
fn environment(spec: &Spec<'_>) -> Option<Vec<(String, String)>> {
    let set: Vec<(&str, &str)> = spec.set.chunks(2).map(|p| (p[0], p[1])).collect();
    if set.iter().any(|(n, v)| !valid(n) || v.contains('\0'))
        || !spec.removed.iter().all(|n| valid(n))
    {
        return None;
    }
    let changed = |name: &str| set.iter().any(|(n, _)| *n == name) || spec.removed.contains(&name);
    let mut env: Vec<(String, String)> = std::env::vars_os()
        .map(|(n, v)| {
            (
                n.to_string_lossy().into_owned(),
                v.to_string_lossy().into_owned(),
            )
        })
        .filter(|(n, _)| !changed(n))
        .collect();
    env.extend(set.iter().map(|(n, v)| ((*n).to_owned(), (*v).to_owned())));
    Some(env)
}

/// Whether `path` is a regular file that the program may execute, one it may not, or neither.
fn executable(path: &Path) -> Option<bool> {
    if !std::fs::metadata(path).is_ok_and(|m| m.is_file()) {
        return None;
    }
    #[cfg(unix)]
    {
        let name = std::ffi::CString::new(path.as_os_str().as_encoded_bytes()).ok()?;
        // SAFETY: `name` is a NUL-terminated string that outlives the call, which only reads it.
        Some(unsafe { libc::access(name.as_ptr(), libc::X_OK) } == 0)
    }
    #[cfg(not(unix))]
    Some(false)
}

/// The file that runs `program`: a path when it holds a `/`, relative to the program's working
/// directory, and otherwise the first executable file of that name in the directories of the
/// `PATH` of `env`.
fn resolve(program: &str, env: &[(String, String)]) -> Result<PathBuf, Failure> {
    let missing = || (IoError::NotFound, program.to_owned());
    let denied = || (IoError::PermissionDenied, program.to_owned());
    if program.contains('/') {
        let path = std::env::current_dir()
            .map_err(|_| missing())?
            .join(program);
        return match executable(&path) {
            Some(true) => Ok(path),
            Some(false) => Err(denied()),
            None => Err(missing()),
        };
    }
    let path = env
        .iter()
        .find(|(n, _)| n == "PATH")
        .map_or("", |(_, v)| v.as_str());
    let mut found_denied = false;
    for dir in path
        .split(':')
        .filter(|d| !d.is_empty() && !program.is_empty())
    {
        let file = Path::new(dir).join(program);
        match executable(&file) {
            Some(true) => return Ok(file),
            Some(false) => found_denied = true,
            None => {}
        }
    }
    Err(if found_denied { denied() } else { missing() })
}

/// A status: the code the program exited with, or `-n` for the signal `n` that ended it.
fn status_of(status: ExitStatus) -> i64 {
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt as _;
        if let Some(signal) = status.signal() {
            return -i64::from(signal);
        }
    }
    status.code().map_or(-1, i64::from)
}

/// The command that runs `file` as `spec.program`, with its environment and directory.
fn command(spec: &Spec<'_>, file: &Path, env: Vec<(String, String)>) -> Command {
    let mut c = Command::new(file);
    #[cfg(unix)]
    std::os::unix::process::CommandExt::arg0(&mut c, spec.program);
    c.args(&spec.args).env_clear().envs(env);
    if !spec.dir.is_empty() {
        c.current_dir(spec.dir);
    }
    c
}

/// A write to a child that has closed its input fails rather than ending the program.
fn ignore_broken_pipes() {
    #[cfg(unix)]
    {
        static ONCE: std::sync::Once = std::sync::Once::new();
        // SAFETY: setting a signal's disposition to "ignore" installs no handler, and the
        // children get the default back, as `Command` resets it in each.
        ONCE.call_once(|| unsafe {
            libc::signal(libc::SIGPIPE, libc::SIG_IGN);
        });
    }
}

fn run_of(program: &str, child: Option<Child>, status: Option<i64>) -> Run {
    Run {
        program: program.to_owned(),
        child,
        input: None,
        output: None,
        kept: Vec::new(),
        at: 0,
        status,
        captured: (String::new(), String::new()),
    }
}

/// Runs the command to its end with `input` as its standard input, writing it on a thread of
/// its own while its two outputs are read, so that none of the three waits for another.
fn captured(mut c: Command, program: &str, input: &str) -> std::io::Result<Run> {
    ignore_broken_pipes();
    let mut child = c
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let stdin = child.stdin.take();
    let input = input.as_bytes().to_vec();
    let writer = std::thread::spawn(move || {
        if let Some(mut stdin) = stdin {
            let _ = stdin.write_all(&input);
        }
    });
    let out = child.wait_with_output()?;
    let _ = writer.join();
    let mut run = run_of(program, None, Some(status_of(out.status)));
    run.captured = (
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    );
    Ok(run)
}

/// Starts the command as `mode` says, and gives its run's number.
pub(super) fn start(spec: &Spec<'_>, mode: Mode<'_>) -> Result<i64, Failure> {
    let other = || (IoError::Other, spec.program.to_owned());
    // WebAssembly runs no other program (wasm.what-std-reads).
    if cfg!(target_os = "wasi") {
        return Err((IoError::PermissionDenied, spec.program.to_owned()));
    }
    let texts = [spec.program, spec.dir]
        .into_iter()
        .chain(spec.args.iter().copied());
    if texts.into_iter().any(|t| t.contains('\0')) {
        return Err(other());
    }
    let env = environment(spec).ok_or_else(other)?;
    if !spec.dir.is_empty() && !Path::new(spec.dir).is_dir() {
        return Err((IoError::NotFound, spec.dir.to_owned()));
    }
    let file = resolve(spec.program, &env)?;
    let mut c = command(spec, &file, env);
    let failed = |e: std::io::Error| (IoError::of(&e), spec.program.to_owned());
    let run = match mode {
        Mode::Captured(input) => captured(c, spec.program, input).map_err(failed)?,
        Mode::Inherited => {
            let status = c.status().map_err(failed)?;
            run_of(spec.program, None, Some(status_of(status)))
        }
        Mode::Piped => {
            ignore_broken_pipes();
            let mut child = c
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .spawn()
                .map_err(failed)?;
            let mut run = run_of(spec.program, None, None);
            run.input = child.stdin.take();
            run.output = child.stdout.take().map(BufReader::new);
            run.child = Some(child);
            run
        }
    };
    Ok(register(run))
}

impl Run {
    /// Writes `text` to the child's standard input, or tells why it can't.
    pub(super) fn write(&mut self, text: &[u8]) -> Result<(), Failure> {
        let program = self.program.clone();
        let input = self
            .input
            .as_mut()
            .ok_or((IoError::Other, program.clone()))?;
        input
            .write_all(text)
            .and_then(|()| input.flush())
            .map_err(|_| (IoError::Other, program))
    }

    /// Closes the child's standard input.
    pub(super) fn close_input(&mut self) {
        self.input = None;
    }

    /// The next line of the child's output, without its `\n` and a `\r` before it, as
    /// `io.read_line` gives one.
    pub(super) fn read_line(&mut self) -> Option<String> {
        let mut line = Vec::new();
        if let Some(output) = self.output.as_mut() {
            if output.read_until(b'\n', &mut line).unwrap_or(0) == 0 {
                self.output = None;
                return None;
            }
        } else {
            let rest = self.kept.get(self.at..).filter(|r| !r.is_empty())?;
            let end = rest
                .iter()
                .position(|&b| b == b'\n')
                .map_or(rest.len(), |i| i + 1);
            line.extend_from_slice(&rest[..end]);
            self.at += end;
        }
        if line.last() == Some(&b'\n') {
            line.pop();
        }
        if line.last() == Some(&b'\r') {
            line.pop();
        }
        Some(String::from_utf8_lossy(&line).into_owned())
    }

    /// The rest of the child's output, which `read_all` gives and `wait` keeps.
    fn take(&mut self) -> Vec<u8> {
        let mut text = self.kept.split_off(self.at);
        if let Some(mut output) = self.output.take() {
            let _ = output.read_to_end(&mut text);
        }
        self.kept.clear();
        self.at = 0;
        text
    }

    /// The rest of the child's output.
    pub(super) fn read_all(&mut self) -> String {
        String::from_utf8_lossy(&self.take()).into_owned()
    }

    /// Closes the child's standard input, keeps the rest of its output, waits for it to end and
    /// gives its status.
    pub(super) fn wait(&mut self) -> i64 {
        if let Some(status) = self.status {
            return status;
        }
        self.input = None;
        self.kept = self.take();
        let status = self
            .child
            .take()
            .and_then(|mut c| c.wait().ok())
            .map_or(-1, status_of);
        self.status = Some(status);
        status
    }

    /// Ends the child at once, unless it has ended already.
    pub(super) fn kill(&mut self) {
        if let Some(child) = self.child.as_mut() {
            let _ = child.kill();
        }
    }
}
