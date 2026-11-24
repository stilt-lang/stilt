//! `stilt reduce COMMAND...`: a smaller program on which a command of `stilt` still stops on
//! the same internal error, written with a report to attach to the bug. It copies the program
//! that the command names, reruns the command on smaller copies, each in a process of its own
//! that uses no engine, and keeps a copy when that process stops on an internal error at the same
//! place in the compiler's code ([`search`]).

mod search;

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use search::{Files, Search, is_module, lines};

use crate::report::Report;

/// How long a candidate's command may run before it counts as not failing.
const PATIENCE: Duration = Duration::from_secs(30);

/// The line that a panic of the compiler prints first: where in its code it stopped.
const PANICKED: &str = "panicked at ";

/// `stilt reduce` of `command`, writing what it finds into `out`.
pub(crate) fn command(command: &[String], out: &Path) -> Report {
    match reduce(command, out) {
        Ok(message) => Report {
            stderr: message,
            ..Report::default()
        },
        Err(message) => Report::refuse(&message),
    }
}

fn reduce(command: &[String], out: &Path) -> Result<String, String> {
    let (at, program) = program_of(command)?;
    let files = read(&program)?;
    let work = std::env::temp_dir().join(format!("stilt-reduce-{}", std::process::id()));
    let runner = Runner::new(command, at, &program, &work)?;
    let first = runner.place(&files)?.ok_or_else(|| {
        format!(
            "`stilt {}` doesn't stop on an internal error, so there is nothing to reduce",
            command.join(" ")
        )
    })?;
    let entry = match () {
        () if program.is_file() => "",
        () if program.join("stilt.toml").is_file() => "src/main.lt",
        () => "main.lt",
    };
    // A manifest stays whole: a line left out of it is an error of its own.
    let found = Search::new(files.clone(), |c| {
        runner.place(c).ok().flatten() == Some(first.clone())
    })
    .run(entry);
    let _ = std::fs::remove_dir_all(&work);
    let _ = std::fs::remove_dir_all(out);
    write(&placed(out, &program), &found.best, &program)?;
    let report = runner.report(&found.best, &first)?;
    std::fs::write(out.join("report.md"), report)
        .map_err(|e| format!("cannot write {}: {e}", out.display()))?;
    Ok(format!(
        "wrote {}: a program of {} lines, from {}, that stops `stilt {}` at {first}, after {} \
         runs; attach it to the report at {}\n",
        out.display(),
        lines(&found.best),
        lines(&files),
        command.join(" "),
        found.tried,
        crate::bug::ISSUES
    ))
}

/// Where the program in `command` is among its arguments, and its path: the first argument
/// after the command's name that names a file or a directory, or the working directory.
fn program_of(command: &[String]) -> Result<(Option<usize>, PathBuf), String> {
    if command.is_empty() {
        return Err("give the command that stopped, as `stilt reduce check main.lt`".to_owned());
    }
    let at = (1..command.len()).find(|&i| Path::new(&command[i]).exists());
    let path = at.map_or_else(|| PathBuf::from("."), |i| PathBuf::from(&command[i]));
    Ok((at, path))
}

/// The program's files: a file alone, as `""`, or each `.lt` file and manifest below a
/// directory, by its path from it, but for those under a name that starts with `.` and under
/// `target`, which hold no source.
fn read(program: &Path) -> Result<Files, String> {
    let mut files = Files::new();
    if program.is_file() {
        files.insert(String::new(), split(&text(program)?));
    } else {
        walk(program, "", &mut files)?;
    }
    Ok(files)
}

fn text(path: &Path) -> Result<String, String> {
    std::fs::read_to_string(path).map_err(|e| format!("cannot read {}: {e}", path.display()))
}

fn walk(dir: &Path, relative: &str, files: &mut Files) -> Result<(), String> {
    let entries =
        std::fs::read_dir(dir).map_err(|e| format!("cannot read {}: {e}", dir.display()))?;
    for entry in entries.flatten() {
        let name = entry.file_name().to_string_lossy().into_owned();
        let path = entry.path();
        let at = if relative.is_empty() {
            name.clone()
        } else {
            format!("{relative}/{name}")
        };
        if name.starts_with('.') || name == "target" {
            continue;
        }
        if path.is_dir() {
            walk(&path, &at, files)?;
        } else if is_module(&name) || name == "stilt.toml" {
            files.insert(at, split(&text(&path)?));
        }
    }
    Ok(())
}

fn split(text: &str) -> Vec<String> {
    text.lines().map(str::to_owned).collect()
}

/// The name the program is written under: its file's or its directory's.
fn name(program: &Path) -> String {
    let canonical = program
        .canonicalize()
        .unwrap_or_else(|_| program.to_path_buf());
    canonical.file_name().map_or_else(
        || "program".to_owned(),
        |n| n.to_string_lossy().into_owned(),
    )
}

/// Where a program is written in `root`: a file in it, and a directory under its own name, so
/// that the command names it as it named the program.
fn placed(root: &Path, program: &Path) -> PathBuf {
    if program.is_file() {
        root.to_path_buf()
    } else {
        root.join(name(program))
    }
}

/// Writes the files into `root`, as a single file named after `program` or as a directory.
fn write(root: &Path, files: &Files, program: &Path) -> Result<(), String> {
    let failed = |e: std::io::Error| format!("cannot write {}: {e}", root.display());
    if program.is_dir() {
        let _ = std::fs::remove_dir_all(root);
    }
    std::fs::create_dir_all(root).map_err(failed)?;
    for (path, lines) in files {
        let name = if path.is_empty() {
            PathBuf::from(name(program))
        } else {
            PathBuf::from(path)
        };
        let file = root.join(name);
        if let Some(dir) = file.parent() {
            std::fs::create_dir_all(dir).map_err(failed)?;
        }
        let mut text = lines.join("\n");
        text.push('\n');
        std::fs::write(file, text).map_err(failed)?;
    }
    Ok(())
}

/// What runs the command on a candidate.
struct Runner<'a> {
    command: &'a [String],
    at: Option<usize>,
    program: &'a Path,
    work: PathBuf,
    /// A directory whose engines' directory can't be made, so that the command runs in its own
    /// process (engines.private).
    tmp: PathBuf,
}

impl<'a> Runner<'a> {
    fn new(
        command: &'a [String],
        at: Option<usize>,
        program: &'a Path,
        work: &Path,
    ) -> Result<Self, String> {
        let tmp = work.join("tmp");
        crate::engine::without_engines(&tmp)
            .map_err(|e| format!("cannot write {}: {e}", tmp.display()))?;
        Ok(Self {
            command,
            at,
            program,
            work: work.join("program"),
            tmp,
        })
    }

    /// Where in the compiler's code the command stops on the program `files`, if it stops on
    /// an internal error.
    fn place(&self, files: &Files) -> Result<Option<String>, String> {
        let output = self.run(files)?;
        let stderr = String::from_utf8_lossy(&output);
        if !stderr.contains("an internal error, which is a bug in stilt") {
            return Ok(None);
        }
        let place = stderr.lines().find_map(|l| {
            let at = l.find(PANICKED)?;
            Some(l[at + PANICKED.len()..].trim_end_matches(':').to_owned())
        });
        // An error of the compiler's own that isn't a panic is placed by its message.
        let place = place.or_else(|| {
            let line = stderr.lines().find(|l| l.contains(crate::bug::INTERNAL))?;
            Some(line[line.find(crate::bug::INTERNAL)?..].to_owned())
        });
        Ok(place.or_else(|| Some("an unknown place".to_owned())))
    }

    /// What the command writes to stderr on the program `files`, or nothing when it outlasts
    /// [`PATIENCE`].
    fn run(&self, files: &Files) -> Result<Vec<u8>, String> {
        write(&self.work, files, self.program)?;
        let target = if self.program.is_file() {
            self.work.join(name(self.program))
        } else {
            self.work.clone()
        };
        let mut args: Vec<String> = self.command.to_vec();
        match self.at {
            Some(i) => args[i] = target.to_string_lossy().into_owned(),
            None => args.push(target.to_string_lossy().into_owned()),
        }
        let exe = std::env::current_exe().map_err(|e| format!("cannot find stilt: {e}"))?;
        let mut child = Command::new(exe)
            .args(&args)
            .env("TMPDIR", &self.tmp)
            .env("NO_COLOR", "1")
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| format!("cannot run stilt: {e}"))?;
        let mut stderr = child.stderr.take().expect("a pipe");
        let reader = std::thread::spawn(move || {
            let mut bytes = Vec::new();
            let _ = std::io::Read::read_to_end(&mut stderr, &mut bytes);
            bytes
        });
        let start = Instant::now();
        while child.try_wait().ok().flatten().is_none() {
            if start.elapsed() > PATIENCE {
                let _ = child.kill();
                let _ = child.wait();
                return Ok(Vec::new());
            }
            std::thread::sleep(Duration::from_millis(20));
        }
        Ok(reader.join().unwrap_or_default())
    }

    /// The report: the command, the toolchain, where it stops, and what it writes, as it would
    /// in the report's directory: without the reduced copy's path, the note of a command that
    /// runs without an engine, and the note that names this command.
    fn report(&self, files: &Files, place: &str) -> Result<String, String> {
        let program = name(self.program);
        let target = if self.program.is_file() {
            self.work.join(&program)
        } else {
            self.work.clone()
        };
        let written = String::from_utf8_lossy(&self.run(files)?).into_owned();
        let _ = std::fs::remove_dir_all(self.work.parent().unwrap_or(&self.work));
        let mut stderr = String::new();
        for line in written.lines().filter(|l| {
            !l.ends_with("so the command runs without an engine")
                && !l.starts_with("note: `stilt reduce ")
        }) {
            stderr.push_str(&line.replace(&*target.to_string_lossy(), &program));
            stderr.push('\n');
        }
        let mut command = self.command.to_vec();
        match self.at {
            Some(i) => command[i] = program,
            None => command.push(program),
        }
        Ok(format!(
            "# stilt stops on an internal error\n\n- Command: `stilt {}`, run in this directory\n\
             - Toolchain: stilt {}, on {}-{}\n- Where: {place}\n\nWhat it writes to stderr:\n\n\
             ```text\n{}```\n",
            command.join(" "),
            env!("STILT_VERSION"),
            std::env::consts::ARCH,
            std::env::consts::OS,
            stderr
        ))
    }
}
