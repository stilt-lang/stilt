//! A program held in an image, with its run, and the edits patched into it (goal
//! edit-to-running-program).

use std::ffi::OsString;
use std::path::Path;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use stilt_codegen_clif::Image;
use stilt_mir::mir::Function;
use stilt_runtime::{Ended, Running};

use super::code::{Code, Update};

/// How long a run that must stop is waited for.
const STOP_WAIT: Duration = Duration::from_secs(1);

/// A program held in an image, with its run.
pub(super) struct Session {
    args: Vec<String>,
    image: Image,
    /// The paths of the program's files, by the indexes its locations use.
    files: Vec<String>,
    running: Running,
    /// Whether the program had errors when it started, so that the run ends with status 2
    /// however it ends (program.programs-with-errors).
    with_errors: bool,
}

impl Session {
    /// Compiles the code of the program at `path` and starts it with `args`, or says why it
    /// can't.
    pub(super) fn start(path: &Path, args: &[OsString], code: Code) -> Result<Self, String> {
        let mut image = Image::watched().map_err(crate::bug::internal)?;
        image.set_files(super::paths(path));
        dump(&code.functions);
        image.set_guards(code.guards);
        image.load(&code.functions).map_err(crate::bug::internal)?;
        let args: Vec<String> = args
            .iter()
            .map(|a| a.to_string_lossy().into_owned())
            .collect();
        let running = launch(&image, &code.files, &args, true, code.with_errors)
            .map_err(crate::bug::internal)?;
        Ok(Self {
            args,
            image,
            files: code.files,
            running,
            with_errors: code.with_errors,
        })
    }

    /// Ends the session once its run has ended: its image's code is freed, unless a task of the
    /// run on a thread that hasn't ended may still run it, and
    /// the program's thread waits until the process ends. A session kept so stays where a
    /// leak check finds it.
    pub(super) fn close(self) {
        static KEPT: Mutex<Vec<usize>> = Mutex::new(Vec::new());
        if !self.running.quiet() {
            let kept = Box::into_raw(Box::new(self)) as usize;
            KEPT.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(kept);
        }
    }

    /// The status the run ended with, waiting at most `timeout` for it to end.
    pub(super) fn wait(&self, timeout: Duration) -> Option<i32> {
        match self.running.wait(timeout)? {
            Ended::Status(status) => Some(status),
            // A stopped run is replaced by a new one at once, unless starting that failed with
            // an internal error, which was reported. A run's entry is no test's.
            Ended::Stopped | Ended::Tested(_) => Some(1),
        }
    }

    /// Takes in what an edit changed: an edit that leaves errors patches nothing, and reports
    /// them, and otherwise its new code is patched in.
    pub(super) fn update(&mut self, update: Update) {
        match update {
            Update::Unchanged => {}
            Update::Errors(diagnostics) => {
                eprint!("{}", crate::colour::stderr(&diagnostics));
                eprintln!("stilt: the program has errors, so the edit isn't patched");
            }
            Update::NoMain => {
                eprintln!("stilt: module `main` has no function `main`, so the edit isn't patched");
            }
            Update::Unreadable(message) => eprintln!("stilt: {message}"),
            Update::Patch {
                functions,
                guards,
                moved,
                files,
            } => {
                self.files = files;
                self.image.set_guards(guards);
                if let Err(message) = self.patch(&functions, moved) {
                    eprintln!("stilt: internal error: {message}");
                }
            }
        }
    }

    /// Compiles the functions that the edit changed into the image, and starts the program
    /// again if the edit changed the layout of its values. The run is stopped before the new
    /// code goes in, so that it never runs code of the new layout on values of the old one; a
    /// run that doesn't stop takes the whole process with it, which starts again.
    fn patch(&mut self, functions: &[Arc<Function>], moved: bool) -> Result<(), String> {
        if moved && self.running.ended().is_none() {
            let stopped = self.running.stop(STOP_WAIT);
            if !stopped && !matches!(self.running.ended(), Some(Ended::Status(_))) {
                return Err(restart());
            }
        }
        let loaded = self.image.load(functions)?;
        if !moved {
            if self.running.ended().is_none() {
                let n = loaded.compiled.len();
                let s = if n == 1 { "" } else { "s" };
                eprintln!("stilt: patched {n} function{s}");
            }
            return Ok(());
        }
        if matches!(self.running.ended(), Some(Ended::Status(_))) {
            // It ended on its own before it was stopped, and `run` ends with it.
            return Ok(());
        }
        eprintln!("stilt: the layout of the program's values changed, so it starts again");
        // The stopped run keeps its objects, so the new one can't check for leaks.
        let (files, args) = (&self.files, &self.args);
        self.running = launch(&self.image, files, args, false, self.with_errors)?;
        Ok(())
    }
}

/// Starts `stilt run` again in the place of this process, whose run didn't stop when it had to,
/// or says why it can't.
fn restart() -> String {
    eprintln!("stilt: the program didn't stop, so `stilt run` starts again");
    let program = match std::env::current_exe() {
        Ok(program) => program,
        Err(e) => return format!("cannot start `stilt run` again: {e}"),
    };
    let mut command = std::process::Command::new(program);
    command.args(std::env::args_os().skip(1));
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        let error = command.exec();
        format!("cannot start `stilt run` again: {error}")
    }
    #[cfg(not(unix))]
    {
        let _ = command;
        "cannot start `stilt run` again on this system".to_owned()
    }
}

/// Writes the MIR of each function to standard error, when `STILT_DUMP_MIR` is set.
fn dump(functions: &[Arc<Function>]) {
    if std::env::var_os("STILT_DUMP_MIR").is_some() {
        for f in functions {
            eprintln!("{}", stilt_mir::print::print(f));
        }
    }
}

/// Starts a run of the image's program.
fn launch(
    image: &Image,
    files: &[String],
    args: &[String],
    check_leaks: bool,
    with_errors: bool,
) -> Result<Running, String> {
    Ok(stilt_runtime::start(stilt_runtime::Program {
        entry: image.entry()?,
        files: files.to_vec(),
        args: args.to_vec(),
        check_leaks,
        with_errors,
    }))
}
