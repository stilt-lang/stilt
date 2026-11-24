//! An engine of the compiler holding a project, which the commands of `stilt` on the project ask,
//! as they do while a person works on it (goal one-engine).

use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::time::{Duration, Instant};

use stilt_meter::Counts;

/// How long the harness waits for the engine to listen.
const START: Duration = Duration::from_secs(60);

/// An engine holding the project, stopped when this is dropped.
pub(crate) struct Engine {
    stilt: PathBuf,
    project: PathBuf,
    child: Child,
}

impl Engine {
    /// Starts the engine of `stilt` for `project`, after stopping any engine that holds it
    /// already, and waits until it listens.
    pub(crate) fn start(stilt: &Path, project: &Path) -> Result<Self, String> {
        let _ = Command::new(stilt)
            .args(["engine", "--stop"])
            .arg(project)
            .output();
        let child = Command::new(stilt)
            .arg("engine")
            .arg(project)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .map_err(|e| format!("cannot start {}: {e}", stilt.display()))?;
        let engine = Self {
            stilt: stilt.to_path_buf(),
            project: project.to_path_buf(),
            child,
        };
        let since = Instant::now();
        while !engine.listens() {
            if since.elapsed() > START {
                return Err("the engine doesn't listen".to_owned());
            }
            std::thread::sleep(Duration::from_millis(20));
        }
        Ok(engine)
    }

    /// Whether the engine answers, which it does once it is done with the command before:
    /// after it answers a command, it forgets what it keeps beyond its bounds.
    pub(crate) fn listens(&self) -> bool {
        Command::new(&self.stilt)
            .args(["engine", "--ran"])
            .arg(&self.project)
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .is_ok_and(|s| s.success())
    }

    /// `stilt ARGS` on the project, which the engine answers. A command with errors is no
    /// failure: an edit of the script may leave some.
    pub(crate) fn ask(&self, args: &[&str]) -> Result<(), String> {
        self.answer(args).map(drop)
    }

    /// What `stilt ARGS` on the project, which the engine answers, writes, and its status.
    pub(crate) fn answer(&self, args: &[&str]) -> Result<Output, String> {
        Command::new(&self.stilt)
            .args(args)
            .arg(&self.project)
            .stdin(Stdio::null())
            .output()
            .map_err(|e| format!("cannot run {}: {e}", self.stilt.display()))
    }

    /// What `stilt ARGS` on the project writes, and what the command's own process cost,
    /// read by the meter once it ended.
    pub(crate) fn answer_counted(&self, args: &[&str]) -> Result<(Output, Counts), String> {
        let mut command = Command::new(&self.stilt);
        command.args(args).arg(&self.project);
        stilt_meter::run(&mut command)
            .map_err(|e| format!("cannot run {}: {e}", self.stilt.display()))
    }

    /// The engine's process.
    pub(crate) fn pid(&self) -> u32 {
        self.child.id()
    }
}

impl Drop for Engine {
    fn drop(&mut self) {
        let _ = Command::new(&self.stilt)
            .args(["engine", "--stop"])
            .arg(&self.project)
            .output();
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}
