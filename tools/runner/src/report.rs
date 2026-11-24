//! Reporting results: one greppable line per failure on stdout, and the details in a log file.

use std::fmt::Write as _;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use crate::discovery;
use crate::runner::{Outcome, Record};

/// Counts of each outcome.
#[derive(Debug, Default)]
pub(crate) struct Summary {
    pub(crate) passed: usize,
    pub(crate) failed: usize,
    pub(crate) malformed: usize,
    pub(crate) declined: usize,
}

impl Summary {
    pub(crate) fn add(&mut self, outcome: &Outcome) {
        match outcome {
            Outcome::Passed => self.passed += 1,
            Outcome::Failed(_) => self.failed += 1,
            Outcome::Malformed(_) => self.malformed += 1,
            Outcome::Declined => self.declined += 1,
        }
    }

    pub(crate) fn all_passed(&self) -> bool {
        self.failed == 0 && self.malformed == 0
    }

    /// The summary of `count` tests or examples, `what`, run in `elapsed`: the declined ones
    /// only when there are some.
    pub(crate) fn line(&self, count: usize, what: &str, elapsed: std::time::Duration) -> String {
        let declined = if self.declined > 0 {
            format!(", {} declined", self.declined)
        } else {
            String::new()
        };
        format!(
            "{count} {what}: {} passed, {} failed, {} malformed{declined}, in {:.1} s",
            self.passed,
            self.failed,
            self.malformed,
            elapsed.as_secs_f64()
        )
    }
}

/// Writes one log file per failing test into a directory that it empties first.
#[derive(Debug)]
pub(crate) struct Logs {
    dir: PathBuf,
}

impl Logs {
    pub(crate) fn create(dir: &Path) -> io::Result<Self> {
        discovery::empty_dir(dir)?;
        Ok(Self {
            dir: dir.to_owned(),
        })
    }

    /// Writes the log of a failed or malformed test, and returns its path.
    pub(crate) fn write(&self, record: &Record) -> io::Result<PathBuf> {
        let path = self
            .dir
            .join(format!("{}.log", record.name.replace(['/', '\\'], "__")));
        fs::write(&path, log(record))?;
        Ok(path)
    }
}

/// The `ERROR` line for a test that didn't pass.
pub(crate) fn error_line(record: &Record, log: &Path) -> String {
    let reason = match &record.outcome {
        Outcome::Passed | Outcome::Declined => unreachable!("only failures are reported"),
        Outcome::Failed(reasons) => {
            let more = reasons.len() - 1;
            if more == 0 {
                reasons[0].clone()
            } else {
                format!("{} (and {more} more)", reasons[0])
            }
        }
        Outcome::Malformed(reason) => reason.clone(),
    };
    format!("ERROR {}: {reason} [log: {}]", record.name, log.display())
}

fn log(record: &Record) -> String {
    let mut text = format!("test: {}\n", record.name);
    match &record.outcome {
        Outcome::Passed | Outcome::Declined => {}
        Outcome::Failed(reasons) => {
            for reason in reasons {
                let _ = writeln!(text, "failure: {reason}");
            }
        }
        Outcome::Malformed(reason) => {
            let _ = writeln!(text, "{reason}");
        }
    }
    if !record.expected.is_empty() {
        let _ = write!(text, "\n=== expected\n{}", record.expected);
    }
    for step in &record.steps {
        let output = &step.output;
        let _ = write!(
            text,
            "\n=== {}\n{}\n--- stdout\n{}\n--- stderr\n{}\n",
            step.command,
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
    }
    text
}
