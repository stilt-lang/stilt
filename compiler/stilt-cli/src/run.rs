//! `stilt run`: compiles a program in memory and runs it, and patches each edit of its files into
//! it while it runs (conformance.commands; program.main, program.exit-statuses and
//! program.programs-with-errors; goal edit-to-running-program).
//!
//! A program with errors runs all the same: its diagnostics come first, its code with an error
//! panics in place of running, and it exits with status 2 however it ends
//! (program.programs-with-errors). A program without `main` isn't run, and the status is 2
//! (program.missing-main).
//!
//! While the program runs, `run` looks at its files every 50 ms on the main thread, which
//! otherwise waits for the program's own thread to end, and is woken as soon as it does: a
//! program that ends before the first look waits for none. The program writes its output as a built
//! executable does, a line at a time (program.output-flushing). An edit is checked as `check`
//! checks it, and one that leaves errors patches nothing. Every function whose MIR the edit changed
//! is compiled again into the program's image, and each later call of it runs the new code, calls
//! already under way included. An edit that changes the layout of the program's values, its types'
//! declarations or its traits', stops the run and starts it again, since a value made before has no
//! meaning after. When the program ends, `run` ends with its status.
//!
//! The program's code comes from its engine when one runs, which lowers it as `run` would and sends
//! it, and then, at each look, what the edits since the last look change in the run (goal
//! one-engine); with none, `run` holds the program in a database of its own, with the same code
//! ([`code`]). Either way, `run` compiles and patches what it is given alike.
//!
//! `run --profile` holds the program itself, compiled with the counts of a profile, runs it
//! without patching, so that every count is of the code its profile's hashes name, and adds
//! the counts to the program's profile when it ends (builds.profiles; [`crate::profile`]).

mod code;
mod session;

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Duration;

use stilt_db::Database;
use stilt_rc::Counted;

pub(crate) use code::{Lowering, Start, Update, files, has_errors};
use session::Session;

use crate::engine::Remote;
use crate::sync::Synced;

/// How often the program's files are looked at.
const TICK: Duration = Duration::from_millis(50);

/// Runs the program at `path` with `args`, patching each edit of its files into it, or with
/// `profile` counting what its profile counts, and exits as it ends.
pub(crate) fn run(path: &Path, args: &[OsString], profile: bool) -> ExitCode {
    let refuse = |message: String| {
        eprintln!("stilt: {message}");
        ExitCode::from(crate::NOT_A_PROGRAM)
    };
    eprint!(
        "{}",
        crate::packages::lines(&crate::packages::prepare(path))
    );
    if profile {
        if let Err(report) = crate::profile::read(path) {
            return report.print();
        }
        stilt_mir::profiling::set_profiling(stilt_mir::profiling::Profiling::Count);
    }
    let (mut held, start) = match Held::open(path, profile) {
        Ok(opened) => opened,
        Err(message) => return refuse(message),
    };
    eprint!("{}", crate::colour::stderr(&start.diagnostics));
    let mut session = match start.code.and_then(|code| Session::start(path, args, code)) {
        Ok(session) => session,
        Err(message) => return refuse(message),
    };
    loop {
        if let Some(status) = session.wait(TICK) {
            session.close();
            if profile
                && status != 134
                && let Held::Here(here) = &held
                && let Err(report) = crate::profile::add(
                    path,
                    &here.db,
                    here.synced.program,
                    &stilt_runtime::profile::take(),
                )
            {
                report.print();
            }
            drop(held);
            return ExitCode::from(u8::try_from(status).unwrap_or(1));
        }
        if !profile {
            session.update(held.look());
        }
    }
}

/// Where a run's program is held.
enum Held {
    /// In a database of `run`'s own.
    Here(Box<Here>),
    /// In the program's engine, which sends its code.
    Engine(Remote),
    /// Nowhere: the engine stopped answering, so the run goes on without patching.
    Lost,
}

/// A run's program, held in a database of `run`'s own.
struct Here {
    db: Database,
    synced: Synced,
    counted: Counted,
    lowering: Lowering,
}

impl Held {
    /// The program at `path`, held by its engine if one answers and otherwise here, or here
    /// for a profiled run, with what starting it needs, or why it isn't a program.
    fn open(path: &Path, profile: bool) -> Result<(Self, Start), String> {
        if !profile && let Some((remote, start)) = Remote::start(path) {
            return Ok((Held::Engine(remote), start));
        }
        let db = Database::default();
        let synced = Synced::load(&db, path)?;
        let mut counted = Counted::default();
        let mut lowering = Lowering::default();
        let start = lowering.start(&db, synced.program, &mut counted);
        let here = Here {
            db,
            synced,
            counted,
            lowering,
        };
        Ok((Held::Here(Box::new(here)), start))
    }

    /// What the edits since the last look change in the run.
    fn look(&mut self) -> Update {
        match self {
            Held::Here(here) => {
                let Here {
                    db,
                    synced,
                    counted,
                    lowering,
                } = &mut **here;
                match synced.sync(db) {
                    Ok(true) => lowering.update(db, synced.program, counted),
                    Ok(false) => Update::Unchanged,
                    Err(message) => Update::Unreadable(message),
                }
            }
            Held::Engine(remote) => remote.look().unwrap_or_else(|_| {
                eprintln!(
                    "stilt: the program's engine stopped answering, so later edits aren't patched"
                );
                *self = Held::Lost;
                Update::Unchanged
            }),
            Held::Lost => Update::Unchanged,
        }
    }
}

/// Where the files of the program at `path` are, which debuggers read (goal debuggable-builds).
pub(crate) fn paths(path: &Path) -> Vec<PathBuf> {
    stilt_db::sources(path)
        .unwrap_or_default()
        .into_iter()
        .map(|s| s.file.canonicalize().unwrap_or(s.file))
        .collect()
}
