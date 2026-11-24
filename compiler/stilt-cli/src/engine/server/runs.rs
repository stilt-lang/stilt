//! The engine's side of a run (goals edit-to-running-program and one-engine): it lowers the
//! program's code, as `run` would in its own process, and sends it, then answers each of the run's
//! looks with what the edits since the last change in the run, until the run ends and closes the
//! connection. The front end and the MIR run here, once, for every client of the engine; `run`
//! compiles what it receives.

use std::os::unix::net::UnixStream;

use super::super::wire::{Look, Reply, receive, send};
use super::{Engine, Unanswered};
use crate::run::{Lowering, Update};

/// A run, as the engine follows it.
#[derive(Debug, Default)]
struct Run {
    /// Its program's code, as its image holds it.
    lowering: Lowering,
    /// The revision of the program that its image holds.
    seen: u64,
}

impl Engine {
    /// Answers a run, whose connection is counted as being answered, as a command's is, until
    /// what starting it needs is sent; each look is counted then as a command of its own, so
    /// that the run keeps no other command from forgetting results, while its looks keep the
    /// engine from idling.
    pub(super) fn run(&self, stream: &UnixStream) {
        let mut run = Run::default();
        let lowering = &mut run.lowering;
        let start = |db: &_, program| lowering.start(db, program, &mut self.counted());
        let started = match self.answered(start) {
            Ok((start, revision)) => {
                run.seen = revision;
                send(stream, &Reply::Started(start)).is_ok()
            }
            Err(why) => {
                let _ = send(stream, &Reply::Elsewhere(why.message()));
                false
            }
        };
        self.lowered();
        self.end(true);
        if !started {
            return;
        }
        while receive::<Look>(stream).is_ok() {
            self.begin();
            let looked = self.look(&mut run);
            let sent = looked
                .as_ref()
                .is_some_and(|(update, _)| send(stream, update).is_ok());
            self.end(looked.is_some_and(|(_, computed)| computed));
            if !sent {
                return;
            }
        }
    }

    /// What the edits since the run's last look change in it, whichever command took them in,
    /// and whether answering computed anything; or `None` when a query panicked, which ends
    /// the run's connection, so that the run goes on without patching.
    fn look(&self, run: &mut Run) -> Option<(Update, bool)> {
        let revision = match self.held().sync() {
            Ok(revision) => revision,
            Err(message) => return Some((Update::Unreadable(message), false)),
        };
        if revision == run.seen {
            return Some((Update::Unchanged, false));
        }
        let lowering = &mut run.lowering;
        let update = |db: &_, program| lowering.update(db, program, &mut self.counted());
        match self.answered(update) {
            Ok((update, revision)) => {
                run.seen = revision;
                self.lowered();
                Some((update, true))
            }
            Err(Unanswered::Unreadable(message)) => Some((Update::Unreadable(message), true)),
            Err(Unanswered::Panicked) => None,
        }
    }
}
