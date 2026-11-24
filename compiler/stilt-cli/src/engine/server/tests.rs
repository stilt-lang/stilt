//! The engine's side of a run of tests (program.running-tests; goals one-verdict and
//! repeated-failures-flagged): it checks the program and lowers the entries of its tests, as `test`
//! would in its own process, reusing the results it remembers, and sends them; it then takes the
//! results of the run and remembers them, with the program's files when the verdict wasn't done.

use std::os::unix::net::UnixStream;
use std::sync::{MutexGuard, PoisonError};

use super::super::wire::{Reply, receive, send};
use super::Engine;
use crate::test::{Memory, plan};

impl Engine {
    fn memory(&self) -> MutexGuard<'_, Memory> {
        self.tests.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Answers a run of tests, whose connection is counted as being answered until its results
    /// are remembered, so that the engine doesn't idle while the tests run.
    pub(super) fn test(&self, stream: &UnixStream, json: bool) {
        let planned = self
            .answered(|db, program| plan(db, program, json, &mut self.counted(), &self.memory()));
        let keys = match planned {
            Ok(((plan, keys), _)) => {
                if send(stream, &Reply::Tested(plan)).is_err() {
                    return;
                }
                keys
            }
            Err(why) => {
                let _ = send(stream, &Reply::Elsewhere(why.message()));
                return;
            }
        };
        if let Ok(results) = receive::<Vec<crate::test::Ran>>(stream) {
            self.memory().record(&keys, &results);
            let _ = send(stream, &Reply::Recorded);
        }
    }
}
