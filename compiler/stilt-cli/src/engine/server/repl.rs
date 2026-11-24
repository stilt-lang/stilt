//! The engine's side of a session of the REPL (repl.sessions; goal one-engine): it holds the
//! session's front, which reads the program's database, and answers each of the session's asks
//! with what its image loads and runs, until the session ends and closes the connection. The
//! front end and the MIR run here, for every client of the engine; the session compiles and runs
//! what it receives. While a session is open, the engine doesn't idle.

use std::os::unix::net::UnixStream;
use std::sync::atomic::Ordering;

use super::super::wire::{Reply, receive, send};
use super::Engine;
use crate::repl::{Ask, Front, Opened};

impl Engine {
    /// Answers a session, whose connection is counted as being answered, as a command's is,
    /// until what it reports first is sent; each ask is counted then as a command of its own.
    pub(super) fn repl(&self, stream: &UnixStream) {
        let opened = self.answered(Front::open);
        let mut front = match opened {
            Ok(((front, report, files), _)) => {
                let opened = Opened { report, files };
                if send(stream, &Reply::Opened(opened)).is_err() {
                    self.end(true);
                    return;
                }
                front
            }
            Err(why) => {
                let _ = send(stream, &Reply::Elsewhere(why.message()));
                self.end(true);
                return;
            }
        };
        self.sessions.fetch_add(1, Ordering::SeqCst);
        self.end(true);
        while let Ok(ask) = receive::<Ask>(stream) {
            self.begin();
            let answer = |db: &_, program| front.ask(db, program, &mut self.counted(), &ask);
            let sent = match self.answered(answer) {
                Ok((answer, _)) => send(stream, &answer).is_ok(),
                Err(_) => false,
            };
            self.end(true);
            if !sent {
                break;
            }
        }
        self.sessions.fetch_sub(1, Ordering::SeqCst);
    }
}
