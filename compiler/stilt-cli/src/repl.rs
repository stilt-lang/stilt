//! `stilt repl`: the REPL, which evaluates expressions and `let`s in a module's scope, and keeps
//! its bindings as the program's files change (repl.sessions; goal interactive-evaluation).
//!
//! - **The program.** The session is on the program in the working directory, a directory
//!   program or a package, whose module `main` it starts in, with its items, its imports and
//!   the prelude; with no program there, it has the prelude alone. `:module NAME` moves it to
//!   another module of the program.
//! - **Inputs.** Each line of standard input is an input: an expression, which answers with
//!   its value and its type, or a `let`, which answers with the type of each name it binds.
//!   An input is checked as a test's body of the module is, and its diagnostics are placed at
//!   `input N`, its number in the session.
//! - **Two sides.** A session's front holds the database's side ([`front`]): it checks each
//!   input, lowers it and counts it, with what it names of the program, as `run` lowers a
//!   program, in the program's engine when it has one, which answers with the functions to
//!   load. Its image holds the code and the bindings' values ([`session`]), and runs each input
//!   on a thread of its own, so that a raise or a panic ends only the input.
//! - **Edits.** Each answer first takes in the edits of the program's files since the last:
//!   the functions they changed are patched into the image, as `run` patches a running program,
//!   and a binding whose type an edit changed is dropped, with a note ([`bindings`]).

mod bindings;
mod front;
mod held;
mod input;
mod session;

use std::io::{IsTerminal as _, Write as _};
use std::path::Path;
use std::process::ExitCode;

pub(crate) use front::{Answer, Ask, Asked, Front};
pub(crate) use held::Opened;

use held::Held;
use session::Session;

/// Runs a session on the program in the working directory, until standard input ends or an
/// input ends the session, and exits with the session's status.
pub(crate) fn command() -> ExitCode {
    let path = Path::new(".");
    let (mut held, opened) = match Held::open(path) {
        Ok(opened) => opened,
        Err(message) => {
            eprintln!("stilt: {message}");
            return ExitCode::from(crate::NOT_A_PROGRAM);
        }
    };
    eprint!("{}", opened.report);
    let mut session = match Session::new(opened.files, crate::run::paths(path)) {
        Ok(session) => session,
        Err(message) => {
            eprintln!("stilt: {}", crate::bug::internal(message));
            return ExitCode::from(1);
        }
    };
    let status = inputs(&mut held, &mut session);
    // An input that panicked left its thread waiting with the image's code on its stack, so the
    // image lasts until the process ends.
    std::mem::forget(session);
    held.close();
    ExitCode::from(u8::try_from(status).unwrap_or(1))
}

/// Reads and answers the session's inputs, and gives the status the session ends with: 0 at
/// the end of standard input, and otherwise the status of the input that ended it.
fn inputs(held: &mut Held, session: &mut Session) -> i32 {
    let terminal = std::io::stdin().is_terminal();
    let mut number = 0;
    loop {
        if terminal {
            print!("> ");
            let _ = std::io::stdout().flush();
        }
        // The standard library's `read_line` reads from the same buffer, so that an input that
        // reads a line reads the next one.
        let Some(line) = stilt_runtime::input_line() else {
            return 0;
        };
        let text = line.trim();
        if text.is_empty() {
            continue;
        }
        number += 1;
        let Some(ask) = ask(text, number, session) else {
            continue;
        };
        match held.ask(&ask) {
            Ok(answer) => {
                if let Some(status) = session.take(answer) {
                    return status;
                }
            }
            Err(message) => {
                eprintln!("stilt: {message}");
                return 1;
            }
        }
    }
}

/// What the input asks of the session's front, or `None` for a command the REPL doesn't know,
/// which it refuses.
fn ask(text: &str, number: u32, session: &Session) -> Option<Ask> {
    let what = match text.strip_prefix(':') {
        None => Asked::Input {
            text: text.to_owned(),
            number,
        },
        Some(command) => {
            let words: Vec<&str> = command.split_whitespace().collect();
            let ["module", name] = words.as_slice() else {
                eprintln!("stilt: input {number} is no command: the REPL knows `:module NAME`");
                return None;
            };
            Asked::Module((*name).to_owned())
        }
    };
    Some(Ask {
        live: session.live(),
        what,
    })
}
