//! `stilt show`: prints code with its inferred facts, or a diagnostic code's explanation
//! (Inferred facts, "Seven commands"; goals shown-facts and short-messages).
//!
//! The address says what to show. A code, such as `E0404`, shows its entry in the registry. A
//! module of the program, such as `main`, shows as its skeleton: its header and imports, and
//! its signatures and doc summaries. A part (edits.parts) shows by its path with `/body` for
//! a body, with a hash or without one: a function, such as `main.totals`, a method by its
//! type's or trait's name, such as `main.Point.norm`, or one of a trait impl by both, such as
//! `main.Point.Show.show`, shows under its module's header, which has the module's tier written
//! in, with its own facts written in: the parameters it consumes, the calls at which it loses
//! reuse, the modes of its bindings that aren't at their defaults (modes.show), the sources
//! its views read (views.show), and its `panic` and `alloc`, each with the line that causes
//! it, and with the inferred
//! type of each variable whose type the source doesn't write. A type, trait, constant or test
//! shows as its canonical text under the header, a type that can form a cycle with the fields or
//! variants through which it can (cycles.can-form-cycle), and a body as its canonical text. An
//! address with a hash is refused unless the hash is current (edits.showing-parts). With `--json`,
//! each shows as one JSON record with the fields `at`, `text` and, for a declaration with a body,
//! `body`: a module's with its tier, the records of its functions and the records of its other
//! declarations. A part with holes shows each one's context after it, and its record lists the
//! contexts under `holes` (goal hole-context).

pub(crate) mod release;

use std::path::Path;
use std::process::ExitCode;

use stilt_db::{Database, Program};
use stilt_diag::Code;
pub(crate) use stilt_ide::show::{How, definition, hover};

use crate::engine;
use crate::report::{Report, in_process};

/// Shows what `address` names, in the program at `path` unless it is a diagnostic code: as
/// text for people, or with `json` as JSON records, one per line. An address that names
/// nothing is refused, with the status of a path that isn't a program.
pub(crate) fn command(address: &str, path: &Path, json: bool, expanded: bool) -> ExitCode {
    if let Some(code) = Code::lookup(address) {
        let stdout = if json {
            format!("{}\n", code.explanation_json())
        } else {
            code.explanation()
        };
        return Report {
            stdout,
            ..Report::default()
        }
        .print();
    }
    if is_code(address) {
        let message = format!("`{address}` is no registered diagnostic code");
        return Report::refuse(&message).print();
    }
    let command = engine::Command::Show {
        address: address.to_owned(),
        json,
        expanded,
    };
    let how = How { json, expanded };
    crate::packages::reported(path, false, || {
        engine::ask(path, &command)
            .unwrap_or_else(|| in_process(path, |db, program| show(db, program, address, how)))
    })
    .print()
}

/// Whether `address` is spelled as a diagnostic code is: `E` or `W`, then four digits.
fn is_code(address: &str) -> bool {
    let (first, digits) = address.split_at(address.len().min(1));
    matches!(first, "E" | "W") && digits.len() == 4 && digits.bytes().all(|b| b.is_ascii_digit())
}

/// The view of the module or the parts that `address` names in the program
/// ([`stilt_ide::show::show`]), or its refusal, with the status of a path that isn't a
/// program.
pub(crate) fn show(db: &Database, program: Program, address: &str, how: How) -> Report {
    match stilt_ide::show::show(db, program, address, how) {
        Ok(shown) => Report {
            stdout: shown.stdout,
            stderr: shown.stderr,
            ..Report::default()
        },
        Err(refusal) => Report::refuse(&refusal),
    }
}
