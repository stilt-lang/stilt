//! What `stilt show ADDRESS` prints, for the playground (`compiler/stilt-cli/src/show.rs`): a
//! diagnostic code's explanation, the skeleton of a module, and a part of the program or of the
//! standard library, a declaration or its body by its path (edits.showing-parts), as its text
//! with its facts written in and each hole's context after it (goal hole-context). The views are
//! `stilt show`'s own ([`stilt_ide::show`]). The page never asks for an address with a hash,
//! which this refuses.

use stilt_diag::Code;
use stilt_ide::show::How;

use crate::report::{Report, in_process};

/// Shows what `address` names, in the program at `path` unless it is a diagnostic code. An
/// address that names nothing is refused, with the status of a path that isn't a program.
pub(crate) fn command(address: &str, path: &str) -> Report {
    if let Some(code) = Code::lookup(address) {
        return Report {
            stdout: code.explanation(),
            ..Report::default()
        };
    }
    if is_code(address) {
        let message = format!("`{address}` is no registered diagnostic code");
        return Report::refuse(&message);
    }
    if stilt_edit::Address::parse(address, false).is_ok_and(|a| a.hash.is_some()) {
        return Report::refuse(&format!("`{address}` has a hash, which isn't shown here"));
    }
    in_process(path, |db, program| {
        let how = How {
            json: false,
            expanded: false,
        };
        match stilt_ide::show::show(db, program, address, how) {
            Ok(shown) => Report {
                stdout: shown.stdout,
                stderr: shown.stderr,
                ..Report::default()
            },
            Err(refusal) => Report::refuse(&refusal),
        }
    })
}

/// Whether `address` is spelled as a diagnostic code is: `E` or `W`, then four digits.
fn is_code(address: &str) -> bool {
    let (first, digits) = address.split_at(address.len().min(1));
    matches!(first, "E" | "W") && digits.len() == 4 && digits.bytes().all(|b| b.is_ascii_digit())
}
