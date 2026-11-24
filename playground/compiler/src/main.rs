//! `stilt-playground`: what `stilt check` and `stilt show` print for a program of one file,
//! with the facts that the language server writes beside each function, built for WebAssembly
//! (`wasm32-wasip1`), which the playground's page runs in the browser through a WASI host of its
//! own (playground/README.md). Its commands take the arguments of `stilt`'s and print what they
//! print, from the same code: this crate compiles the modules of `stilt show` and of the reports
//! of `stilt check` from the command's sources, and writes here only what joins them.
//!
//! - `check [--json] PATH` prints the program's diagnostics, as `stilt check` does;
//! - `show ADDRESS PATH` prints what `stilt show` prints of a diagnostic code, of module `main`
//!   or of a part of it;
//! - `live PATH` prints, as one JSON object, what the page shows as one types: the diagnostics as
//!   `check --json` gives them, each also rendered for people, and the facts of each function.

mod hints;
mod report;
mod show;

use std::process::ExitCode;

use serde_json::json;
use stilt_db::{Database, Program};

use report::{Report, in_process};

/// What the commands take.
const USAGE: &str = "usage: stilt-playground check [--json] PATH | show ADDRESS PATH | live PATH";

fn main() -> ExitCode {
    // Procedural macros run in the compiler (macros.running).
    stilt_meta::install();
    let args: Vec<String> = std::env::args().skip(1).collect();
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    let report = match args.as_slice() {
        ["check", path] => in_process(path, |db, program| report::check(db, program, false)),
        ["check", "--json", path] => {
            in_process(path, |db, program| report::check(db, program, true))
        }
        ["show", address, path] => show::command(address, path),
        ["live", path] => in_process(path, live),
        _ => Report::refuse(USAGE),
    };
    report.print()
}

/// The program's diagnostics, each as its JSON record and rendered for people, and the facts of
/// each function, as one JSON object on stdout.
fn live(db: &Database, program: Program) -> Report {
    let found = report::diagnostics(db, program);
    let record = json!({
        "diagnostics": found.entries,
        "rendered": found.rendered,
        "functions": hints::functions(db, program),
    });
    Report {
        stdout: format!("{record}\n"),
        status: u8::from(found.errors),
        ..Report::default()
    }
}
