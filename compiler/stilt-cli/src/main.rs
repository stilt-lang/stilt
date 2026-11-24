//! `stilt`, the command of Stilt's compiler. Its commands follow the protocol of
//! conformance.commands.
//!
//! Its place among the crates (`compiler/README.md`): it depends on every crate of the compiler,
//! and none depends on it.

use std::path::Path;
use std::process::ExitCode;

use clap::Parser as _;

mod api_docs;
mod args;
mod bug;
mod build;
mod colour;
mod diagnostic_log;
mod diff;
mod docs;
mod edit;
mod engine;
mod errors;
mod fmt;
mod library;
mod link;
mod lsp;
mod migrate;
mod new;
mod packages;
mod profile;
mod reduce;
mod release;
mod repl;
mod report;
mod run;
mod show;
mod stub;
mod sync;
mod test;
mod wasm;

use args::{Args, Command};
use report::{Report, in_process, text};
use stilt_db::{Database, Program};
use stilt_diag::{Diagnostic, File};

/// The exit status for a path that isn't a program (conformance.run-statuses).
pub(crate) const NOT_A_PROGRAM: u8 = 2;

fn main() -> ExitCode {
    bug::install();
    // Procedural macros run in the compiler (macros.running).
    stilt_meta::install();
    // A package's C libraries are found without loading them (c.finding-libraries).
    stilt_db::install_library_finder(stilt_runtime::c_libraries::finds);
    let command = Args::parse_from(args::program_arguments(std::env::args_os())).command;
    // Checking recurses as deep as code nests, past a main thread's stack for a long sum.
    stilt_db::parallel::deep(|| run(command))
}

/// Runs a command.
fn run(command: Command) -> ExitCode {
    match command {
        Command::Show {
            release: true,
            json,
            address,
            path,
            ..
        } => show::release::command(&address, &path, json),
        Command::Show {
            json,
            expanded,
            address,
            path,
            ..
        } => show::command(&address, &path, json, expanded),
        Command::Build {
            output,
            target,
            release,
            lib,
            path,
        } => build::command(&path, output, target, (release, lib)),
        Command::Repl => repl::command(),
        Command::Run {
            path,
            args,
            profile,
        } => run::run(&path, &args, profile),
        Command::Parse { sexp: _, path } => {
            packages::reported(&path, false, || in_process(&path, parse)).print()
        }
        Command::Check { json, edit, path } => {
            let verdict = || packages::reported(&path, json, || check(&path, json));
            edit::apply(&edit, &path, json, verdict).print()
        }
        Command::Test {
            json,
            std,
            profile,
            edit,
            path,
        } => test_command(&path, json, (std, profile), &edit),
        Command::Fmt { path } => fmt::command(&path),
        Command::Migrate { path } => migrate::command(&path).print(),
        Command::New { lib, path } => new::command(&path, lib).print(),
        Command::Doc { o, json, std, path } => api_docs::command(&path, o.as_deref(), json, std),
        Command::Diff { from, old, new } => diff::command(&old, &new, from.as_deref()).print(),
        engine @ Command::Engine { .. } => engine_command(engine),
        Command::Reduce { o, command } => reduce::command(&command, &o).print(),
        Command::Completions { shell } => args::shells::completions(shell),
        Command::Manual { dir } => args::shells::manual(&dir),
        Command::Lsp => lsp::command(),
    }
}

/// `stilt engine` on the program at its path: stopping its engine, telling it a run ended, or
/// serving it.
fn engine_command(command: Command) -> ExitCode {
    let Command::Engine {
        stop,
        ran,
        record,
        idle,
        path,
    } = command
    else {
        unreachable!("only `stilt engine` is given here")
    };
    if stop {
        engine::stop(&path)
    } else if ran {
        engine::ran(&path)
    } else {
        engine::serve(&path, idle, record)
    }
}

/// `stilt test` on the program at `path`: of the standard library's tests with `std`,
/// counting for the program's profile with `profile`, and otherwise after the edits `edit`.
fn test_command(
    path: &Path,
    json: bool,
    (std, profile): (bool, bool),
    edit: &[String],
) -> ExitCode {
    if std {
        stilt_db::read_std_examples();
        return test::report_std(path, json).print();
    }
    if profile {
        return packages::reported(path, json, || test::report_profiled(path, json)).print();
    }
    let verdict = || packages::reported(path, json, || test::report(path, json));
    edit::apply(edit, path, json, verdict).print()
}

/// The program's diagnostics, by way of its engine if one runs. With a diagnostic log, the
/// check runs in this process, whose variables name the log.
fn check(path: &Path, json: bool) -> Report {
    if let Some(log) = diagnostic_log::path() {
        let report = in_process(path, |db, program| {
            diagnostic_log::record_program(&log, db, program);
            report::check(db, program, json)
        });
        return profile::checked(path, report, json);
    }
    let command = engine::Command::Check { json };
    let report = engine::ask(path, &command)
        .unwrap_or_else(|| in_process(path, |db, program| report::check(db, program, json)));
    profile::checked(path, report, json)
}

/// Ends a command's use of its database, which the process ends with: the system takes its
/// memory back faster than freeing each query's result would. The sanitizers' build frees it,
/// so that `LeakSanitizer` finds only what is lost (goal no-memory-errors).
pub(crate) fn end(db: Database) {
    if cfg!(stilt_sanitizers) {
        drop(db);
    } else {
        std::mem::forget(db);
    }
}

/// The tree of every file, or, if any file has a syntax error, the syntax errors that `check`
/// reports, the first of each part that has one, and nothing on stdout.
fn parse(db: &Database, program: Program) -> Report {
    let mut trees = Vec::new();
    let mut errors = Vec::new();
    for &file in program.files(db) {
        let parse = stilt_db::parse(db, file);
        if parse.errors().is_empty() {
            trees.push(format!(
                "(file {} {})\n",
                stilt_syntax::sexp::quote(file.path(db)),
                stilt_syntax::sexp::module(&parse.tree())
            ));
        } else {
            let text = text(db, file);
            let at = File::new(file.path(db), &text);
            errors.extend(parse.errors().iter().map(|error| line(&at, error)));
        }
    }
    if errors.is_empty() {
        Report {
            stdout: trees.concat(),
            ..Report::default()
        }
    } else {
        Report {
            stderr: errors.concat(),
            status: 1,
            ..Report::default()
        }
    }
}

/// A diagnostic as a line, as `parse` reports syntax errors: `FILE:LINE:COL: CODE: MESSAGE`.
fn line(file: &File<'_>, d: &Diagnostic) -> String {
    let at = file.position(d.range.start());
    format!("{}:{at}: {}: {}\n", file.path, d.code, d.message)
}
