//! Checking a program's bodies across the machine's cores (Compiler architecture, "Queries";
//! goal clean-check). Each body is checked on its own against the declarations' signatures,
//! so the bodies are checked in parallel, in waves: every file is parsed; every module is
//! resolved; every body of the program is type checked; when a `without` limits one to no
//! `panic` or no `alloc`, every function is summarized and the implicit effects of the program
//! found (facts.inference); and every body of the program gets the diagnostics of every phase.
//! Each wave runs queries that checking in order runs, and no others. [`check`] then finds every body done, and gathers their diagnostics in its own
//! order, so the result is the one checking them in order gives, byte for byte.

use stilt_db::{Db, Program, SourceFile, parallel};
use stilt_hir::{FileDiagnostic, resolve_module};

use crate::copies::body_print;
use crate::queries::{
    body_count, body_diagnostics, body_summary, broken, check, implicit_effects, reads_effects,
};

/// The diagnostics of a program, as [`check`] gives them, with its bodies checked in parallel.
pub fn check_in_parallel<D: Db + Clone>(db: &D, program: Program) -> &[FileDiagnostic] {
    let own = stilt_db::reported_files(db, program);
    parallel::for_each(db, own, |db, &file| {
        stilt_db::syntax_errors(db, file);
    });
    prime(db, program);
    check(db, program)
}

fn prime<D: Db + Clone>(db: &D, program: Program) {
    let files: Vec<SourceFile> = program
        .std(db)
        .iter()
        .chain(program.files(db))
        .copied()
        .collect();
    parallel::for_each(db, &files, |db, &file| {
        resolve_module(db, program, file);
    });
    let bodies = |files: &[SourceFile]| -> Vec<(SourceFile, u32)> {
        files
            .iter()
            .flat_map(|&file| (0..body_count(db, program, file)).map(move |i| (file, i)))
            .collect()
    };
    let own = bodies(program.files(db));
    parallel::for_each(db, &own, |db, &(file, index)| {
        // A small result of type checking, which proves the body checked without reading its
        // typed body, which an engine may have forgotten (goal bounded-cache).
        broken(db, program, file, index);
    });
    if own.iter().any(|&(f, i)| reads_effects(db, program, f, i)) {
        parallel::for_each(db, &bodies(&files), |db, &(file, index)| {
            body_summary(db, program, file, index);
        });
        implicit_effects(db, program);
    }
    parallel::for_each(db, &own, |db, &(file, index)| {
        body_diagnostics(db, program, file, index);
        body_print(db, program, file, index);
    });
}
