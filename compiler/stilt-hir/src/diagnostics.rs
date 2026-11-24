//! The diagnostics of a program, so far those of its syntax, its names and its declarations
//! (errors.part-reports; errors.registry-phases).

use stilt_db::{Db, Program, SourceFile};
use stilt_diag::{Diagnostic, Edit, Fix, codes};

use crate::consts::constant_cycles;
use crate::cycles::import_cycles;
use crate::decls::declarations;
use crate::exports::export_errors;
use crate::lower::resolve_module;
use crate::scope::{Problem, def_map, module_scope};

/// A diagnostic, with the file it is in.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FileDiagnostic {
    /// The file.
    pub file: SourceFile,
    /// The diagnostic, at a span of the file.
    pub diagnostic: Diagnostic,
}

/// The diagnostics of a program's files, but for those of its fetched packages
/// (packages.dependencies-with-errors): the first syntax error of each part of a file that has one,
/// and each file's errors of names and declarations and its warnings about commented-out code, but
/// for those that a part with a syntax error holds back (errors.part-reports). They are sorted by
/// file, position and code.
#[salsa::tracked(returns(ref))]
pub fn check(db: &dyn Db, program: Program) -> Vec<FileDiagnostic> {
    let files = stilt_db::reported_files(db, program);
    let mut all = Vec::new();
    for &file in files {
        let syntax = stilt_db::syntax_errors(db, file);
        let at = |d: &Diagnostic| FileDiagnostic {
            file,
            diagnostic: d.clone(),
        };
        all.extend(syntax.errors.iter().map(at));
        all.extend(
            file_diagnostics(db, program, file)
                .iter()
                .filter(|d| !syntax.holds_back(d))
                .map(at),
        );
    }
    all.sort_by(|a, b| {
        let key = |d: &FileDiagnostic| {
            (
                d.file.path(db),
                d.diagnostic.range.start(),
                d.diagnostic.code,
            )
        };
        key(a).cmp(&key(b))
    });
    all
}

/// The diagnostics in a file of a program, but for its syntax errors: those of resolving its
/// module, those that the program's declarations, imports and constants have there, and the
/// warnings about its comments, those that a part with a syntax error holds back included.
#[salsa::tracked(returns(ref))]
pub fn file_diagnostics(db: &dyn Db, program: Program, file: SourceFile) -> Vec<Diagnostic> {
    let resolution = resolve_module(db, program, file);
    let place = |code, at, message: &String| {
        Diagnostic::new(code, resolution.anchors.range(at), message.clone())
    };
    let fixed = |p: &Problem| {
        let range = resolution.anchors.range(p.at);
        p.fixes
            .iter()
            .fold(place(p.code, p.at, &p.message), |d, (title, text)| {
                d.with_fix(Fix::new(
                    title.clone(),
                    vec![Edit::replace(range, text.clone())],
                ))
            })
    };
    let mut found = resolution.diagnostics.clone();
    if let Some(module) = def_map(db, program).of_file(file) {
        found.extend(module.problems.iter().map(fixed));
    }
    found.extend(module_scope(db, program, file).problems.iter().map(fixed));
    found.extend(
        declarations(db, program)
            .problems
            .iter()
            .filter(|p| p.file == file)
            .map(|p| place(p.code, p.at, &p.message)),
    );
    found.extend(
        import_cycles(db, program)
            .iter()
            .filter(|c| c.file == file)
            .map(|c| {
                let at = resolution.references[c.reference].1;
                Diagnostic::new(codes::E0206, at, c.message.clone())
            }),
    );
    found.extend(
        constant_cycles(db, program)
            .iter()
            .filter(|c| c.file == file)
            .map(|c| {
                let message = "these constants refer to each other in a cycle".to_owned();
                place(codes::E0327, c.at, &message)
            }),
    );
    found.extend(
        export_errors(db, program)
            .iter()
            .filter(|(f, _)| *f == file)
            .map(|(_, d)| d.clone()),
    );
    found.extend(
        crate::foreign::foreign_errors(db, program, file)
            .iter()
            .cloned(),
    );
    found.extend(stilt_db::syntax_warnings(db, file).iter().cloned());
    found
}
