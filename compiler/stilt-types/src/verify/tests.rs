//! Tests of the analysis of verification (facts.verification): what it proves of small
//! bodies, which release builds read, each case taken from the record's required tests and the
//! findings of its reviews, with the verdicts the record's rules give by reasoning.

mod calls;
mod conds;
mod dbm;
mod divisions;
mod exprs;
mod jumps;
mod loops;
mod order;
mod paths;
mod values;

pub(crate) use stilt_db::Database;
use stilt_db::{Program, SourceFile};
use stilt_diag::LineIndex;

use super::{Check, Proofs, verified};
use crate::owners::BodyOwner;
use crate::queries::{body_count, body_owner};

pub(crate) fn program(db: &Database, text: &str) -> (Program, SourceFile) {
    let file = stilt_db::source_file(
        db,
        "main.lt".to_owned(),
        vec!["main".to_owned()],
        text.as_bytes().to_vec(),
    );
    (stilt_db::program(db, vec![file]), file)
}

/// The index of the body of the function `name` of a program of one file.
pub(crate) fn body_of(db: &Database, program: Program, file: SourceFile, name: &str) -> u32 {
    (0..body_count(db, program, file))
        .find(|&i| matches!(body_owner(db, program, file, i), BodyOwner::Fn { name: n, .. } if &**n == name))
        .unwrap_or_else(|| panic!("no function `{name}`"))
}

/// The program's diagnostics, which must hold no error but E0204, the errors of limits that
/// the rules of acceptance decide.
fn checked(db: &Database, program: Program) {
    let diagnostics = crate::check(db, program);
    let errors: Vec<_> = diagnostics
        .iter()
        .filter(|d| d.diagnostic.is_error() && d.diagnostic.code.as_str() != "E0204")
        .collect();
    assert!(errors.is_empty(), "the program has errors: {errors:?}");
}

/// The verdicts of the analysis on the function `name` of a program of one file, each as
/// `LINE:COL VERDICT`: `bounds`, `divide-by-zero`, `missing-key` or `overflow` for a check it
/// proves, and `no bounds` and the others for one it doesn't.
fn verdicts(text: &str, name: &str) -> Vec<String> {
    let db = Database::default();
    let (program, file) = program(&db, text);
    checked(&db, program);
    let index = body_of(&db, program, file, name);
    let start = stilt_hir::body_starts(&db, program, file)[index as usize];
    render(text, start, verified(&db, program, file, index))
}

fn word(c: Check) -> &'static str {
    match c {
        Check::Bounds => "bounds",
        Check::DivideByZero => "divide-by-zero",
        Check::MissingKey => "missing-key",
        Check::Overflow => "overflow",
    }
}

fn render(text: &str, start: stilt_syntax::TextSize, proofs: &Proofs) -> Vec<String> {
    let lines = LineIndex::new(text);
    let at = |r: stilt_syntax::TextRange| {
        let p = lines.position(text, r.start() + start);
        format!("{}:{}", p.line, p.col)
    };
    let mut out: Vec<String> = proofs
        .proved
        .iter()
        .map(|p| format!("{} {}", at(p.at), word(p.check)))
        .collect();
    out.extend(
        proofs
            .unproved
            .iter()
            .map(|(r, c)| format!("{} no {}", at(*r), word(*c))),
    );
    out
}

/// The verdicts but those of overflow.
fn checks(text: &str, name: &str) -> Vec<String> {
    verdicts(text, name)
        .into_iter()
        .filter(|v| !v.ends_with("overflow"))
        .collect()
}

/// Whether `found` holds the verdict `v`, for a message that shows them all.
#[track_caller]
fn has(found: &[String], v: &str) {
    assert!(found.iter().any(|f| f == v), "no `{v}` in {found:#?}");
}

/// The checks of every function of the program that the analysis doesn't prove, but those of
/// overflow, each once as `LINE:COL no KIND`, in the order of the text.
fn unproved(text: &str) -> Vec<String> {
    let db = Database::default();
    let (program, file) = program(&db, text);
    checked(&db, program);
    let lines = LineIndex::new(text);
    let mut found = Vec::new();
    for index in 0..body_count(&db, program, file) {
        if !matches!(body_owner(&db, program, file, index), BodyOwner::Fn { .. }) {
            continue;
        }
        let start = stilt_hir::body_starts(&db, program, file)[index as usize];
        for (r, c) in &verified(&db, program, file, index).unproved {
            if *c != Check::Overflow {
                found.push((r.start() + start, *c));
            }
        }
    }
    found.sort_unstable_by_key(|(at, c)| (*at, word(*c)));
    found.dedup();
    found
        .into_iter()
        .map(|(at, c)| {
            let p = lines.position(text, at);
            format!("{}:{} no {}", p.line, p.col, word(c))
        })
        .collect()
}

#[test]
fn the_sieve_is_total() {
    let text = "module main\nwithout panic, div\n\n\
                fn clear_multiples(m: i64) -> List<bool> {\n\
                \x20 var flags = []\n\
                \x20 for _ in 0..m + 1 { flags.push(true) }\n\
                \x20 for i in 2..m + 1 {\n\
                \x20   var k = i + i\n\
                \x20   while k <= m {\n\
                \x20     flags[k] = false\n\
                \x20     k += i\n\
                \x20   }\n\
                \x20 }\n\
                \x20 flags\n\
                }\n";
    let found = checks(text, "clear_multiples");
    has(&found, "10:7 bounds");
    assert_eq!(unproved(text), Vec::<String>::new());
}
