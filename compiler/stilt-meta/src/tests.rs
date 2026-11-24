//! Tests of what the conformance suite can't show: that each use's expansion is a query of its
//! own, which moving the use or editing another body doesn't run again, and that what a macro
//! reaches is one, which no run reads again while the macro's module doesn't change
//! (macros.running); and that a run that allocates without end stops within the run's
//! memory (macros.step-limits), what it holds weighed whatever its kind ([`limits`]).

mod limits;

use salsa::Setter as _;
use stilt_db::{Database, Program, SourceFile};

const TWICE: &str = "use std.meta

/// The expression, doubled.
pub macro double(e: meta.Expr) -> meta.Expr { quote { $e + $e } }
";

const MAIN: &str = "meta use twice

fn one() -> i64 { twice.double!(1) }

fn two() -> i64 { twice.double!(2) }

fn main() {}
";

const SPELL: &str = "use std.meta

// The text of a pattern.
fn value(pattern: meta.Text) -> str { pattern.value() }

/// The number of characters of a pattern.
pub macro letters(pattern: meta.Text) -> meta.Expr {
  let n = value(pattern).chars().len()
  quote { $n }
}

/// The text of a pattern, as written.
pub macro spelled(pattern: meta.Text) -> meta.Expr {
  let text = value(pattern)
  quote { $text }
}
";

const PATTERNS: &str = "meta use spell

fn line() -> str { spell.spelled!(\"^(\\\\d+) (GET|POST)$\") }

fn host() -> str { spell.spelled!(\"^[a-z]+-\\\\d+$\") }

fn size() -> i64 { spell.letters!(\"abc\") }

fn main() {}
";

const GREEDY: &str = "use std.meta

/// A text that doubles without end.
pub macro grow() -> meta.Expr {
  var s = \"ab\"
  loop { s = \"{s}{s}\" }
}
";

pub(super) fn file(db: &Database, path: &str, text: &str) -> SourceFile {
    let module = path.trim_end_matches(".lt").to_owned();
    stilt_db::source_file(db, path.to_owned(), vec![module], text.as_bytes().to_vec())
}

/// The program of `files`, with the host that runs macros installed.
pub(super) fn program(db: &Database, files: &[(&str, &str)]) -> (Program, Vec<SourceFile>) {
    crate::install();
    let files: Vec<SourceFile> = files.iter().map(|(p, t)| file(db, p, t)).collect();
    (stilt_db::program(db, files.clone()), files)
}

/// The program's diagnostics, as `CODE message`.
pub(super) fn diagnostics(db: &Database, program: Program) -> Vec<String> {
    stilt_types::check(db, program)
        .iter()
        .map(|d| format!("{} {}", d.diagnostic.code, d.diagnostic.message))
        .collect()
}

/// How many macro runs the database made since it was last asked, and how many times it read
/// what a macro reaches.
fn runs_and_reaches(db: &Database) -> (usize, usize) {
    let ran = db.ran();
    let count = |query: &str| ran.iter().filter(|q| q.starts_with(query)).count();
    (count("expansion("), count("reach("))
}

/// How many macro runs the database made since it was last asked.
fn runs(db: &Database) -> usize {
    runs_and_reaches(db).0
}

#[test]
fn moving_a_use_or_editing_another_body_runs_no_macro_again() {
    let mut db = Database::recording();
    let (program, files) = program(&db, &[("main.lt", MAIN), ("twice.lt", TWICE)]);
    assert_eq!(diagnostics(&db, program), Vec::<String>::new());
    assert_eq!(runs(&db), 2);
    // The uses move down a line, and another body changes: each use's tokens, relative to the
    // use, and the macro's module are the same.
    let moved = MAIN
        .replace("fn one", "\nfn one")
        .replace("fn main() {}", "fn main() {\n  let _ = 3\n}");
    files[0].set_bytes(&mut db).to(moved.clone().into_bytes());
    assert_eq!(diagnostics(&db, program), Vec::<String>::new());
    assert_eq!(runs(&db), 0);
    // One use's tokens change: that use expands again, and only it.
    let edited = moved.replace("double!(2)", "double!(3)");
    files[0].set_bytes(&mut db).to(edited.into_bytes());
    assert_eq!(diagnostics(&db, program), Vec::<String>::new());
    assert_eq!(runs(&db), 1);
}

#[test]
fn a_pattern_edit_expands_only_the_use_that_changed() {
    let mut db = Database::recording();
    let (program, files) = program(&db, &[("main.lt", PATTERNS), ("spell.lt", SPELL)]);
    assert_eq!(diagnostics(&db, program), Vec::<String>::new());
    assert_eq!(runs(&db), 3);
    // The pattern of one use changes, as the edit of a regular expression changes its string:
    // that use's macro runs again, and no other's.
    let edited = PATTERNS.replace("[a-z]+", "[a-z0-9]+");
    files[0].set_bytes(&mut db).to(edited.into_bytes());
    assert_eq!(diagnostics(&db, program), Vec::<String>::new());
    assert_eq!(runs(&db), 1);
    // Undoing the edit gives the use its earlier tokens, whose expansion is kept.
    files[0].set_bytes(&mut db).to(PATTERNS.as_bytes().to_vec());
    assert_eq!(diagnostics(&db, program), Vec::<String>::new());
    assert_eq!(runs(&db), 0);
}

#[test]
fn what_a_macro_reaches_is_read_once_while_its_module_does_not_change() {
    let mut db = Database::recording();
    let (program, files) = program(&db, &[("main.lt", PATTERNS), ("spell.lt", SPELL)]);
    assert_eq!(diagnostics(&db, program), Vec::<String>::new());
    // Three runs of two macros: each macro's reach is read once, and its second use's run
    // starts from it.
    assert_eq!(runs_and_reaches(&db), (3, 2));
    // A use's tokens change: its macro runs again, from what it reached before.
    let edited = PATTERNS.replace("\"abc\"", "\"abcd\"");
    files[0].set_bytes(&mut db).to(edited.into_bytes());
    assert_eq!(diagnostics(&db, program), Vec::<String>::new());
    assert_eq!(runs_and_reaches(&db), (1, 0));
    // A function both macros call changes: what each reaches is read again, and each use
    // runs again.
    let other = SPELL.replace("{ pattern.value() }", "{ \"{pattern.value()}\" }");
    files[1].set_bytes(&mut db).to(other.into_bytes());
    assert_eq!(diagnostics(&db, program), Vec::<String>::new());
    assert_eq!(runs_and_reaches(&db), (3, 2));
}

#[test]
fn a_run_that_allocates_without_end_stops() {
    let main = "meta use greedy\n\nfn main() {\n  let _ = greedy.grow!()\n}\n";
    let db = Database::default();
    let (program, _) = program(&db, &[("main.lt", main), ("greedy.lt", GREEDY)]);
    assert_eq!(
        diagnostics(&db, program),
        ["E0226 `greedy.grow!` didn't finish: it ran out of memory; running `grow`"]
    );
}
