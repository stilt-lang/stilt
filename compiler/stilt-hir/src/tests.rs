//! Tests of the diagnostics that resolution and declarations place without positions, and of
//! the queries an edit runs again. Expected positions follow from the registry's spans.

use std::sync::Arc;

use salsa::Setter as _;
use stilt_db::{Database, Program, SourceFile};
use stilt_diag::LineIndex;

use crate::check;

/// A directory program of the given files, named by their paths.
fn program(db: &Database, files: &[(&str, &str)]) -> (Program, Vec<SourceFile>) {
    let files: Vec<_> = files
        .iter()
        .map(|&(path, text)| {
            let module = path.trim_end_matches(".lt").split('/').map(str::to_owned);
            stilt_db::source_file(
                db,
                path.to_owned(),
                module.collect(),
                text.as_bytes().to_vec(),
            )
        })
        .collect();
    let program = stilt_db::program(db, files.clone());
    (program, files)
}

/// The diagnostics of a program, as `FILE:LINE:COL: CODE`.
fn diagnostics(files: &[(&str, &str)]) -> Vec<String> {
    let db = Database::recording();
    let (program, _) = program(&db, files);
    check(&db, program)
        .iter()
        .map(|d| {
            let path = d.file.path(&db);
            let text = String::from_utf8_lossy(d.file.bytes(&db));
            let p = LineIndex::new(&text).position(&text, d.diagnostic.range.start());
            format!("{path}:{}:{}: {}", p.line, p.col, d.diagnostic.code)
        })
        .collect()
}

#[test]
fn a_cycle_is_reported_at_its_last_reference() {
    let found = diagnostics(&[
        ("main.lt", "use a\nfn main() {}\n"),
        ("a.lt", "use b\npub const Y: i64 = 1\n"),
        ("b.lt", "use a\nfn f() -> i64 { a.Y }\n"),
    ]);
    // `a` and `b` depend on each other through `use b`, `use a` and the path `a.Y`, which is
    // placed at its first name.
    assert_eq!(found, ["b.lt:2:17: E0206"]);
}

#[test]
fn records_and_constants_in_cycles_are_reported_at_the_last() {
    let found = diagnostics(&[(
        "main.lt",
        "type A = { b: B }\ntype B = { a: A }\nconst X: i64 = Y\nconst Y: i64 = X\nfn main() {}\n",
    )]);
    assert_eq!(found, ["main.lt:2:6: E0309", "main.lt:4:7: E0327"]);
}

/// program.prelude-namespaces: a prelude item's name is taken only in the item's own namespace.
#[test]
fn a_prelude_name_clashes_only_in_its_namespace() {
    let found = diagnostics(&[(
        "main.lt",
        "type Token = | Eq | List(i64) | Less\ntype Option = {}\ntrait Some {}\n\
         fn same<T: Eq>(a: T, b: T) -> bool { Eq.eq(a, b) }\nfn main() {}\n",
    )]);
    assert_eq!(found, ["main.lt:1:33: E0209", "main.lt:2:6: E0209"]);
}

#[test]
fn impl_blocks() {
    let found = diagnostics(&[(
        "main.lt",
        "trait T { fn t(self) -> i64 }\n\
         type P = { x: i64 }\n\
         impl T for P { fn t(self) -> bool { true } }\n\
         impl T for P { fn u(self) {} }\n\
         fn main(x: i64) {}\n",
    )]);
    assert_eq!(
        found,
        [
            "main.lt:3:19: E0307",
            "main.lt:4:1: E0304",
            "main.lt:5:4: E0310"
        ]
    );
}

#[test]
fn a_lexical_error_that_ends_a_trait_s_block_ends_its_last_member() {
    // errors.breaks: the block is read as a file is, so its last member breaks at the error,
    // before its body would open, and declares no signature for an impl to differ from.
    let found = diagnostics(&[(
        "main.lt",
        "trait T {\n  fn t(self) `-> str\n}\n\n\
         type P = { x: i64 }\n\n\
         impl T for P {\n  fn t(self) -> str { \"t\" }\n}\n\n\
         fn main() {}\n",
    )]);
    assert_eq!(found, ["main.lt:2:14: E0002"]);
}

#[test]
fn a_parameter_that_passes_its_effects_through_writes_no_row_variable() {
    // effects.row-variables and effects.closure-parameters, and traits.impl-signatures.
    let found = diagnostics(&[(
        "main.lt",
        "fn a<e>(f: fn() / {io, e}) {}\n\
         fn b<e>(f: fn(fn() / e)) {}\n\
         fn c(f: fn() / alloc) {}\n\
         fn d<e>(escaping f: fn() / e, inout g: fn() / e) / e {}\n\
         trait T { fn t(self, f: fn()) }\n\
         type P = { x: i64 }\n\
         impl T for P { fn t(self, escaping f: fn()) {} }\n\
         fn main() {}\n",
    )]);
    assert_eq!(
        found,
        [
            "main.lt:1:24: E0509",
            "main.lt:2:22: E0509",
            "main.lt:3:16: E0501",
            "main.lt:7:19: E0307"
        ]
    );
}

#[test]
fn a_parenthesized_alternative_is_placed_inside_its_parentheses() {
    let found = diagnostics(&[(
        "main.lt",
        "type S = | A(i64) | B\nfn f(s: S) -> i64 {\n  match s {\n    A(n) | (B) => 0\n  }\n}\n",
    )]);
    assert_eq!(found, ["main.lt:4:13: E0217"]);
}

#[test]
fn a_body_edit_runs_no_query_of_the_whole_program_again() {
    let mut db = Database::recording();
    let (program, files) = program(
        &db,
        &[
            (
                "main.lt",
                "use b\n\nfn main() / io {\n  print(\"{b.twice(2)}\")\n}\n",
            ),
            ("b.lt", "pub fn twice(x: i64) -> i64 { x * 2 }\n"),
        ],
    );
    assert_eq!(check(&db, program), &[]);
    let _ = db.ran_queries();
    let edited = "use b\n\nfn main() / io {\n  let n = 3\n  print(\"{b.twice(n)}\")\n}\n";
    files[0].set_bytes(&mut db).to(edited.as_bytes().to_vec());
    assert_eq!(check(&db, program), &[]);
    let ran = db.ran_queries();
    for whole in [
        "def_map",
        "std_def_map",
        "declarations",
        "import_cycles",
        "constant_cycles",
    ] {
        assert!(
            !ran.iter().any(|q| q == whole),
            "{whole} ran again: {ran:?}"
        );
    }
    let resolved = ran.iter().filter(|q| *q == "resolve_module").count();
    assert_eq!(
        resolved, 1,
        "only the edited module is resolved again: {ran:?}"
    );
}

#[test]
fn an_added_item_resolves_again_only_the_modules_that_look_into_its_module() {
    // Each module's scope is a query of its own, and so is what it says of each name (goal
    // edit-to-diagnostics): `main` looks up `twice` in `b` and nothing in `c`, and the modules'
    // names hold nothing of their items.
    let mut db = Database::recording();
    let (program, files) = program(
        &db,
        &[
            ("b.lt", "pub fn twice(x: i64) -> i64 { x * 2 }\n"),
            ("c.lt", "pub fn one() -> i64 { 1 }\n"),
            (
                "main.lt",
                "use b\n\nfn main() / io {\n  print(\"{b.twice(2)}\")\n}\n",
            ),
        ],
    );
    assert_eq!(check(&db, program), &[]);
    let _ = db.ran_queries();
    let resolved = |db: &mut Database, file: SourceFile, text: &str| {
        file.set_bytes(db).to(text.as_bytes().to_vec());
        check(db, program);
        let ran = db.ran_queries();
        for whole in ["def_map", "std_def_map", "import_cycles"] {
            assert!(!ran.iter().any(|q| q == whole), "{whole} ran: {ran:?}");
        }
        ran.iter().filter(|q| *q == "resolve_module").count()
    };
    let added = "pub fn one() -> i64 { 1 }\npub fn two() -> i64 { 2 }\n";
    assert_eq!(resolved(&mut db, files[1], added), 1, "only `c` itself");
    let added = "pub fn twice(x: i64) -> i64 { x * 2 }\nfn other() {}\n";
    assert_eq!(
        resolved(&mut db, files[0], added),
        1,
        "only `b`, which `main` names no other"
    );
    assert_eq!(check(&db, program), &[]);
    let private = "fn twice(x: i64) -> i64 { x * 2 }\nfn other() {}\n";
    assert_eq!(resolved(&mut db, files[0], private), 2, "`b` and `main`");
    let found = check(&db, program);
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].diagnostic.code.as_str(), "E0213");
}

#[test]
fn a_module_resolved_again_is_held_once() {
    // The projections of a module resolved again share its new parts, even when it comes out
    // as it was, as after a comment added at its end, so that the database holds no older copy
    // beside them (goal bounded-cache).
    let mut db = Database::recording();
    let (program, files) = program(
        &db,
        &[
            ("b.lt", "pub fn twice(x: i64) -> i64 { x * 2 }\n"),
            (
                "main.lt",
                "use b\n\nfn main() / io {\n  print(\"{b.twice(2)}\")\n}\n",
            ),
        ],
    );
    let main = files[1];
    let held_once = |db: &Database| {
        let body = crate::module_body(db, program, main, 0);
        let module = crate::module_hir(db, program, main);
        let resolution = crate::resolve_module(db, program, main);
        Arc::ptr_eq(body, &resolution.bodies[0]) && Arc::ptr_eq(module, &resolution.module)
    };
    assert!(held_once(&db));
    let commented = "use b\n\nfn main() / io {\n  print(\"{b.twice(2)}\")\n}\n// the end\n";
    main.set_bytes(&mut db).to(commented.as_bytes().to_vec());
    let _ = db.ran_queries();
    assert!(held_once(&db));
    let ran = db.ran_queries();
    let resolved = ran.iter().filter(|q| *q == "resolve_module").count();
    assert_eq!(resolved, 1, "`main` is resolved again: {ran:?}");
}

/// The program's text after each fix of its first diagnostic, which must be E0509. The first
/// fix must leave no diagnostic of names or declarations.
fn fixed(text: &str) -> Vec<String> {
    let db = Database::recording();
    let (program, _) = program(&db, &[("main.lt", text)]);
    let found = check(&db, program);
    let first = &found.first().expect("a diagnostic").diagnostic;
    assert_eq!(first.code.as_str(), "E0509", "{found:?}");
    let fixes: Vec<String> = first
        .fixes
        .iter()
        .map(|f| stilt_diag::apply(text, f))
        .collect();
    let left = diagnostics(&[("main.lt", &fixes[0])]);
    assert_eq!(left, Vec::<String>::new(), "{}", fixes[0]);
    fixes
}

#[test]
fn deleting_a_row_variable_that_passes_through_deletes_every_use() {
    // effects.row-variables and effects.closure-parameters: the function's own row, its return type
    // and the other parameters that pass their effects through gain nothing from the variable
    // either.
    let fixes = fixed("fn apply<e>(x: i64, f: fn(i64) -> i64 / e) -> i64 / e {\n  f(x)\n}\n");
    assert_eq!(
        fixes[0],
        "fn apply(x: i64, f: fn(i64) -> i64) -> i64 {\n  f(x)\n}\n"
    );
    assert_eq!(
        fixes[1],
        "fn apply<e>(x: i64, escaping f: fn(i64) -> i64 / e) -> i64 / e {\n  f(x)\n}\n"
    );
    let fixes = fixed("fn b<A, e, B>(f: fn(A) / { io, e }, g: fn(fn() / e) -> B) -> B / e {}\n");
    assert_eq!(
        fixes[0],
        "fn b<A, B>(f: fn(A) / io, g: fn(fn()) -> B) -> B {}\n"
    );
    let fixes = fixed("fn c<e, A>(f: fn() / {e, io, raise<A>}) / {io, e} {}\n");
    assert_eq!(fixes[0], "fn c<A>(f: fn() / {io, raise<A>}) / io {}\n");
}

#[test]
fn a_row_that_goes_keeps_the_rows_after_it_where_they_were() {
    // declarations.function-type-rows: once the returned function type's row goes, the function's
    // own row would go to it, so the returned type is parenthesized.
    let fixes = fixed("fn d<e>(f: fn() / e) -> fn() / e / io {}\n");
    assert_eq!(fixes[0], "fn d(f: fn()) -> (fn()) / io {}\n");
    let fixes = fixed("fn d<e>(f: fn() -> fn() / e / e) {}\n");
    assert_eq!(fixes[0], "fn d(f: fn() -> fn()) {}\n");
    let fixes = fixed("fn d<e>(f: fn() / e) -> fn() -> fn() -> fn() / io / e / e / io {}\n");
    assert_eq!(
        fixes[0],
        "fn d(f: fn()) -> (fn() -> fn() -> fn() / io) / io {}\n"
    );
}

#[test]
fn a_row_variable_that_says_something_of_a_kept_function_stays() {
    // effects.escaping-parameters: where a function is kept, its row is exactly the one written, so
    // the only fix marks the parameter `escaping`.
    for text in [
        "fn e<e>(f: fn() / e, escaping g: fn() / e) / e {}\n",
        "fn e<e>(f: fn() / e, inout g: fn() / e) {}\n",
        "fn e<e>(f: fn() / e, gs: List<fn() / e>) {}\n",
        "fn e<e>(f: fn() / e) {\n  let g: fn() / e = || {}\n}\n",
    ] {
        let fixes = fixed(text);
        assert_eq!(fixes.len(), 1, "{text}");
        assert!(fixes[0].contains("escaping f"), "{text}");
    }
}
