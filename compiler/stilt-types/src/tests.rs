//! Tests of the queries: what a body elaborates to, which phases report, and what an edit runs
//! again. Expected positions follow from the registry's spans.

use std::fmt::Write as _;

use salsa::Setter as _;
use stilt_db::{Database, Program, SourceFile};
use stilt_diag::LineIndex;

use crate::tast::{Code, Definition, ExprKind, StmtKind};
use crate::ty::Ty;
use crate::{check, check_in_parallel, infer_body};

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

/// The diagnostics of a program of one file, as `LINE:COL: CODE`.
fn diagnostics(text: &str) -> Vec<String> {
    let db = Database::recording();
    let (program, _) = program(&db, &[("main.lt", text)]);
    let index = LineIndex::new(text);
    check(&db, program)
        .iter()
        .map(|d| {
            let p = index.position(text, d.diagnostic.range.start());
            format!("{}:{}: {}", p.line, p.col, d.diagnostic.code)
        })
        .collect()
}

#[test]
fn each_body_reports_its_first_phase_with_errors() {
    // errors.phases: a type error hides the body's later errors, a later error hides its
    // warnings, and each body is checked on its own.
    let found = diagnostics(
        "fn typed() -> i64 {\n  let n = 0\n  n += 1\n  \"one\"\n}\n\
         fn analysed() -> i64 {\n  let n = 0\n  n += 1\n  try n\n}\n\
         fn warned() -> i64 {\n  try 1\n}\n",
    );
    assert_eq!(found, ["4:3: E0311", "8:3: E0403", "12:3: W0500"]);
}

#[test]
fn a_member_of_an_impl_kept_out_of_the_program_is_not_compared() {
    // docs.bodies-compared: the error keeps an impl of an unknown type out of the program
    // (program.errors-outside-bodies), so its member is no method whose body a function copies.
    let body = "{ p.0 * p.0 + p.1 * p.1 + p.0 * p.1 }";
    let found = diagnostics(&format!(
        "impl Nope {{\n  fn norm(p: (i64, i64)) -> i64 {body}\n}}\n\
         fn norm_of(p: (i64, i64)) -> i64 {body}\n"
    ));
    assert_eq!(found, ["1:6: E0211"]);
}

#[test]
fn literals_take_their_default_types() {
    let db = Database::recording();
    let (program, files) = program(
        &db,
        &[("main.lt", "fn f() -> f64 {\n  let n = 3\n  2.5\n}\n")],
    );
    let body = &infer_body(&db, program, files[0], 0).body;
    let Definition::Code(Code::Block(block)) = &body.code else {
        panic!("the body has no errors: {body:?}");
    };
    let types: Vec<&Ty> = block
        .iter()
        .map(|s| match &s.kind {
            StmtKind::Let(b) => &b.value.ty,
            StmtKind::Expr(e) => &e.ty,
            other => panic!("unexpected statement {other:?}"),
        })
        .collect();
    assert_eq!(types, [&Ty::i64(), &Ty::f64()]);
}

#[test]
fn a_read_through_an_option_is_a_match() {
    let db = Database::recording();
    let (program, files) = program(
        &db,
        &[(
            "main.lt",
            "type P = { x: i64 }\nfn f(p: Option<P>) -> Option<i64> {\n  p.x\n}\n",
        )],
    );
    let body = &infer_body(&db, program, files[0], 0).body;
    let Definition::Code(Code::Block(block)) = &body.code else {
        panic!("the body has no errors: {body:?}");
    };
    let StmtKind::Expr(e) = &block[0].kind else {
        panic!("the body is one expression");
    };
    // types.fields-through-option.
    assert!(matches!(e.kind, ExprKind::Match(..)), "{e:?}");
    assert_eq!(e.ty, Ty::option(Ty::i64()));
}

#[test]
fn a_body_edit_checks_only_that_body_again() {
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
    let inferred = ran.iter().filter(|q| *q == "infer_body").count();
    assert_eq!(
        inferred, 1,
        "only the edited body is checked again: {ran:?}"
    );
    assert!(!ran.iter().any(|q| q == "declarations"), "{ran:?}");
}

#[test]
fn a_check_after_its_typed_bodies_are_forgotten_checks_only_what_an_edit_changed() {
    // goal bounded-cache: an engine forgets the typed bodies once a build has lowered them,
    // and checking the program again, in parallel as an engine does, proves the others checked
    // without their typed bodies.
    let mut db = Database::recording();
    crate::keep_typed(&mut db, usize::MAX);
    let lib = "pub fn twice(x: i64) -> i64 { x * 2 }\n\npub fn thrice(x: i64) -> i64 { x * 3 }\n";
    let (program, files) = program(
        &db,
        &[
            (
                "main.lt",
                "use b\n\nfn main() / io {\n  print(\"{b.twice(2)}\")\n}\n",
            ),
            ("b.lt", lib),
        ],
    );
    assert_eq!(check_in_parallel(&db, program), &[]);
    crate::keep_typed(&mut db, 1);
    salsa::Database::trigger_lru_eviction(&mut db);
    crate::keep_typed(&mut db, usize::MAX);
    let _ = db.ran_queries();
    assert_eq!(check_in_parallel(&db, program), &[]);
    assert_eq!(
        db.ran_queries(),
        Vec::<String>::new(),
        "nothing is checked again"
    );
    let edited = "use b\n\nfn main() / io {\n  let n = 3\n  print(\"{b.twice(n)}\")\n}\n";
    files[0].set_bytes(&mut db).to(edited.as_bytes().to_vec());
    assert_eq!(check_in_parallel(&db, program), &[]);
    let ran = db.ran_queries();
    let inferred = ran.iter().filter(|q| *q == "infer_body").count();
    assert_eq!(
        inferred, 1,
        "only the edited body is checked again: {ran:?}"
    );
}

#[test]
fn a_new_panic_checks_only_its_body_again() {
    // goal body-edits-recheck-one-body: the callee's new panic is an error in its caller, limited
    // by `without panic` (effects.without-panic), which the caller's analyses find without type
    // checking it again.
    let mut db = Database::recording();
    let (program, files) = program(
        &db,
        &[
            (
                "main.lt",
                "use pure\n\nfn main() / io {\n  print(\"{pure.twice(2)}\")\n}\n",
            ),
            (
                "pure.lt",
                "module pure\nwithout panic\n\nuse lib\n\npub fn twice(n: i64) -> i64 {\n  lib.double(n)\n}\n",
            ),
            ("lib.lt", "pub fn double(n: i64) -> i64 {\n  n * 2\n}\n"),
        ],
    );
    assert_eq!(check(&db, program), &[]);
    let _ = db.ran_queries();
    let edited = "pub fn double(n: i64) -> i64 {\n  assert n > 0\n  n * 2\n}\n";
    files[2].set_bytes(&mut db).to(edited.as_bytes().to_vec());
    let found: Vec<_> = check(&db, program)
        .iter()
        .map(|d| (d.file.path(&db).clone(), d.diagnostic.code))
        .collect();
    assert_eq!(found, [("pure.lt".to_owned(), stilt_diag::codes::E0204)]);
    let ran = db.ran_queries();
    let inferred = ran.iter().filter(|q| *q == "infer_body").count();
    assert_eq!(
        inferred, 1,
        "only the edited body is checked again: {ran:?}"
    );
}

#[test]
fn a_parameter_passes_its_arguments_effects_through() {
    // effects.non-escaping-parameters: `twice` writes no effect, and its caller marks the raise of
    // its argument.
    let found = diagnostics(
        "fn twice(x: i64, f: fn(i64) -> i64) -> i64 { f(f(x)) }\n\
         fn half(n: i64) -> i64 / raise<str> {\n  if n % 2 != 0 { raise \"odd\" }\n  n / 2\n}\n\
         fn main() / {io, raise<str>} {\n  let n = try twice(12, half)\n  print(\"{n}\")\n}\n",
    );
    assert_eq!(found, Vec::<String>::new());
}

#[test]
fn a_parameter_that_escapes_is_reported_once_where_it_first_does() {
    // effects.escaping-parameters: the escape is the error, rather than the row that doesn't hold
    // the parameter's implicit row variable, and each parameter gets one.
    let found = diagnostics(
        "type B = { f: fn() / io }\n\
         fn stored(f: fn() / io) -> B {\n  let g = || f()\n  B { f }\n}\n\
         fn kept(escaping f: fn() / io) -> B { B { f } }\n\
         fn row<e>(f: fn() / e) {}\n",
    );
    assert_eq!(found, ["3:11: E0508", "7:21: E0509"]);
}

/// The code of a program's first diagnostic, and the program's text after its first fix.
fn first_fixed(text: &str) -> (&'static str, String) {
    let db = Database::recording();
    let (program, _) = program(&db, &[("main.lt", text)]);
    let found = check(&db, program);
    let first = &found.first().expect("a diagnostic").diagnostic;
    let fix = first.fixes.first().expect("a fix");
    (first.code.as_str(), stilt_diag::apply(text, fix))
}

#[test]
fn a_row_written_after_a_returned_function_type_parenthesizes_it() {
    // declarations.function-type-rows: a row after a function type with none would go to that type,
    // so the fixes that write a row in a parameter's type or in the signature parenthesize it.
    let caught = "type E = | Empty\nfn parse() -> i64 / raise<E> { raise Empty }\n\
                  fn safe(make: fn() -> fn()) -> i64 {\n  \
                  try {\n    let run = make()\n    run()\n    parse()\n  } catch _ because \"none\" => 0\n}\n";
    let (code, fixed) = first_fixed(caught);
    assert_eq!(code, "E0506");
    assert!(fixed.contains("fn safe(make: fn() -> (fn()) / raise<E>) -> i64 {"));
    let rowed = "type Box = { v: i64 }\n\
                 fn wrap(g: fn() -> fn() / io) -> Result<fn() / io, Box> {\n  Result.of(g)\n}\n";
    let (code, fixed) = first_fixed(rowed);
    assert_eq!(code, "E0507");
    assert!(fixed.contains("fn wrap(g: fn() -> fn() / io / raise<Box>) ->"));
    let passed = "type Box = { v: i64 }\n\
                  fn wrap(g: fn() -> fn()) -> Result<fn(), Box> {\n  Result.of(g)\n}\n";
    let (code, fixed) = first_fixed(passed);
    assert_eq!(code, "E0507");
    assert!(fixed.contains("fn wrap(g: fn() -> (fn()) / raise<Box>) ->"));
    let printing = "fn make() -> fn() {\n  print(\"made\")\n  || {}\n}\n";
    let (code, fixed) = first_fixed(printing);
    assert_eq!(code, "E0502");
    assert!(fixed.starts_with("fn make() -> (fn()) / io {"));
    for text in [caught, rowed, passed, printing] {
        let fixed = first_fixed(text).1;
        assert_eq!(diagnostics(&fixed), Vec::<String>::new(), "{fixed}");
    }
}

#[test]
fn bodies_checked_in_parallel_report_what_checking_in_order_does() {
    // Each body is checked on its own (errors.phases), so the order the threads take them in
    // changes nothing of the diagnostics, nor of their order.
    let module = |m: usize| {
        let mut text = String::new();
        for f in 0..40 {
            let _ = writeln!(text, "pub fn f{f}(x: i64) -> i64 {{\n  x + {f}\n}}");
            if f % 7 == m % 7 {
                let _ = writeln!(text, "fn g{f}() -> i64 {{\n  \"{f}\"\n}}");
            }
        }
        (format!("m{m}.lt"), text)
    };
    let modules: Vec<(String, String)> = (0..8).map(module).collect();
    let files: Vec<(&str, &str)> = modules
        .iter()
        .map(|(path, text)| (path.as_str(), text.as_str()))
        .collect();
    let shown = |db: &Database, found: &[stilt_hir::FileDiagnostic]| -> Vec<_> {
        found
            .iter()
            .map(|d| (d.file.path(db).clone(), d.diagnostic.clone()))
            .collect()
    };
    let in_order = Database::recording();
    let (checked, _) = program(&in_order, &files);
    let expected = shown(&in_order, check(&in_order, checked));
    assert!(expected.len() > 8, "{expected:?}");
    let parallel = Database::recording();
    let (checked, _) = program(&parallel, &files);
    assert_eq!(
        shown(&parallel, check_in_parallel(&parallel, checked)),
        expected
    );
}

/// The diagnostics of one property over a type, with the declarations it needs.
fn property(decls: &str, ty: &str) -> Vec<String> {
    diagnostics(&format!("{decls}\n/// prop: |x: {ty}| true\nfn f() {{}}\n"))
}

#[test]
fn a_type_that_holds_infinitely_many_types_is_not_generable() {
    // tests.growth-test: a cycle with a growing edge, through itself, through a tuple, through
    // another declaration, or through a type that holds one.
    let grow = "type Grow<T> = | Stop | More(Grow<List<T>>)";
    assert_eq!(property(grow, "Grow<i64>"), ["2:15: E0333"]);
    let tuple = "type P<T> = | Z | S(P<(T, T)>)";
    assert_eq!(property(tuple, "P<bool>"), ["2:15: E0333"]);
    let mutual = "type Ping<T> = | End | Ping(Pong<List<T>>)\ntype Pong<T> = | Pong(Ping<T>)";
    assert_eq!(property(mutual, "Pong<i64>"), ["3:15: E0333"]);
    let via = format!("{grow}\ntype Via<T> = {{ next: Option<Grow<T>> }}");
    assert_eq!(property(&via, "List<Via<u8>>"), ["3:15: E0333"]);
}

#[test]
fn a_type_that_holds_finitely_many_types_is_generable() {
    // tests.growth-test: a cycle without a growing edge, an argument that mentions no parameter,
    // and a growing edge on no cycle.
    let cases = [
        ("type Bin<T> = | Leaf(T) | Node(Bin<T>, Bin<T>)", "Bin<str>"),
        ("type A<T> = | X | Y(A<i64>)", "A<bool>"),
        (
            "type Swap<T, U> = | Done | Next(Swap<U, T>)",
            "Swap<i64, str>",
        ),
        (
            "type Wrap<T> = | Wrap(List<T>)\ntype Outer<T> = | Outer(Wrap<List<T>>)",
            "Outer<u8>",
        ),
    ];
    for (decls, ty) in cases {
        assert_eq!(property(decls, ty), Vec::<String>::new(), "{ty}");
    }
}
