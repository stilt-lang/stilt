//! Tests of the keys of instances: a type parameter is keyed by its argument's layout, and by
//! its constructor too where a bound has methods of their own type parameters, whose calls the
//! instance then makes directly; and generic code that calls itself with ever bigger types has
//! finitely many instances.

use stilt_db::{Database, program, source_file};

use super::MAX_KNOWN;
use crate::FnRef;
use crate::check_errors::CheckErrors;
use crate::walk::reached_from;

const P: &str = "type P = { x: i64, y: i64 }\n\n";

const CHOOSER: &str = "trait Chooser {\n  fn wrap<T>(self, a: T) -> Option<T>\n}\n\ntype W = { first: bool }\n\nimpl Chooser for W {\n  fn wrap<T>(self, a: T) -> Option<T> { if self.first { Some(a) } else { None } }\n}\n\ntype Flip<C> = { inner: C }\n\nimpl<C: Chooser> Chooser for Flip<C> {\n  fn wrap<T>(self, a: T) -> Option<T> { self.inner.wrap(a) }\n}\n\ntype Plain<T> = { value: T }\n\nimpl<T> Chooser for Plain<T> {\n  fn wrap<U>(self, a: U) -> Option<U> { Some(a) }\n}\n\n";

/// The functions that the entry of the program `main` reaches, by name, as MIR prints them.
fn reached(main: &str) -> Vec<(String, String)> {
    let db = Database::default();
    let file = source_file(&db, "main.lt".into(), vec!["main".into()], main.into());
    let program = program(&db, vec![file]);
    reached_from(&db, program, &[FnRef::Main], &CheckErrors::default())
        .functions
        .iter()
        .map(|f| (f.name.to_string(), crate::print(f)))
        .collect()
}

/// The MIR of the function `name` among those reached.
fn code<'a>(reached: &'a [(String, String)], name: &str) -> &'a str {
    reached
        .iter()
        .find(|(n, _)| n == name)
        .map_or_else(|| panic!("{name} isn't reached"), |(_, mir)| mir.as_str())
}

#[test]
fn a_bound_with_methods_of_their_own_type_parameters_keys_its_argument_by_constructor() {
    let main = format!(
        "{P}{CHOOSER}fn get<C: Chooser>(c: C, p: P) -> i64 {{\n  match c.wrap(p) {{\n    Some(q) => q.x\n    None => 0\n  }}\n}}\n\nfn main() / io {{\n  let p = P {{ x: 1, y: 2 }}\n  let w = W {{ first: true }}\n  print(\"{{get(w, p)}} {{get(Flip {{ inner: w }}, p)}} {{get(Plain {{ value: p }}, p)}}\")\n}}\n"
    );
    let reached = reached(&main);
    for (caller, callee) in [
        ("main.get<main.W[]>", "<main.W as main.Chooser>.wrap<ss>"),
        (
            "main.get<main.Flip[main.W[]]>",
            "<main.Flip as main.Chooser>.wrap<main.W[],ss>",
        ),
        (
            "<main.Flip as main.Chooser>.wrap<main.W[],ss>",
            "<main.W as main.Chooser>.wrap<ss>",
        ),
        (
            "main.get<main.Plain[ss]>",
            "<main.Plain as main.Chooser>.wrap<ss,ss>",
        ),
    ] {
        let mir = code(&reached, caller);
        assert!(mir.contains(&format!("{callee}(")), "{mir}");
        assert!(!mir.contains("#0("), "a call through a dictionary in {mir}");
    }
}

#[test]
fn a_bound_without_such_methods_keys_its_argument_by_layout_alone() {
    let main = format!(
        "{P}fn shown<T: Show>(x: T) -> str {{ \"{{x}}\" }}\n\nfn main() / io {{\n  print(shown(P {{ x: 1, y: 2 }}))\n}}\n"
    );
    code(&reached(&main), "main.shown<ss>");
}

#[test]
fn polymorphic_recursion_through_such_a_bound_has_finitely_many_instances() {
    let main = format!(
        "{P}{CHOOSER}fn deep<C: Chooser>(c: C, n: i64, p: P) -> i64 {{\n  if n == 0 {{\n    match c.wrap(p) {{\n      Some(q) => q.x\n      None => 0\n    }}\n  }} else {{\n    deep(Flip {{ inner: c }}, n - 1, p)\n  }}\n}}\n\nfn main() / io {{\n  print(\"{{deep(W {{ first: true }}, 3, P {{ x: 1, y: 2 }})}}\")\n}}\n"
    );
    let reached = reached(&main);
    let deep = reached
        .iter()
        .filter(|(n, _)| n.starts_with("main.deep"))
        .count();
    // Each constructor a key knows is an instance, and past them one more, for the layout
    // alone, whose calls go past the caps.
    assert!(deep > MAX_KNOWN, "{deep} instances");
    assert!(deep <= MAX_KNOWN + 2, "{deep} instances");
}
