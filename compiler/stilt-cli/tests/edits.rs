//! The addresses of parts, their hashes, `show` with an address and the `at` of diagnostics
//! (edits.parts, edits.hash and edits.diagnostic-addresses). No conformance test observes them, so
//! these are their tests. The hashes in the expectations are BLAKE3 digests of canonical texts that
//! the tests write out.

mod common;

use std::path::Path;

use common::{directory, file, finish, hash, project, stderr, stdout, stilt};
use serde_json::Value;

/// The JSON records `stilt show --json ADDRESS` prints for the program at `path`.
fn records(path: &Path, address: &str) -> Vec<Value> {
    let output = stilt(
        &["show", "--json", address, path.to_str().expect("UTF-8")],
        None,
    );
    finish(path);
    stdout(&output)
        .lines()
        .map(|line| serde_json::from_str(line).expect("one JSON record a line"))
        .collect()
}

/// The `at` of the one record `show` gives for `address`.
fn at(path: &Path, address: &str) -> String {
    let found = records(path, address);
    assert_eq!(found.len(), 1, "{address} names one part");
    found[0]["at"].as_str().expect("an `at`").to_owned()
}

/// A program with a part of each kind.
const KINDS: &str = "/// A point.\ntype Point = { x: i64, y: i64 }\n\nconst ORIGIN: Point = Point { x: 0, y: 0 }\n\ntrait Shape {\n  fn area(self) -> i64\n  fn twice(self) -> i64 { self.area() * 2 }\n  fn skipped(self) -> i64 = ?\n}\n\nimpl Point {\n  pub const LIMIT: i64 = 10\n  fn norm(self) -> i64 { self.x * self.x + self.y * self.y }\n}\n\nimpl Shape for Point {\n  fn area(self) -> i64 { 0 }\n}\n\nimpl Shape for i64 {\n  fn area(self) -> i64 { self }\n}\n\ntest \"parses a \\\"line\\\"\" { assert(true) }\n\nfn main() { }\n";

#[test]
fn every_kind_of_part_has_the_path_the_table_gives() {
    // edits.parts, edits.paths and edits.body-addresses.
    let path = file("edits", "kinds", KINDS);
    let output = stilt(
        &["show", "--json", "main", path.to_str().expect("UTF-8")],
        None,
    );
    let module: Value = serde_json::from_slice(&output.stdout).expect("one JSON record");
    let mut declared: Vec<&Value> = module["functions"]
        .as_array()
        .into_iter()
        .chain(module["declarations"].as_array())
        .flatten()
        .collect();
    declared.sort_by_key(|r| r["at"].as_str().map(str::to_owned));
    let paths: Vec<String> = declared
        .iter()
        .map(|r| {
            r["at"]
                .as_str()
                .unwrap()
                .split('#')
                .next()
                .unwrap()
                .to_owned()
        })
        .collect();
    let mut expected = [
        "main.Point",
        "main.ORIGIN",
        "main.Shape",
        "main.Shape.area",
        "main.Shape.twice",
        "main.Shape.skipped",
        "main.Point.LIMIT",
        "main.Point.norm",
        "main.Point.Shape.area",
        "main.i64.Shape.area",
        "main.\"parses a \\\"line\\\"\"",
        "main.main",
    ]
    .map(str::to_owned);
    expected.sort();
    assert_eq!(paths, expected);
    // edits.body-addresses: a body's address is the declaration's path and `/body`, and types,
    // traits and a trait's method without a default body have none.
    for record in declared {
        let at = record["at"].as_str().unwrap();
        let path = at.split('#').next().unwrap();
        let without = ["main.Point", "main.Shape", "main.Shape.area"].contains(&path);
        match record["body"].as_str() {
            Some(body) => assert!(
                !without && body.starts_with(&format!("{path}/body#")),
                "{at}"
            ),
            None => assert!(without, "{at} has a body"),
        }
    }
    finish(&path);
}

#[test]
fn a_record_has_the_canonical_text_that_its_hash_covers() {
    // edits.canonical-text, edits.hash and edits.showing-parts: `text` is the canonical text, `at`
    // its hash, and the body's own.
    let path = file("edits", "text", KINDS);
    let norm = &records(&path, "main.Point.norm")[0];
    let text = "fn norm(self) -> i64 { self.x * self.x + self.y * self.y }";
    assert_eq!(norm["text"], text);
    assert_eq!(norm["at"], format!("main.Point.norm#{}", hash(text)));
    let body = "{ self.x * self.x + self.y * self.y }";
    assert_eq!(norm["body"], format!("main.Point.norm/body#{}", hash(body)));
    let record = &records(&path, "main.Point.norm/body")[0];
    assert_eq!(record["text"], body);
    assert_eq!(record["at"], norm["body"]);
    assert!(record.get("body").is_none());
    let docs = &records(&path, "main.Point")[0];
    let text = "/// A point.\ntype Point = { x: i64, y: i64 }";
    assert_eq!(docs["text"], text);
    assert_eq!(docs["at"], format!("main.Point#{}", hash(text)));
    assert!(docs.get("body").is_none());
    let constant = &records(&path, "main.ORIGIN/body")[0];
    assert_eq!(constant["text"], "Point { x: 0, y: 0 }");
    let hole = &records(&path, "main.Shape.skipped/body")[0];
    assert_eq!(hole["text"], "= ?");
    let case = &records(&path, "main.\"parses a \\\"line\\\"\"")[0];
    assert_eq!(case["kind"], "test");
    finish(&path);
}

#[test]
fn a_member_that_is_too_long_for_its_block_is_laid_out_at_column_0() {
    // edits.canonical-text: the canonical text starts at column 0, so a method that fits in 100
    // columns there is one line, though inside its impl it would not fit.
    let long = "fn long(self) -> i64 { self.x + self.x + self.x + self.x + self.x + self.x + self.x + 10000000000 }";
    assert_eq!(long.len(), 99);
    let source = format!("type P = {{ x: i64 }}\n\nimpl P {{\n  {long}\n}}\n");
    let path = file("edits", "wide", &source);
    assert_eq!(records(&path, "main.P.long")[0]["text"], long);
}

#[test]
fn paths_name_impls_by_the_last_names_of_their_type_and_trait() {
    // edits.paths: `impl Pretty for orders.Order` in the module `pretty` gives
    // `pretty.Order.Pretty.pretty`, and a path is read by what it names.
    let orders = "pub type Order = { qty: i64 }\n";
    let pretty = "use orders\n\npub trait Pretty {\n  fn pretty(self) -> str\n}\n\nimpl Pretty for orders.Order {\n  fn pretty(self) -> str { \"order\" }\n}\n";
    let main = "use pretty\n\nfn main() { }\n";
    let dir = project(
        "edits",
        "foreign",
        &[
            ("orders.lt", orders),
            ("pretty.lt", pretty),
            ("main.lt", main),
        ],
    );
    let found = records(&dir, "pretty.Order.Pretty.pretty");
    assert_eq!(found.len(), 1);
    assert_eq!(found[0]["file"], "pretty.lt");
    let method = "fn pretty(self) -> str { \"order\" }";
    assert_eq!(
        found[0]["at"],
        format!("pretty.Order.Pretty.pretty#{}", hash(method))
    );
    // The module `pretty` declares no `Order`, yet the path names a part of it.
    assert_eq!(records(&dir, "pretty.Order").len(), 0);
    finish(&dir);
}

#[test]
fn a_part_of_a_module_that_an_item_of_its_parent_hides_in_code_is_still_addressed() {
    // edits.paths: `a.b` is a module and `a` also declares a function `b` (program.namespaces and
    // program.child-modules); the module's parts keep their paths.
    let a = "pub fn b() -> i64 { 1 }\n";
    let b = "pub fn f() -> i64 { 2 }\n";
    let main = "use a\n\nfn main() { }\n";
    let dir = directory("edits", "hidden");
    std::fs::create_dir_all(dir.join("a")).expect("a directory");
    for (name, text) in [("a.lt", a), ("a/b.lt", b), ("main.lt", main)] {
        std::fs::write(dir.join(name), text).expect("a file");
    }
    assert_eq!(
        at(&dir, "a.b.f"),
        format!("a.b.f#{}", hash("pub fn f() -> i64 { 2 }"))
    );
    finish(&dir);
}

#[test]
fn a_path_that_names_two_parts_shows_each_of_them() {
    // edits.one-part-per-path: a type and a constant of one name, and a function defined twice.
    let source = "type Origin = { x: i64 }\nconst Origin: Origin = Origin { x: 0 }\n\nfn twice() -> i64 { 1 }\n\nfn twice() -> i64 { 2 }\n";
    let path = file("edits", "twice", source);
    let found = records(&path, "main.Origin");
    assert_eq!(found.len(), 2);
    assert_eq!(found[0]["kind"], "type");
    assert_eq!(found[1]["kind"], "constant");
    let found = records(&path, "main.twice");
    assert_eq!(found.len(), 2);
    assert_ne!(found[0]["at"], found[1]["at"]);
    // An address with the hash of one shows that one.
    let second = found[1]["at"].as_str().unwrap();
    let only = records(&path, second);
    assert_eq!(only.len(), 1);
    assert_eq!(only[0]["text"], "fn twice() -> i64 { 2 }");
    finish(&path);
}

#[test]
fn two_foreign_impls_of_one_name_have_one_path_and_one_hash() {
    // edits.one-part-per-path: the impls of one trait in a module for type constructors of one name
    // from different modules, whose texts are the same.
    let one = "pub type T = { a: i64 }\n";
    let two = "pub type T = { b: i64 }\n";
    let main = "use one\nuse two\n\ntrait Tr {\n  fn m(self) -> i64\n}\n\nimpl Tr for one.T {\n  fn m(self) -> i64 { 1 }\n}\n\nimpl Tr for two.T {\n  fn m(self) -> i64 { 1 }\n}\n\nfn main() { }\n";
    let dir = project(
        "edits",
        "same",
        &[("one.lt", one), ("two.lt", two), ("main.lt", main)],
    );
    let found = records(&dir, "main.T.Tr.m");
    assert_eq!(found.len(), 2);
    assert_eq!(found[0]["at"], found[1]["at"]);
    finish(&dir);
}

/// The hashes of `main.f` and `main.f/body` in a program whose source is `source`.
fn hashes(name: &str, source: &str) -> (String, String) {
    let path = file("edits", name, source);
    let record = &records(&path, "main.f")[0];
    let split = |key: &str| {
        record[key]
            .as_str()
            .unwrap()
            .rsplit('#')
            .next()
            .unwrap()
            .to_owned()
    };
    (split("at"), split("body"))
}

#[test]
fn a_hash_survives_formatting_and_reindenting_and_a_changed_signature() {
    // edits.canonical-text and edits.hash.
    let base = "fn f(x: i64) -> i64 {\n  let y = x + 1\n  y * 2\n}\n";
    let (decl, body) = hashes("base", base);
    let ugly = "fn  f( x:i64 )->i64{ let y=x+1;
 y*2 }
";
    assert_eq!(hashes("ugly", ugly), (decl.clone(), body.clone()));
    let indented = "    fn f(x: i64) -> i64 {\n        let y = x + 1\n        y * 2\n    }\n";
    assert_eq!(hashes("indented", indented), (decl.clone(), body.clone()));
    let impl_block =
        "type T = { a: i64 }\n\nimpl T {\n  fn f(self) -> i64 {\n    let y = 1\n    y\n  }\n}\n";
    let loose = "type T = { a: i64 }\n\nimpl T {\n  fn g(self) -> i64 { 0 }\n}\n\nimpl T {\n  fn f(self) -> i64 {\n    let y = 1\n    y\n  }\n}\n";
    let path = file("edits", "moved", impl_block);
    let moved = file("edits", "moved2", loose);
    let a = records(&path, "main.T.f")[0].clone();
    let b = records(&moved, "main.T.f")[0].clone();
    assert_eq!((&a["at"], &a["body"]), (&b["at"], &b["body"]));
    // A new signature changes the declaration's hash and leaves the body's.
    let changed = "fn f(x: i64, z: i64) -> i64 {\n  let y = x + 1\n  y * 2\n}\n";
    let (new_decl, new_body) = hashes("signature", changed);
    assert_ne!(new_decl, decl);
    assert_eq!(new_body, body);
}

#[test]
fn a_comment_inside_a_part_or_after_its_last_token_changes_its_hash() {
    // edits.parts and edits.hash: a comment in a part's span, or one that follows its last token on
    // the same line, belongs to it. A comment on a line of its own after the part does not.
    let base = "fn f() -> i64 { 1 }\n";
    let (decl, body) = hashes("plain", base);
    let (inside, inside_body) = hashes("inside", "fn f() -> i64 {\n  // why\n  1\n}\n");
    assert_ne!(inside, decl);
    assert_ne!(inside_body, body);
    let (after, after_body) = hashes("after", "fn f() -> i64 { 1 } // why\n");
    assert_ne!(after, decl);
    assert_ne!(after_body, body);
    assert_eq!(
        hashes("below", "fn f() -> i64 { 1 }\n// why\n"),
        (decl.clone(), body.clone())
    );
    assert_eq!(
        hashes("above", "// why\nfn f() -> i64 { 1 }\n"),
        (decl.clone(), body.clone())
    );
    // A doc comment is the declaration's, and not its body's.
    let (docs, docs_body) = hashes("docs", "/// One.\nfn f() -> i64 { 1 }\n");
    assert_ne!(docs, decl);
    assert_eq!(docs_body, body);
}

#[test]
fn an_item_with_a_syntax_error_is_addressed_and_replaced_as_a_whole() {
    // edits.files-with-syntax-errors: the hash covers the source text as written, and there is no
    // `/body`.
    let broken = "fn bad(x: ) -> i64 { 1 }";
    let source = format!("fn good() -> i64 {{ 1 }}\n\n{broken}\n\nfn also() -> i64 {{ 2 }}\n");
    let path = file("edits", "broken", &source);
    let good = records(&path, "main.good");
    assert_eq!(
        good[0]["at"],
        format!("main.good#{}", hash("fn good() -> i64 { 1 }"))
    );
    let bad = &records(&path, "main.bad")[0];
    assert_eq!(bad["at"], format!("main.bad#{}", hash(broken)));
    assert!(bad.get("body").is_none());
    let none = stilt(&["show", "main.bad/body", path.to_str().unwrap()], None);
    assert_eq!(none.status.code(), Some(2));
    let at = bad["at"].as_str().unwrap();
    let fixed = "fn bad(x: i64) -> i64 { x }";
    let output = stilt(
        &["check", "--edit", at, fixed, path.to_str().unwrap()],
        None,
    );
    assert!(output.status.success(), "{}", stderr(&output));
    let after = std::fs::read_to_string(&path).unwrap();
    assert_eq!(
        after,
        format!("fn good() -> i64 {{ 1 }}\n\n{fixed}\n\nfn also() -> i64 {{ 2 }}\n")
    );
}

#[test]
fn show_refuses_an_address_whose_hash_is_not_current() {
    // edits.showing-parts, and edits.refusals for an edit.
    let path = file("edits", "stale-show", "fn f() -> i64 { 1 }\n");
    let current = at(&path, "main.f");
    let output = stilt(&["show", &current, path.to_str().unwrap()], None);
    assert!(output.status.success());
    assert!(stdout(&output).contains("fn f() -> i64 { 1 }"));
    let output = stilt(&["show", "main.f#0000", path.to_str().unwrap()], None);
    assert_eq!(output.status.code(), Some(2));
    assert!(stderr(&output).contains("E0703"));
    // A module's address takes no hash.
    let output = stilt(&["show", "main#0000", path.to_str().unwrap()], None);
    assert_eq!(output.status.code(), Some(2));
}

#[test]
fn a_diagnostic_has_the_address_of_the_smallest_part_that_holds_its_span() {
    // edits.diagnostic-addresses.
    let source = "use nothere\n\n/// Doubles.\n/// ex: dubble(2) == 4\nfn double(x: i64) -> i64 { x * 2 }\n\nfn sig(x: Strng) -> i64 { 1 }\n\nfn body() -> i64 { cuont }\n\ntrait Shape {\n  fn area(self) -> i64\n}\n\ntype Sq = { w: i64 }\n\nimpl Shape for Sq {\n}\n";
    let path = file("edits", "diagnostics", source);
    let output = stilt(&["check", "--json", path.to_str().unwrap()], None);
    let json: Value = serde_json::from_slice(&output.stdout).unwrap();
    let found: Vec<(String, Option<String>)> = json["diagnostics"]
        .as_array()
        .unwrap()
        .iter()
        .map(|d| {
            (
                d["code"].as_str().unwrap().to_owned(),
                d["at"].as_str().map(str::to_owned),
            )
        })
        .collect();
    let docs = "/// Doubles.\n/// ex: dubble(2) == 4\nfn double(x: i64) -> i64 { x * 2 }";
    let sig = "fn sig(x: Strng) -> i64 { 1 }";
    let body = "{ cuont }";
    assert_eq!(
        found,
        [
            // In a `use` declaration: no part.
            ("E0205".to_owned(), None),
            // In a doc example: the declaration.
            (
                "E0211".to_owned(),
                Some(format!("main.double#{}", hash(docs)))
            ),
            // In a signature: the declaration.
            ("E0211".to_owned(), Some(format!("main.sig#{}", hash(sig)))),
            // In a body: the body.
            (
                "E0211".to_owned(),
                Some(format!("main.body/body#{}", hash(body)))
            ),
            // At an impl's header: no part.
            ("E0305".to_owned(), None),
        ]
    );
}
