//! The parts of a file, their canonical texts and hashes, the texts that parts take, writing,
//! and fixes as edits (edits.parts, edits.writing and edits.fixes-as-edits).

use stilt_syntax::parse;

use crate::{Address, Part, Replacement, canonical, check_text, fix_edits, hash, parts, splice};

const SOURCE: &str = "module main\n\nuse a.b\n\n/// Shows.\n/// ex: f(1) == 2\npub fn f(x: i64) -> i64 { x + 1 } // trailing\n\ntype P = { x: i64 }\n\nimpl Show for orders.Point<T> {\n  fn show(self) -> str { \"x\" }\n}\n\nimpl i64 {\n  pub const A: i64 = 1\n}\n\ntrait Tr {\n  fn m(self) -> i64\n  fn d(self) -> i64 = ?\n}\n\ntest \"a\\\"b\" { assert(true) }\n";

fn found(source: &str) -> Vec<Part> {
    parts("main", &parse(source), source)
}

fn source<'a>(text: &'a str, part: &Part) -> &'a str {
    &text[part.extent.clone()]
}

#[test]
fn the_parts_are_the_declarations_and_bodies_with_their_paths() {
    // edits.parts, edits.paths and edits.body-addresses.
    let addresses: Vec<String> = found(SOURCE).iter().map(Part::address).collect();
    assert_eq!(
        addresses,
        [
            "main.f",
            "main.f/body",
            "main.P",
            "main.Point.Show.show",
            "main.Point.Show.show/body",
            "main.i64.A",
            "main.i64.A/body",
            "main.Tr",
            "main.Tr.m",
            "main.Tr.d",
            "main.Tr.d/body",
            "main.\"a\\\"b\"",
            "main.\"a\\\"b\"/body",
        ]
    );
}

#[test]
fn a_declaration_runs_from_its_first_doc_comment_to_its_last_token_and_its_trailing_comment() {
    // edits.extents.
    let parts = found(SOURCE);
    assert_eq!(
        source(SOURCE, &parts[0]),
        "/// Shows.\n/// ex: f(1) == 2\npub fn f(x: i64) -> i64 { x + 1 } // trailing"
    );
    assert_eq!(source(SOURCE, &parts[1]), "{ x + 1 } // trailing");
    assert_eq!(source(SOURCE, &parts[10]), "= ?");
    assert_eq!(source(SOURCE, &parts[6]), "1");
}

#[test]
fn the_canonical_text_is_laid_out_alone_at_column_0() {
    // edits.canonical-text.
    let text = "impl P {\n  fn   f( x :i64)->i64{x+1}\n}\n";
    let parts = found(text);
    assert_eq!(
        canonical(&parts[0], source(text, &parts[0])),
        "fn f(x: i64) -> i64 { x + 1 }"
    );
    assert_eq!(canonical(&parts[1], source(text, &parts[1])), "{ x + 1 }");
    let indented = "\n\n      fn f() -> i64 {\n            1\n      }\n";
    let parts = found(indented);
    assert_eq!(
        canonical(&parts[0], source(indented, &parts[0])),
        "fn f() -> i64 { 1 }"
    );
}

#[test]
fn a_hash_is_four_lowercase_digits_of_the_blake3_digest() {
    // edits.hash: the first two bytes of the digest of the empty string are af13.
    assert_eq!(hash(""), "af13");
    assert_eq!(hash("a"), hash("a"));
    assert_ne!(hash("a"), hash("b"));
}

#[test]
fn a_part_with_a_syntax_error_hashes_its_source_text_as_written() {
    // edits.files-with-syntax-errors.
    let text = "fn good() -> i64 { 1 }\n\nfn bad(x: ) -> i64 { 1 }\n\nfn also() -> i64 { 2 }\n";
    let parts = found(text);
    let addresses: Vec<String> = parts.iter().map(Part::address).collect();
    assert_eq!(
        addresses,
        [
            "main.good",
            "main.good/body",
            "main.bad",
            "main.also",
            "main.also/body"
        ]
    );
    assert!(parts[2].broken);
    assert_eq!(
        canonical(&parts[2], source(text, &parts[2])),
        "fn bad(x: ) -> i64 { 1 }"
    );
}

#[test]
fn addresses_are_read_and_written() {
    let a = Address::parse("main.totals/body#a91f", true).unwrap();
    assert_eq!(
        (a.path.as_str(), a.body, a.hash.as_deref()),
        ("main.totals", true, Some("a91f"))
    );
    assert_eq!(a.to_string(), "main.totals/body#a91f");
    assert!(Address::parse("main.totals/body#a91", true).is_err());
}

fn function() -> Part {
    found("fn f() -> i64 { 1 }\n").remove(0)
}

#[test]
fn a_new_text_is_exactly_one_instance_of_the_part() {
    // edits.new-text.
    let f = function();
    assert!(check_text(&f, "fn g(x: i64) -> i64 { x }").is_ok());
    assert!(check_text(&f, "\n/// Docs.\nfn g() -> i64 { 1 }\n\n").is_ok());
    assert!(check_text(&f, "fn g() -> i64 { 1 } // why").is_ok());
    assert_eq!(check_text(&f, "type T = { a: i64 }"), Err(None));
    assert_eq!(check_text(&f, "fn g() { }\nfn h() { }"), Err(None));
    assert_eq!(check_text(&f, "// above\nfn g() { }"), Err(None));
    assert_eq!(check_text(&f, "use a"), Err(None));
    let error = check_text(&f, "fn g() -> i64 { 1 ) }")
        .unwrap_err()
        .unwrap();
    assert_eq!(
        (error.code.as_str(), error.line, error.col),
        ("E0100", 1, 19)
    );
}

#[test]
fn the_text_of_a_body_is_a_block_a_hole_or_an_expression() {
    let text = "fn f() -> i64 { 1 }\n\nconst C: i64 = 1\n\ntest \"t\" { assert(true) }\n";
    let parts = found(text);
    let (fn_body, const_body, test_body) = (&parts[1], &parts[3], &parts[5]);
    assert!(check_text(fn_body, "{ 2 }").is_ok());
    assert!(check_text(fn_body, "= ?").is_ok());
    assert_eq!(check_text(fn_body, "-> i64 { 2 }"), Err(None));
    assert_eq!(
        check_text(fn_body, "fn g() { }"),
        Err(Some(crate::Syntax {
            code: "E0100".to_owned(),
            message: "unexpected `fn`".to_owned(),
            line: 1,
            col: 1,
        }))
    );
    assert!(check_text(const_body, "1 + 2").is_ok());
    assert!(check_text(test_body, "{ assert(false) }").is_ok());
    assert_eq!(
        check_text(test_body, "1"),
        Err(Some(crate::Syntax {
            code: "E0100".to_owned(),
            message: "expected a block, in braces, found the number `1`".to_owned(),
            line: 1,
            col: 1,
        }))
    );
}

#[test]
fn members_are_read_in_the_grammar_of_their_place() {
    let text = "type T = { a: i64 }\n\nimpl Tr for T {\n  fn m(self) -> i64 { 1 }\n}\n";
    let member = &found(text)[1];
    assert!(check_text(member, "fn m(self) -> i64 { 2 }").is_ok());
    // A member of a trait impl takes no `pub` (program.visibility).
    assert!(check_text(member, "pub fn m(self) -> i64 { 2 }").is_err());
    // A trait impl holds constants (traits.impl-members), but a function's part takes a function
    // (edits.new-text); it holds no type: a syntax error.
    assert_eq!(check_text(member, "const A: i64 = 1"), Err(None));
    assert!(matches!(
        check_text(member, "type A = { a: i64 }"),
        Err(Some(_))
    ));
}

#[test]
fn writing_keeps_every_byte_outside_the_part_and_lays_the_part_out_in_its_place() {
    // edits.writing.
    let text = "type P = {x:i64}\n\n\nimpl P {\n        fn  f(self)->i64{ 0 }  \n}\n";
    let parts = found(text);
    let out = splice(
        "main",
        text,
        &parts,
        &[(1, "fn f(self) -> i64 { let a = 1; a }")],
    );
    assert_eq!(
        out,
        "type P = {x:i64}\n\n\nimpl P {\n        fn f(self) -> i64 {\n          let a = 1\n          a\n        }  \n}\n"
    );
    let out = splice("main", text, &parts, &[(1, "fn f(self) -> i64 { 0 }")]);
    assert_eq!(
        out,
        "type P = {x:i64}\n\n\nimpl P {\n        fn f(self) -> i64 { 0 }  \n}\n"
    );
}

#[test]
fn a_fix_becomes_one_edit_for_each_declaration_it_changes() {
    // edits.fixes-as-edits.
    let text = "fn f(count: i64) -> i64 { cuont }\n\nfn g() -> i64 { 1 }\n";
    let parts = found(text);
    let at = text.find("cuont").unwrap();
    let change = Replacement {
        range: at..at + 5,
        text: "count".to_owned(),
    };
    let edits = fix_edits(text, &parts, |_| false, std::slice::from_ref(&change));
    assert_eq!(edits.len(), 1);
    assert_eq!(edits[0].at, format!("main.f/body#{}", hash("{ cuont }")));
    assert_eq!(edits[0].new, "{ count }");
    // A change outside the body edits the declaration.
    let at = text.find("count").unwrap();
    let rename = Replacement {
        range: at..at + 5,
        text: "n".to_owned(),
    };
    let edits = fix_edits(text, &parts, |_| false, &[rename.clone(), change.clone()]);
    assert_eq!(edits.len(), 1);
    assert!(edits[0].at.starts_with("main.f#"));
    assert_eq!(edits[0].new, "fn f(n: i64) -> i64 { count }");
    // Outside every declaration, or in a declaration with two paths: none.
    let between = Replacement {
        range: 33..34,
        text: String::new(),
    };
    let none = fix_edits(text, &parts, |_| false, &[between]);
    assert_eq!(none.len(), 0);
    let none = fix_edits(text, &parts, |p| p == "main.f", &[change]);
    assert_eq!(none.len(), 0);
}

#[test]
fn a_fix_of_a_trait_and_its_method_is_one_edit_of_the_trait() {
    let text = "trait Tr {\n  fn m(self) -> i64\n}\n";
    let parts = found(text);
    let name = Replacement {
        range: 6..8,
        text: "Ta".to_owned(),
    };
    let method = Replacement {
        range: 27..30,
        text: "u64".to_owned(),
    };
    let edits = fix_edits(text, &parts, |_| false, &[name, method]);
    assert_eq!(edits.len(), 1);
    assert_eq!(edits[0].new, "trait Ta {\n  fn m(self) -> u64\n}");
}

#[test]
fn a_part_with_a_lexical_error_runs_to_the_end_of_its_text() {
    // edits.files-with-syntax-errors: the tokens after a lexical error are the part's too.
    let text = "fn good() -> i64 { 1 }\n\nfn bad() / io {\n  print(\"n is \\(n)\")\n}\n// later\n\nfn also() -> i64 { 2 }\n";
    let all = found(text);
    let bad = all.iter().find(|p| p.path == "main.bad").unwrap();
    assert!(bad.broken);
    assert_eq!(
        source(text, bad),
        "fn bad() / io {\n  print(\"n is \\(n)\")\n}"
    );
    assert!(!all.iter().any(|p| p.path == "main.bad" && p.body));
    let also = all
        .iter()
        .find(|p| p.path == "main.also" && !p.body)
        .unwrap();
    assert_eq!(all[also.decl].path, "main.also");
}
