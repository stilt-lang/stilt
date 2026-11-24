//! Tests of parsing whole texts: trees, first errors and warnings. Expected trees and positions
//! follow from `reference/03-syntax.md` and the Reference's lexical chapter.

use super::*;

/// The tree form of a text without syntax errors.
fn sexp(text: &str) -> String {
    let parse = parse(text);
    assert_eq!(parse.error(), None, "{text}");
    assert_eq!(
        parse.syntax().text().to_string(),
        text,
        "the tree holds all the text"
    );
    sexp::module(&parse.tree())
}

/// The tree form of the body of `fn f() { BODY }`, the expression or statements in it.
fn body(body: &str) -> String {
    let tree = sexp(&format!("fn f() {{ {body} }}"));
    let block = tree
        .strip_prefix("(module (fn f () () (tuple) (row) (block ")
        .and_then(|rest| rest.strip_suffix(")))"))
        .unwrap_or_else(|| panic!("an unexpected tree: {tree}"));
    block.to_owned()
}

/// The code, line and column of the first syntax error of a text.
fn error(text: &str) -> (&'static str, u32, u32) {
    let parse = parse(text);
    assert_eq!(
        parse.syntax().text().to_string(),
        text,
        "the tree holds all the text"
    );
    let e = parse.error().expect("the text has a syntax error");
    placed(text, e)
}

fn warnings(text: &str) -> Vec<(&'static str, u32, u32)> {
    parse(text)
        .warnings()
        .iter()
        .map(|w| placed(text, w))
        .collect()
}

/// The code, line and column of a diagnostic of `text`.
fn placed(text: &str, d: &Diagnostic) -> (&'static str, u32, u32) {
    let at = LineIndex::new(text).position(text, d.range.start());
    (d.code.as_str(), at.line, at.col)
}

#[test]
fn a_function() {
    assert_eq!(
        sexp("fn main() / io {\n  print(\"hi\")\n}\n"),
        r#"(module (fn main () () (tuple) (row io) (block (call print "hi"))))"#
    );
}

#[test]
fn a_lexical_error_after_a_grammar_error() {
    assert_eq!(error("fn f( {\n\"abc"), ("E0100", 1, 7));
    assert_eq!(error("fn f() {}\n\"abc"), ("E0005", 2, 1));
}

#[test]
fn one_shift_token_closes_two_lists() {
    assert_eq!(
        sexp("fn f(m: Map<str, List<i64>>) {}"),
        "(module (fn f () ((m (Map str (List i64)))) (tuple) (row) (block)))"
    );
    assert_eq!(
        sexp("fn f(g: List<fn() / raise<E>>) {}"),
        "(module (fn f () ((g (List (fn () (tuple) (row (raise E)))))) (tuple) (row) (block)))"
    );
    // The second `>` has nothing to close, and the error is at the `>>`.
    assert_eq!(error("fn f(m: List<i64>>) {}"), ("E0100", 1, 17));
}

#[test]
fn rows_go_to_the_innermost_function_type() {
    assert_eq!(
        sexp("fn f() -> fn() / io / e {}"),
        "(module (fn f () () (fn () (tuple) (row io)) (row e) (block)))"
    );
}

#[test]
fn escaping_starts_a_parameter_whose_type_is_written_with_fn() {
    // lexical.contextual-keywords, and declarations.parameters.
    assert_eq!(
        sexp("fn f(x: fn(escaping), escaping g: fn() / io) { let escaping = 1 }"),
        "(module (fn f () ((x (fn (escaping) (tuple) (row))) (escaping g (fn () (tuple) (row io)))) \
         (tuple) (row) (block (let escaping 1))))"
    );
    assert_eq!(error("fn f(escaping g: i64) {}"), ("E0100", 1, 18));
    assert_eq!(error("fn f(escaping g: (fn())) {}"), ("E0100", 1, 18));
    assert_eq!(error("fn f(inout escaping g: fn()) {}"), ("E0100", 1, 21));
    assert_eq!(error("fn f(escaping inout g: fn()) {}"), ("E0100", 1, 15));
    assert_eq!(error("fn f(escaping: i64) {}"), ("E0100", 1, 14));
}

#[test]
fn comparisons_dont_chain() {
    assert_eq!(error("fn f() { a < b < c }"), ("E0100", 1, 16));
    assert_eq!(body("a < b && b < c"), "(&& (< a b) (< b c))");
}

#[test]
fn precedence() {
    assert_eq!(body("-a * b + c"), "(+ (* (neg a) b) c)");
    assert_eq!(body("x & 1 == 0"), "(== (& x 1) 0)");
    assert_eq!(body("a else b else c"), "(else a (else b c))");
    assert_eq!(body("return + 1"), "(+ (return) 1)");
    assert_eq!(body("return - 1"), "(return (neg 1))");
    assert_eq!(body("raise e else f"), "(raise (else e f))");
}

#[test]
fn a_catch_belongs_to_the_innermost_open_try() {
    assert_eq!(
        body("try a(try b()) catch _ => 0"),
        "(try (call a (try (call b))) (catch (arm _ 0)))"
    );
    assert_eq!(
        body("try try a catch e => b"),
        "(try (try a (catch (arm e b))))"
    );
}

#[test]
fn heads_leave_out_struct_literals_and_blocks() {
    assert_eq!(body("if P {}"), "(if P (block))");
    assert_eq!(body("P {}"), "(struct P)");
    assert_eq!(body("if return {}"), "(if (return) (block))");
    assert_eq!(
        body("if f(P { x }) {}"),
        "(if (call f (struct P (x x))) (block))"
    );
}

#[test]
fn paths_are_names_followed_by_fields() {
    assert_eq!(body("fs.read(p)"), "(call (field fs read) p)");
    assert_eq!(body("t.0.1"), "(field (field t 0) 1)");
    assert_eq!(body(".name.len()"), "(call (field (field . name) len))");
    assert_eq!(body("orders.Order { id }"), "(struct orders.Order (id id))");
}

#[test]
fn a_use_path_takes_names_of_either_case_after_its_first() {
    // Name resolution tells a module from an item (program.what-use-binds).
    assert_eq!(
        sexp("use std.sync.Shared.new"),
        "(module (use std.sync.Shared.new))"
    );
    assert_eq!(error("use Std.io"), ("E0100", 1, 5));
}

#[test]
fn separators() {
    assert_eq!(body("a\n  .b"), "(field a b)");
    assert_eq!(body("x = 1;; y = 2"), "(= x 1) (= y 2)");
    // A separator sits on the line of the token before it.
    assert_eq!(error("fn f() {\n  let x =\n}"), ("E0100", 3, 1));
    assert_eq!(error("type Id = UserId\nfn f() {}"), ("E0100", 1, 11));
}

#[test]
fn doc_comments() {
    assert_eq!(
        sexp("/// Adds.\n/// ex: add(1, 2) == 3\npub fn add(a: i64, b: i64) -> i64 { a + b }"),
        "(module (doc \"Adds.\" (ex (== (call add 1 2) 3)) (pub (fn add () ((a i64) (b i64)) i64 \
         (row) (block (+ a b))))))"
    );
    // A doc comment before something other than a declaration is the error.
    assert_eq!(error("/// doc\nuse a"), ("E0100", 1, 1));
    assert_eq!(error("fn f() {} /// doc\nfn g() {}"), ("E0100", 1, 11));
    assert_eq!(error("/// doc\n\nfn g() {}"), ("E0100", 1, 1));
    // An example's error is in the file's coordinates.
    assert_eq!(error("/// ex: 1 +\nfn g() {}"), ("E0100", 1, 12));
    // A lexical error in an example, the format spec of an interpolation.
    assert_eq!(
        error("/// ex: f(\"{x: 1}\") == 1\nfn g() {}"),
        ("E0007", 1, 14)
    );
    assert_eq!(
        error("/// prop: f(\"{x: 1}\")\nfn g() {}"),
        ("E0007", 1, 16)
    );
}

/// tests.prop-lines: a property is parsed as an example is, and its tree is `(prop EXPR)`.
#[test]
fn properties() {
    assert_eq!(
        sexp(
            "/// prop: |xs: List<i64>| reverse(reverse(xs)) == xs //~ PASS\n\
             fn reverse(xs: List<i64>) -> List<i64> { xs }"
        ),
        "(module (doc (prop (closure ((: xs (List i64))) (== (call reverse (call reverse xs)) \
         xs))) (fn reverse () ((xs (List i64))) (List i64) (row) (block xs))))"
    );
    assert_eq!(
        sexp("///   prop:|x: i64| x == x\nfn f() {}"),
        "(module (doc (prop (closure ((: x i64)) (== x x))) (fn f () () (tuple) (row) (block))))"
    );
    assert_eq!(error("/// prop: |x: i64| x +\nfn f() {}"), ("E0100", 1, 23));
    assert_eq!(
        sexp("/// props: are text\nfn f() {}"),
        "(module (doc \"props: are text\" (fn f () () (tuple) (row) (block))))"
    );
}

#[test]
fn contextual_keywords() {
    assert_eq!(
        sexp("module a.b\nwithout alloc,\n  panic\nfn f() / {io, raise<E>, io} {}"),
        "(module (header a.b (without alloc panic)) (fn f () () (tuple) \
         (row io (raise E) io) (block)))"
    );
    assert_eq!(body("let io = without"), "(let io without)");
    assert_eq!(
        body("try f() catch _ because \"why\" => 0"),
        "(try (call f) (catch (arm _ (because \"why\") 0)))"
    );
}

#[test]
fn limits() {
    // A second `without` in a header and a repeated limit parse; resolution rejects them.
    assert_eq!(
        sexp("module m; without panic; without alloc"),
        "(module (header m (without panic) (without alloc)))"
    );
    assert_eq!(
        sexp("fn f(without: i64) -> i64 / e without panic, panic { without }"),
        "(module (fn f () ((without i64)) i64 (row e) (without panic panic) (block without)))"
    );
    assert_eq!(
        sexp("trait T { fn a(self); fn b(self) without alloc = ? }"),
        "(module (trait T (fn a () (self) (tuple) (row)) (fn b () (self) (tuple) (row) \
         (without alloc) ?)))"
    );
    // A name that isn't a limit, a tier among them (program.header-limits and program.tiers), a
    // missing limit, and a trait method with limits but no body.
    assert_eq!(error("module m\nwithout core"), ("E0100", 2, 9));
    assert_eq!(error("module m\nwithout panic, advanced"), ("E0100", 2, 16));
    assert_eq!(error("fn f() without systems {}"), ("E0100", 1, 16));
    assert_eq!(error("fn f() without panic, {}"), ("E0100", 1, 23));
    assert_eq!(
        error("trait T { fn a(self) without panic }"),
        ("E0100", 1, 36)
    );
    // A clause may start the line after a signature or a header's path
    // (lexical.terminator-insertion), and follow a header's path on its line.
    assert_eq!(
        sexp("fn f() -> i64\n  without panic {}"),
        "(module (fn f () () i64 (row) (without panic) (block)))"
    );
    assert_eq!(
        sexp("module m without panic\nwithout alloc"),
        "(module (header m (without panic) (without alloc)))"
    );
    // `without` that no limit follows on its line starts no clause.
    assert_eq!(
        error("fn f() -> i64\n  without\n  panic {}"),
        ("E0100", 1, 11)
    );
    // The capabilities are limits after `without`, and names elsewhere (facts.without).
    assert_eq!(
        sexp("fn f() without fs, net, clock, env, console, rand, spawn { fs.read(env) }"),
        "(module (fn f () () (tuple) (row) (without fs net clock env console rand spawn) \
         (block (call (field fs read) env))))"
    );
}

#[test]
fn patterns() {
    assert_eq!(
        body("match x { A(b, -1) | B { c, d: _, .. } => 0, [h, ..t] => 1, (y,) => 2 }"),
        "(match x (arm (or (A b -1) (record B (c c) (d _) ..)) 0) (arm (list h (.. t)) 1) \
         (arm (tuple y) 2))"
    );
}

#[test]
fn interpolation() {
    assert_eq!(
        body(r#""a{x:>4}b{y}""#),
        r#"(interp "a" (splice x ">4") "b" (splice y))"#
    );
}

#[test]
fn commented_out_code() {
    assert_eq!(warnings("// f(x)\n"), [("W0001", 1, 1)]);
    assert_eq!(warnings("// i.e. done\n"), [("W0001", 1, 1)]);
    assert_eq!(warnings("// x;\n"), [("W0001", 1, 1)]);
    for exempt in [
        "// fallthrough",
        "// 42",
        "// -1",
        "// (-1)",
        "// -(1)",
        "// (unused)",
        "// \"done {x}\"",
        "// ?",
        "// ;",
        "//~ ERROR E0100",
        "/// f(x)",
    ] {
        assert_eq!(warnings(exempt), [], "{exempt}");
    }
}

#[test]
fn recovery_keeps_all_the_text() {
    for text in [
        "fn f( {",
        "fn f() { let = }\nfn g() {}",
        "}}} fn",
        "type A = | B( | C",
        "fn f() { match x { A => , } }",
        "\"unterminated\nfn f() { 1 @ 2 }",
        "fn f() -> List<i64>> {}",
        "impl<T: Ord>> X {}",
    ] {
        let parse = parse(text);
        assert_eq!(parse.syntax().text().to_string(), text);
        assert!(parse.error().is_some(), "{text}");
    }
}

/// The items that a text with a syntax error declares, read a part at a time (errors.parts):
/// each as its kind and name, with `!` after one that holds an error.
fn parts(text: &str) -> Vec<String> {
    let parse = parse(text);
    assert!(parse.error().is_some(), "{text}");
    assert_eq!(parse.syntax().text().to_string(), text);
    parse
        .syntax()
        .children()
        .filter(|n| n.kind() != ERROR)
        .map(|n| {
            let name = n
                .children()
                .find(|c| c.kind() == NAME)
                .map(|c| c.text().to_string())
                .unwrap_or_default();
            let broken = if n.children().any(|c| c.kind() == ERROR) {
                "!"
            } else {
                ""
            };
            format!("{:?} {name}{broken}", n.kind())
        })
        .collect()
}

#[test]
fn a_file_with_a_syntax_error_is_read_an_item_at_a_time() {
    assert_eq!(
        parts("fn f() { 1 + }\nfn g() {}\ntype T = { x: }\nconst C: i64 = 1"),
        ["FN f!", "FN g", "TYPE_DECL T!", "CONST C"]
    );
    // An error before the body's `{` keeps only the name.
    assert_eq!(parts("fn f(x: i64) -> { x }\nfn g() {}"), ["FN f!", "FN g"]);
    // Reading resumes at the next declaration that starts a line, inside a bracket left open.
    assert_eq!(parts("fn f(x: i64 {}\nfn g() {}"), ["FN f!", "FN g"]);
    // An impl whose error is inside its block keeps its other members.
    assert_eq!(
        parts("impl T {\n  fn a() {}\n  fn b() { , }\n}\nfn c() {}"),
        ["IMPL ", "FN c"]
    );
    assert_eq!(parts("impl for {\n}\nfn c() {}"), ["FN c"]);
    // A lexical error ends the tokens.
    assert_eq!(parts("fn f() {}\nfn g() { \"open\n}"), ["FN f", "FN g!"]);
}

#[test]
fn encoding() {
    assert_eq!(
        decode(b"fn \xFF").map_err(|e| (e.code.as_str(), e.range)),
        Err(("E0001", TextRange::empty(3.into())))
    );
    assert_eq!(
        decode(b"\r \xFF").map_err(|e| (e.code.as_str(), e.range)),
        Err(("E0001", TextRange::new(0.into(), 1.into())))
    );
    assert_eq!(error("\u{FEFF}fn f() {}"), ("E0001", 1, 1));
}

mod macros;
