//! The cases of the format that the pairs of `tests/format/` leave out: files without code, line
//! endings, interpolations, and spacing that keeps tokens apart.

use crate::{Error, format};

fn formatted(source: &str) -> String {
    format(source.as_bytes()).unwrap_or_else(|error| panic!("{source:?}: {error:?}"))
}

#[test]
fn a_file_without_code_keeps_only_its_comments() {
    assert_eq!(formatted(""), "");
    assert_eq!(formatted("  \n\n\t\n"), "");
    assert_eq!(
        formatted("\n\n// one\n\n\n// two\n\n"),
        "// one\n\n// two\n"
    );
    assert_eq!(formatted("// no newline"), "// no newline\n");
}

#[test]
fn line_endings_become_newlines_and_tabs_become_spaces() {
    assert_eq!(
        formatted("fn main() {\r\n\tlet x = 1\r\n\tlet y = x\r\n}\r\n"),
        "fn main() {\n  let x = 1\n  let y = x\n}\n"
    );
}

#[test]
fn interpolations_stay_on_their_line() {
    assert_eq!(
        formatted("type P = { x: i64 }\nfn f(x: i64) -> str { \"{P { x: x }} {x+1}\" }\n"),
        "type P = { x: i64 }\nfn f(x: i64) -> str { \"{P { x }} {x + 1}\" }\n"
    );
    // A block in an interpolation needs its `;`, so the interpolation is written as it is.
    let kept = "fn f() -> str { \"{ { let y = 1; y } }\" }\n";
    assert_eq!(formatted(kept), kept);
}

#[test]
fn spaces_keep_tokens_apart() {
    // `(1).0` would read as a float without its space, and `| |` closes no parameters.
    assert_eq!(
        formatted("fn f() -> i64 { 1 .0 + t.0.1 + (1,).0 }\n"),
        "fn f() -> i64 { 1 .0 + t.0.1 + (1,).0 }\n"
    );
    assert_eq!(
        formatted("fn f() -> List<List<i64>> { let g = | | 1; [[-1]] }\n"),
        "fn f() -> List<List<i64>> {\n  let g = || 1\n  [[-1]]\n}\n"
    );
}

#[test]
fn a_rest_pattern_keeps_its_space_when_a_trailing_comma_goes() {
    let once = formatted("type P = { a: i64 }\nfn f(p: P) { let P { a: b, .., } = p }\n");
    assert_eq!(
        once,
        "type P = { a: i64 }\nfn f(p: P) { let P { a: b, .. } = p }\n"
    );
    assert_eq!(formatted(&once), once);
}

#[test]
fn a_macro_keeps_its_tokens_and_its_separators() {
    // `- >` would read as `->`, and a line break before `.` or after `*` separates nothing
    // (lexical.terminator-insertion), so a `;` does.
    let source = "syntax odd { (- > $x: expr) => { $x; .foo() }; [] => $(a)*; () => 1 }\n";
    assert_eq!(
        formatted(source),
        "syntax odd {\n  (- > $x: expr) => {\n    $x;\n    .foo()\n  }\n  [] => $(a)*;\n  () => 1\n}\n"
    );
    // A closure's bars and type arguments in a template.
    let closure = "syntax add {\n  ($x: expr) => {\n    let v: List<List<i64>> = $x.map(|a| a + 1)\n    v\n  }\n}\n";
    assert_eq!(formatted(closure), closure);
}

#[test]
fn a_file_with_a_syntax_error_is_not_formatted() {
    assert!(matches!(format(b"fn main( {}\n"), Err(Error::Syntax(_))));
    assert!(matches!(format(b"fn f() {}\n\xff"), Err(Error::Syntax(_))));
}
