//! Tests of the trees of macros' declarations and uses, and of their syntax errors, which
//! follow from syntax.macros and macros.syntax-declarations.

use super::{body, error, sexp};

#[test]
fn a_declaration() {
    assert_eq!(
        sexp("syntax unless {\n  ($cond: expr) $body: block => if !($cond) $body\n}\n"),
        "(module (syntax unless (arm (paren (frag cond expr)) (frag body block) \
         (template if ! (paren (frag cond)) (frag body)))))"
    );
}

#[test]
fn repetitions_and_groups() {
    assert_eq!(
        sexp(
            "pub syntax p {\n  [$($k: expr => $v: expr),*] => [$(($k, $v)),*]\n  \
             ($($x: name)*) => { $(print($x));* }\n}"
        ),
        "(module (pub (syntax p (arm (bracket (rep , * (frag k expr) => (frag v expr))) \
         (template (bracket (rep , * (paren (frag k) , (frag v)))))) \
         (arm (paren (rep _ * (frag x name))) \
         (template (brace (rep ; * print (paren (frag x)))))))))"
    );
}

#[test]
fn literals_are_strings_of_their_text() {
    assert_eq!(
        sexp("syntax c {\n  () => \"one {$x}\"\n  ($x: Name) => 1_0 + x\n}"),
        "(module (syntax c (arm (paren) (template \"one \" (frag x) \"\")) \
         (arm (paren (frag x Name)) (template \"10\" + x))))"
    );
}

#[test]
fn uses() {
    assert_eq!(
        body("unless!(a > b) { print(\"no\"); x }"),
        "(macro unless (paren a > b) (brace print (paren \"no\") ; x))"
    );
    assert_eq!(
        body("m.swap![1, (2)]"),
        "(macro m.swap (bracket \"1\" , (paren \"2\")))"
    );
    assert_eq!(
        body("match p { pair!(1, s) => 0 }"),
        "(match p (arm (macro pair (paren \"1\" , s)) 0))"
    );
    assert_eq!(
        body("m!(x).len()"),
        "(call (field (macro m (paren x)) len))"
    );
}

#[test]
fn a_head_leaves_out_the_trailing_block() {
    assert_eq!(body("if m!(x) { 1 }"), "(if (macro m (paren x)) (block 1))");
}

#[test]
fn errors() {
    // `$` outside a declaration (macros.templates).
    assert_eq!(error("fn f() {\n  let x = $y\n}"), ("E0100", 2, 11));
    assert_eq!(error("fn f() {\n  m!($y)\n}"), ("E0100", 2, 6));
    // A use needs a group.
    assert_eq!(error("fn f() {\n  m!x\n}"), ("E0100", 2, 5));
    // A fragment needs a kind, and a repetition an operator.
    assert_eq!(error("syntax a { ($x) => 0 }"), ("E0100", 1, 15));
    assert_eq!(error("syntax a { ($($x: expr),) => 0 }"), ("E0100", 1, 25));
    // An arm needs a template.
    assert_eq!(error("syntax a { () => }"), ("E0100", 1, 18));
}

mod forms {
    use crate::SyntaxKind::{self, *};
    use crate::forms::{Form, Piece, parse_form};

    fn pieces<'a>(tokens: &[(SyntaxKind, &'a str)]) -> Vec<Piece<'a>> {
        tokens
            .iter()
            .map(|&(kind, text)| Piece { kind, text })
            .collect()
    }

    #[test]
    fn a_form_takes_the_longest_prefix_it_can() {
        let p = pieces(&[
            (INT, "1"),
            (PLUS, "+"),
            (INT, "2"),
            (FAT_ARROW, "=>"),
            (INT, "3"),
        ]);
        let parsed = parse_form(&p, Form::Expr);
        assert_eq!((parsed.taken, parsed.error), (3, None));
        let text = parsed.node().map(|n| n.text().to_string());
        assert_eq!(text.as_deref(), Some("1 + 2"));
    }

    #[test]
    fn a_form_with_an_error_names_its_token() {
        let p = pieces(&[(INT, "1"), (PLUS, "+"), (COMMA, ",")]);
        assert_eq!(parse_form(&p, Form::Expr).error, Some(2));
        let p = pieces(&[
            (L_CURLY, "{"),
            (LOWER_IDENT, "a"),
            (SEP, ";"),
            (LOWER_IDENT, "b"),
        ]);
        assert_eq!(parse_form(&p, Form::Block).error, Some(4));
        let p = pieces(&[
            (L_PAREN, "("),
            (INT, "1"),
            (COMMA, ","),
            (UNDERSCORE, "_"),
            (R_PAREN, ")"),
        ]);
        assert!(parse_form(&p, Form::Pattern).is_whole(5));
        assert!(!parse_form(&p, Form::Expr).is_whole(5));
    }
}
