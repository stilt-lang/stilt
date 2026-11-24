//! The lexical structure of lexical.tokens as regular expressions: the classes of tokens that
//! `reference/03-syntax.md` names, the whitespace and comments between tokens, and the newlines that
//! the grammar reads as separators.

/// A regular expression over characters.
#[derive(Clone, Debug)]
pub(crate) enum Rx {
    Lit(String),
    /// A set of characters, or all but those of the set when negated.
    Set(bool, Vec<(char, char)>),
    Seq(Vec<Rx>),
    Alt(Vec<Rx>),
    Star(Box<Rx>),
    Plus(Box<Rx>),
    Opt(Box<Rx>),
}

pub(crate) fn lit(text: &str) -> Rx {
    Rx::Lit(text.to_owned())
}

/// The characters listed in `spec`, where `a-z` is a range.
pub(crate) fn set(spec: &str) -> Rx {
    Rx::Set(false, ranges(spec))
}

/// Every character but those listed in `spec`.
pub(crate) fn none_of(spec: &str) -> Rx {
    Rx::Set(true, ranges(spec))
}

fn ranges(spec: &str) -> Vec<(char, char)> {
    let chars: Vec<char> = spec.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        if chars.get(i + 1) == Some(&'-') && i + 2 < chars.len() {
            out.push((chars[i], chars[i + 2]));
            i += 3;
        } else {
            out.push((chars[i], chars[i]));
            i += 1;
        }
    }
    out
}

fn seq(items: Vec<Rx>) -> Rx {
    Rx::Seq(items)
}

fn alt(items: Vec<Rx>) -> Rx {
    Rx::Alt(items)
}

fn star(item: Rx) -> Rx {
    Rx::Star(Box::new(item))
}

fn plus(item: Rx) -> Rx {
    Rx::Plus(Box::new(item))
}

fn opt(item: Rx) -> Rx {
    Rx::Opt(Box::new(item))
}

/// The names `reference/03-syntax.md` gives to classes of tokens, with the lexemes of the classes
/// that lexical.tokens defines. `SEP`, `TOKEN` and `DOC` are not lexemes: the grammar reads a
/// separator as a semicolon or a newline (lexical.separators), a `TOKEN` as one of the tokens it
/// stands for, and a doc comment as a comment.
pub(crate) const CLASSES: [&str; 9] = [
    "lower",
    "Upper",
    "INT",
    "FLOAT",
    "STRING",
    "STRING_HEAD",
    "STRING_MID",
    "STRING_TAIL",
    "FORMAT",
];

pub(crate) fn is_class(name: &str) -> bool {
    CLASSES.contains(&name) || name == "SEP" || name == "TOKEN"
}

/// The lexeme of the class, named in lowercase.
pub(crate) fn lexemes() -> Vec<(String, Rx)> {
    let digit = || set("0-9");
    let hex = || set("0-9a-fA-F");
    // Digits with a `_` only between two of them (lexical.integer-literals).
    let run = |d: fn() -> Rx| seq(vec![d(), star(alt(vec![d(), seq(vec![lit("_"), d()])]))]);
    // No leading zero (lexical.integer-literals and lexical.float-literals).
    let decimal = alt(vec![
        lit("0"),
        seq(vec![
            set("1-9"),
            star(alt(vec![digit(), seq(vec![lit("_"), digit()])])),
        ]),
    ]);
    let exponent = seq(vec![set("eE"), opt(set("+-")), plus(digit())]);
    let int = alt(vec![
        decimal.clone(),
        seq(vec![lit("0x"), run(hex)]),
        seq(vec![lit("0o"), run(|| set("0-7"))]),
        seq(vec![lit("0b"), run(|| set("01"))]),
    ]);
    // `DeE` (lexical.float-literals); the forms with a fraction are made of tokens (see
    // `shape::publish`).
    let float_exponent = seq(vec![decimal, exponent.clone()]);
    let fraction = seq(vec![run(digit), opt(exponent)]);
    // lexical.escapes: the escapes, and no raw newline.
    let unicode = seq(vec![lit("\\u{"), hex_digits(), lit("}")]);
    let escape = alt(vec![seq(vec![lit("\\"), set("ntr0\\\"{")]), unicode]);
    let text = || star(alt(vec![none_of("\"\\{\n"), escape.clone()]));
    let part = |open: &str, close: &str| seq(vec![lit(open), text(), lit(close)]);
    // lexical.format-specs: `[[fill]align][width][.precision][kind]`, with the numbers unbounded.
    let format = seq(vec![
        lit(":"),
        opt(seq(vec![opt(none_of("{}\n")), set("<^>")])),
        star(digit()),
        opt(seq(vec![lit("."), plus(digit())])),
        opt(set("xXobe")),
    ]);
    // lexical.identifiers and lexical.case: the case of the first letter, after any underscores and
    // digits.
    let name = |first: &str| {
        seq(vec![
            opt(seq(vec![lit("_"), star(set("0-9_"))])),
            set(first),
            star(set("A-Za-z0-9_")),
        ])
    };
    vec![
        ("lower".into(), name("a-z")),
        ("upper".into(), name("A-Z")),
        ("int".into(), int),
        ("float_exponent".into(), float_exponent),
        ("fraction".into(), fraction),
        ("string".into(), part("\"", "\"")),
        ("string_head".into(), part("\"", "{")),
        ("string_mid".into(), part("}", "{")),
        ("string_tail".into(), part("}", "\"")),
        ("format".into(), format),
    ]
}

/// One to six hexadecimal digits.
fn hex_digits() -> Rx {
    let hex = || set("0-9a-fA-F");
    let mut rest = opt(hex());
    for _ in 0..4 {
        rest = opt(seq(vec![hex(), rest]));
    }
    seq(vec![hex(), rest])
}

/// Spaces, tabs and the comments that run to the end of the line (lexical.whitespace and
/// lexical.line-comments). A doc comment is a comment here.
pub(crate) fn blank() -> Rx {
    alt(vec![plus(set(" \t")), comment()])
}

pub(crate) fn comment() -> Rx {
    seq(vec![lit("//"), star(none_of("\n"))])
}

/// The blanks before the first token, which one lexeme of the Lark form matches.
pub(crate) fn leading_blanks() -> Rx {
    plus(alt(vec![set(" \t"), comment()]))
}

/// A newline, which may be written `\r\n` (lexical.source-text).
pub(crate) fn newline() -> Rx {
    seq(vec![opt(lit("\r")), lit("\n")])
}
