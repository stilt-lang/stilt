//! The foreign syntax that marks of other languages make: `::` in paths, before a variant and
//! before type arguments, `?` after a type, `??` and `?.`, and `!` after an optional value
//! (reference/messages.md).

use rowan::TextRange;
use stilt_diag::{Code, Edit, codes};

use crate::SyntaxKind::*;
use crate::foreign::{Cx, Foreign};

/// `a::b`, a path of Rust's, C++'s or PHP's. Each `::` of the part becomes what Stilt writes:
/// `.` in a path, nothing between a type and its variant, which Stilt names alone, and nothing
/// before type arguments, which an annotation gives instead.
pub(crate) fn paths(cx: &Cx<'_>) -> Foreign {
    let mut edits = Vec::new();
    let mut skip_to = 0;
    for i in doubled_colons(cx) {
        if i < skip_to {
            continue;
        }
        match form(cx, i) {
            Form::TypeArguments(end) => {
                edits.push(Edit::delete(cx.through(i, end)));
                skip_to = end + 1;
            }
            Form::Variant => edits.push(Edit::delete(cx.through(i - 1, i + 1))),
            Form::Path => edits.push(Edit::replace(cx.through(i, i + 1), ".")),
        }
    }
    let (message, help, title) = match form(cx, cx.at) {
        Form::TypeArguments(_) => (
            "Stilt gives no type arguments in an expression: an annotation gives them",
            "Type arguments are inferred, or given by an annotation, as \
             `let xs: List<i64> = …`.",
            "delete the type arguments",
        ),
        Form::Variant => (
            "Stilt names a variant alone, as `Circle(r)`, not through its type",
            "A variant's name is visible wherever its type is, in patterns and in \
             expressions alike.",
            "name the variant alone",
        ),
        Form::Path => (
            "Stilt writes a path with `.`, as `List.new()`",
            "A module's items, a type's functions and a trait's members are all named with `.`.",
            "write `.`",
        ),
    };
    Foreign::new(message, help).fix(title, edits)
}

/// What a `::` whose first `:` is token `i` writes.
enum Form {
    /// Type arguments, `::<…>`, whose `>` is the token given.
    TypeArguments(usize),
    /// A variant through its type, as `Shape::Circle`.
    Variant,
    Path,
}

fn form(cx: &Cx<'_>, i: usize) -> Form {
    if cx.kind(i + 2) == L_ANGLE
        && let Some(end) = closing_angle(cx, i + 2)
    {
        return Form::TypeArguments(end);
    }
    let upper = |j: Option<usize>| j.is_some_and(|j| cx.kind(j) == UPPER_IDENT);
    if upper(i.checked_sub(1)) && upper(Some(i + 2)) && cx.kind(i + 3) != DOT {
        return Form::Variant;
    }
    Form::Path
}

/// The first `:` of each `::` of the part.
fn doubled_colons(cx: &Cx<'_>) -> Vec<usize> {
    (0..cx.tokens.len().saturating_sub(1))
        .filter(|&i| cx.kind(i) == COLON && cx.kind(i + 1) == COLON && cx.touching(i))
        .filter(|&i| i == 0 || !(cx.kind(i - 1) == COLON && cx.touching(i - 1)))
        .collect()
}

/// The `>` that closes the `<` at token `open`, counting a `>>` as two.
fn closing_angle(cx: &Cx<'_>, open: usize) -> Option<usize> {
    let mut depth = 0usize;
    for i in open..cx.tokens.len() {
        match cx.kind(i) {
            L_ANGLE => depth += 1,
            R_ANGLE => depth -= 1,
            SHR if depth >= 2 => depth -= 2,
            L_CURLY | R_CURLY | SEP | EOF => return None,
            _ => {}
        }
        if depth == 0 {
            return Some(i);
        }
    }
    None
}

/// `T?`, Swift's and Kotlin's optional type, `a ?? b`, a fallback for a missing value, and
/// `a?.b`, a field read through an optional value.
pub(crate) fn optional(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    if let Some(form) = mark(cx, at) {
        let (message, help, title) = if form == QUESTION {
            (
                "Stilt gives a missing value's fallback with `else`, as `x else 0`",
                "`else` after an `Option` gives the value inside it, or the fallback when it is \
                 `None`.",
                "write `else`",
            )
        } else {
            (
                "Stilt reads a field through an `Option` with `.`, without `?`",
                "A field read through an `Option` is an `Option` of the field, `None` when the \
                 value is missing.",
                "write `.` and `else`",
            )
        };
        let edits = (cx.statement_start(at)..cx.statement_end(at))
            .filter_map(|i| match mark(cx, i)? {
                QUESTION => Some(Edit::replace(cx.through(i, i + 1), "else")),
                _ => Some(Edit::delete(cx.range(i))),
            })
            .collect();
        return Some(Foreign::new(message, help).fix(title, edits));
    }
    let start = type_start(cx, at)?;
    let found = Foreign::new(
        "Stilt writes a type whose value may be missing as `Option<T>`",
        "A value that may be missing has the type `Option<T>`: `None`, or `Some(x)`.",
    );
    let edits = vec![
        Edit::insert(cx.range(start).start(), "Option<"),
        Edit::replace(cx.range(at), ">"),
    ];
    Some(found.fix("write `Option<…>`", edits))
}

/// The token after the `?` at token `i` in `??` or `?.`, if it is one.
fn mark(cx: &Cx<'_>, i: usize) -> Option<crate::SyntaxKind> {
    let next = cx.kind(i + 1);
    let first = i == 0 || !(cx.kind(i - 1) == QUESTION && cx.touching(i - 1));
    (cx.kind(i) == QUESTION && matches!(next, QUESTION | DOT) && cx.touching(i) && first)
        .then_some(next)
}

/// The first token of the type that ends just before token `at`, when an annotation or a
/// result type holds it: names, `.`, and type arguments, after a `:` or a `->`.
fn type_start(cx: &Cx<'_>, at: usize) -> Option<usize> {
    let mut i = at;
    while let Some(last) = i.checked_sub(1) {
        match cx.kind(last) {
            UPPER_IDENT | LOWER_IDENT | DOT | COMMA | L_ANGLE | R_ANGLE | SHR => i = last,
            COLON | THIN_ARROW if i < at => return Some(i),
            _ => return None,
        }
    }
    None
}

/// `x!`, Swift's and Kotlin's unwrapping of an optional value.
pub(crate) fn unwrap(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    let after_value = matches!(cx.kind_before(1), R_PAREN | R_BRACK | LOWER_IDENT)
        && cx.before(1).is_some_and(|i| cx.touching(i));
    if cx.kind(at) != BANG || !after_value || cx.kind(at + 1) == EQ {
        return None;
    }
    let found = Foreign::new(
        "Stilt unwraps an `Option` with `.unwrap()`, not `!`",
        "`unwrap()` panics on `None`; `else` gives a fallback instead, as `x else 0`.",
    );
    Some(found.fix(
        "write `.unwrap()`",
        vec![Edit::replace(cx.range(at), ".unwrap()")],
    ))
}

/// The span of `&mut ` before `self`, which the fix writes `inout `.
pub(crate) fn inout_self(reference: TextRange) -> Foreign {
    let found = Foreign::new(
        "Stilt has no references: a method that changes its receiver takes `inout self`",
        "A method's receiver is a value, `self`; one that changes it takes `inout self`.",
    );
    found.fix(
        "write `inout self`",
        vec![Edit::replace(reference, "inout ")],
    )
}

/// What a lexical error says when it comes from another language's string: a string in
/// backticks, `\(x)` inserting a value, and `//` inside a string's `{…}`, where it begins a
/// comment.
pub(crate) fn lexical(text: &str, code: Code, at: usize) -> Option<Foreign> {
    let line = &text[at..];
    let line = &line[..line.find('\n').unwrap_or(line.len())];
    let span = |from: usize, len: usize| TextRange::at(offset(at + from), offset(len));
    if code == codes::E0002 && line.starts_with('`') {
        let found = Foreign::new(
            "Stilt writes a string in double quotes, and inserts a value as `{name}`",
            "Every string inserts the value of each `{…}` in it, as `\"hello {name}\"`.",
        );
        let Some(close) = line[1..].find('`') else {
            return Some(found);
        };
        let mut edits = vec![
            Edit::replace(span(0, 1), "\""),
            Edit::replace(span(close + 1, 1), "\""),
        ];
        edits.extend(
            line[..close]
                .match_indices("${")
                .map(|(i, _)| Edit::replace(span(i, 2), "{")),
        );
        return Some(found.fix("write it in double quotes", edits));
    }
    if code == codes::E0006 && line.starts_with("\\(") {
        let found = Foreign::new(
            "Stilt inserts a value in a string with `{n}`, not `\\(n)`",
            "Every string inserts the value of each `{…}` in it, as `\"hello {name}\"`.",
        );
        let Some(close) = line.find(')') else {
            return Some(found);
        };
        let edit = Edit::replace(span(0, close + 1), format!("{{{}}}", &line[2..close]));
        return Some(found.fix("write `{…}`", vec![edit]));
    }
    (code == codes::E0005 && comment_in_interpolation(line)).then(|| {
        Foreign::new(
            "`//` begins a comment, even inside a string's `{…}`",
            "Stilt divides with `/`, which rounds an integer quotient toward zero, and \
             `div_euclid` rounds it down.",
        )
    })
}

/// Whether `//` stands inside an interpolation of the string that starts `line`.
fn comment_in_interpolation(line: &str) -> bool {
    let bytes = line.as_bytes();
    let mut depth = 0usize;
    let mut i = 1;
    while i < bytes.len() {
        match bytes[i] {
            b'\\' => i += 1,
            b'{' => depth += 1,
            b'}' => depth = depth.saturating_sub(1),
            b'/' if depth > 0 && bytes.get(i + 1) == Some(&b'/') => return true,
            b'"' if depth == 0 => return false,
            _ => {}
        }
        i += 1;
    }
    false
}

fn offset(n: usize) -> rowan::TextSize {
    rowan::TextSize::from(u32::try_from(n).expect("a source file is under 4 GiB"))
}

/// `a ** b`, the power operator of Python, JavaScript and Ruby.
pub(crate) fn power(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    let star = at.checked_sub(1)?;
    if cx.kind(at) != STAR || cx.kind(star) != STAR || !cx.touching(star) {
        return None;
    }
    let found = Foreign::new(
        "Stilt raises a number to a power with `pow`, as `a.pow(2)`",
        "`pow` is a method of every integer and float type; an integer's can overflow.",
    );
    let base = star.checked_sub(1).filter(|&i| cx.kind(i) == LOWER_IDENT);
    let exponent = Some(at + 1).filter(|&i| matches!(cx.kind(i), LOWER_IDENT | INT));
    let (Some(base), Some(exponent)) = (base, exponent) else {
        return Some(found);
    };
    let written = format!("{}.pow({})", cx.word(base), cx.word(exponent));
    Some(found.fix(
        "write `pow`",
        vec![Edit::replace(cx.through(base, exponent), written)],
    ))
}
