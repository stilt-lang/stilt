//! The foreign syntax that words of other languages begin: `let mut`, `function`, `elif`,
//! `throw`, `and`, `struct`, `import` and the like (reference/messages.md).

use rowan::TextRange;
use stilt_diag::Edit;

use crate::SyntaxKind::*;
use crate::foreign::{Cx, Foreign};

/// A word of another language in a body.
pub(crate) fn words(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    let previous = cx.word_before(1);
    if previous == "mut" && cx.kind_before(2) == LET_KW {
        let found = Foreign::new(
            "Stilt declares a variable that changes with `var`, not `let mut`",
            "A `let` binding never changes, and a `var` binding can, so no `mut` is needed.",
        );
        let written = cx.through(at - 2, at - 1);
        return Some(found.fix("write `var`", vec![Edit::replace(written, "var")]));
    }
    let replaced = |word: &str, with: &str, help| {
        let found = Foreign::new(format!("Stilt writes `{with}`, not `{word}`"), help);
        Some(found.fix(
            &format!("write `{with}`"),
            vec![Edit::replace(cx.range(at), with)],
        ))
    };
    match cx.word(at) {
        w @ ("elif" | "elsif" | "elseif") if cx.kind_before(1) == R_CURLY => {
            replaced(w, "else if", "An `if` chains to another with `else if`.")
        }
        w @ ("and" | "or") if cx.at > 0 => {
            let with = if w == "and" { "&&" } else { "||" };
            let end = cx.statement_end(at);
            let edits = (cx.statement_start(at)..end)
                .filter(|&i| cx.word(i) == w)
                .map(|i| Edit::replace(cx.range(i), with))
                .collect();
            let found = Foreign::new(
                format!("Stilt writes `{with}`, not `{w}`"),
                "`&&`, `||` and `!` work on `bool`s.",
            );
            Some(found.fix(&format!("write `{with}`"), edits))
        }
        _ => previous_word(cx, previous),
    }
}

/// A word of another language just before the token where the part breaks.
fn previous_word(cx: &Cx<'_>, previous: &str) -> Option<Foreign> {
    let at = cx.at;
    let before = || cx.range(at - 1);
    match previous {
        "throw" => {
            let found = Foreign::new(
                "Stilt raises an error with `raise`, not `throw`",
                "`raise` ends the function with the error, which its row names, as `/ raise<E>`.",
            );
            Some(found.fix("write `raise`", vec![Edit::replace(before(), "raise")]))
        }
        "not" => {
            let found = Foreign::new(
                "Stilt writes `!`, not `not`",
                "`&&`, `||` and `!` work on `bool`s.",
            );
            let written = TextRange::new(before().start(), cx.range(at).start());
            Some(found.fix("write `!`", vec![Edit::replace(written, "!")]))
        }
        "new" => Some(Foreign::new(
            format!(
                "Stilt has no `new`: a record is built with its fields, as `{} {{ … }}`",
                cx.word(at)
            ),
            "A record literal names each field, as `Point { x: 0, y: 0 }`, and a type's own functions are named on it, as `List.new()`.",
        )),
        "lambda" => lambda(cx),
        _ => quotes(cx),
    }
}

/// `lambda x: body`, Python's closure.
fn lambda(cx: &Cx<'_>) -> Option<Foreign> {
    let colon = (cx.at + 1..cx.statement_end(cx.at)).find(|&i| cx.kind(i) == COLON)?;
    let params = TextRange::new(cx.range(cx.at).start(), cx.range(colon - 1).end());
    let written = TextRange::new(cx.range(cx.at - 1).start(), cx.range(colon).end());
    let found = Foreign::new(
        "Stilt writes a closure as `|x| x * 2`",
        "A closure is its parameters between `|`, then its body.",
    );
    let edit = Edit::replace(written, format!("|{}|", &cx.text[params]));
    Some(found.fix("write the closure with `|`", vec![edit]))
}

/// A string in single quotes, and a function's result type after `:`.
fn quotes(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    if cx.kind(at) == QUOTE {
        let start = usize::from(cx.range(at).start());
        let line = &cx.text[start + 1..];
        let line = &line[..line.find('\n').unwrap_or(line.len())];
        let close = line.find('\'')?;
        let found = Foreign::new(
            format!(
                "Stilt writes a string in double quotes, as \"{}\"",
                &line[..close]
            ),
            "A string holds any text, one character or more, and is written in `\"`.",
        );
        let end = rowan::TextSize::from(u32::try_from(start + 1 + close).expect("a short file"));
        let edits = vec![
            Edit::replace(cx.range(at), "\""),
            Edit::replace(TextRange::at(end, 1.into()), "\""),
        ];
        return Some(found.fix("write it in double quotes", edits));
    }
    if cx.kind(at) == COLON && cx.kind_before(1) == R_PAREN && in_signature(cx) {
        let found = Foreign::new(
            "Stilt writes a function's result type after `->`, not `:`",
            "A signature is the parameters, then `->` and the result type, then the row after `/`.",
        );
        return Some(found.fix("write `->`", vec![Edit::replace(cx.range(at), " ->")]));
    }
    braces(cx)
}

/// Whether the token where the part breaks follows the parameters of a function's signature.
fn in_signature(cx: &Cx<'_>) -> bool {
    cx.opening(cx.at - 1).is_some_and(|open| declares(cx, open))
}

/// Whether token `i` is inside the parameters of a function's signature.
pub(crate) fn in_parameters(cx: &Cx<'_>, i: usize) -> bool {
    let mut depth = 0usize;
    for j in (0..i).rev() {
        match cx.kind(j) {
            R_PAREN | R_BRACK | R_CURLY => depth += 1,
            L_PAREN if depth == 0 => return declares(cx, j),
            L_PAREN | L_BRACK | L_CURLY if depth > 0 => depth -= 1,
            L_BRACK | L_CURLY => return false,
            _ => {}
        }
    }
    false
}

/// Whether the `(` at token `open` opens a function's parameters: `fn`, the name, and its
/// generics, if it has any.
fn declares(cx: &Cx<'_>, open: usize) -> bool {
    let mut name = open.checked_sub(1);
    if let Some(close) = name.filter(|&i| cx.kind(i) == R_ANGLE) {
        let mut depth = 0usize;
        name = (0..=close).rev().find(|&j| {
            match cx.kind(j) {
                R_ANGLE => depth += 1,
                L_ANGLE => depth -= 1,
                _ => {}
            }
            depth == 0
        });
        name = name.and_then(|j| j.checked_sub(1));
    }
    name.and_then(|i| i.checked_sub(1))
        .is_some_and(|i| cx.kind(i) == FN_KW)
}

/// A branch or a loop's body without braces, as `if n > 0 return 1`, and C's `for (…)`.
fn braces(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    if cx.kind_before(1) == L_PAREN && cx.kind_before(2) == FOR_KW {
        return Some(Foreign::new(
            "Stilt loops over a range, as `for i in 0..n`, or a list, as `for x in xs`",
            "A `for` loop takes each value of what follows `in`; a `while` loop runs while its condition holds.",
        ));
    }
    let start = cx.statement_start(at);
    let keyword = (start..at).find(|&i| matches!(cx.kind(i), IF_KW | WHILE_KW))?;
    let simple = (keyword..at).all(|i| !matches!(cx.kind(i), L_CURLY | R_CURLY));
    if !simple
        || !matches!(
            cx.kind(at),
            RETURN_KW | BREAK_KW | CONTINUE_KW | LOWER_IDENT
        )
    {
        return None;
    }
    let end = cx.statement_end(at);
    let found = Foreign::new(
        format!("the body of `{}` is a block, in braces", cx.word(keyword)),
        "Braces always mark a branch or a loop's body, so the condition needs no parentheses.",
    );
    let edits = vec![
        Edit::insert(cx.range(at).start(), "{ "),
        Edit::insert(cx.range(end - 1).end(), " }"),
    ];
    Some(found.fix("write the body in braces", edits))
}

/// A declaration that begins with another language's word: `function`, `def`, `public`,
/// `import`, `struct`, `class` or `enum`.
pub(crate) fn declarations(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    let word = cx.word(at);
    let named = matches!(cx.kind(at + 1), LOWER_IDENT | UPPER_IDENT);
    let replaced = |with: &str, message: String, help| {
        let found = Foreign::new(message, help);
        Some(found.fix(
            &format!("write `{with}`"),
            vec![Edit::replace(cx.range(at), with)],
        ))
    };
    match word {
        "function" | "func" | "fun" | "def" if named => replaced(
            "fn",
            format!("Stilt declares a function with `fn`, not `{word}`"),
            "A function is `fn`, its name, its parameters with their types, and `->` and its result type.",
        ),
        "public" | "export" if cx.kind(at + 1) == FN_KW || cx.kind(at + 1) == TYPE_KW => replaced(
            "pub",
            format!("Stilt marks an item public with `pub`, not `{word}`"),
            "An item is private to its module unless it is `pub`.",
        ),
        "import" | "require" | "include" if cx.word(at + 1) == "std" => replaced(
            "use",
            format!("Stilt imports a module with `use`, not `{word}`"),
            "`use std.fs` imports a module, whose items are then named through it, as `fs.exists`.",
        ),
        "struct" if named => record(cx),
        "class" if named => Some(Foreign::new(
            "Stilt declares a record type as `type Point = { x: i64 }`, and its methods in `impl Point`",
            "A type holds data, and its methods are in an `impl` block of their own.",
        )),
        "enum" if named => variants(cx),
        _ => None,
    }
}

/// `struct Point { x: i64 }`, which Stilt writes `type Point = { x: i64 }`.
fn record(cx: &Cx<'_>) -> Option<Foreign> {
    let open = (cx.at..cx.tokens.len()).find(|&i| matches!(cx.kind(i), L_CURLY | SEP | EOF))?;
    let found = Foreign::new(
        "Stilt declares a record type as `type Point = { x: i64, y: i64 }`",
        "A record type is `type`, its name, `=` and its fields in braces.",
    );
    if cx.kind(open) != L_CURLY {
        return Some(found);
    }
    let edits = vec![
        Edit::replace(cx.range(cx.at), "type"),
        Edit::insert(cx.range(open).start(), "= "),
    ];
    Some(found.fix("write `type … =`", edits))
}

/// `enum Color { Red, Green }`, which Stilt writes `type Color = | Red | Green`. The fix
/// writes one on a single line.
fn variants(cx: &Cx<'_>) -> Option<Foreign> {
    let found = Foreign::new(
        "Stilt declares a variant type as `type Color = | Red | Green`",
        "A variant type is `type`, its name, `=` and its variants, each after `|`.",
    );
    let Some(open) = (cx.at..cx.tokens.len())
        .find(|&i| matches!(cx.kind(i), L_CURLY | SEP | EOF))
        .filter(|&i| cx.kind(i) == L_CURLY)
    else {
        return Some(found);
    };
    let commas = cx.inside(open, COMMA);
    let close = cx.closing(open)?;
    if close == open + 1 || (open..close).any(|i| cx.kind(i) == SEP) {
        return Some(found);
    }
    let mut edits = vec![
        Edit::replace(cx.range(cx.at), "type"),
        Edit::replace(cx.with_blanks(open), "= | "),
    ];
    for &comma in &commas {
        let last = comma + 1 == close;
        edits.push(Edit::replace(cx.range(comma), if last { "" } else { " |" }));
    }
    let before_close = TextRange::new(cx.range(close - 1).end(), cx.range(close).end());
    edits.push(Edit::delete(before_close));
    Some(found.fix("write `type … = | …`", edits))
}
