//! The foreign syntax of declarations and of statement keywords that other languages write:
//! `interface`, `protocol`, `extension`, `async fn` and `await`, a variable outside a function,
//! `mutating`, Go's receivers and `type T struct`, a function or constant named in the other
//! case, `throws`, and `switch`, `guard`, `go` and `defer` (reference/messages.md).

use stilt_diag::Edit;

use crate::SyntaxKind::*;
use crate::foreign::{Cx, Foreign};

/// What the syntax error at `cx.at` says, if it comes from one of these forms.
pub(crate) fn items(cx: &Cx<'_>) -> Option<Foreign> {
    let rules: [fn(&Cx<'_>) -> Option<Foreign>; 5] =
        [kinds, functions, statements, names, parameters];
    rules.iter().find_map(|rule| rule(cx))
}

/// `interface`, `protocol` and `extension`, which begin a declaration.
fn kinds(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    if !matches!(cx.kind(at + 1), UPPER_IDENT) {
        return None;
    }
    let trait_help = "A trait lists the methods that a type implements, each in an `impl` of \
                      the trait for the type.";
    match cx.word(at) {
        "protocol" => {
            let found = Foreign::new("Stilt declares a protocol as a `trait`", trait_help);
            Some(found.fix("write `trait`", vec![Edit::replace(cx.range(at), "trait")]))
        }
        "interface" if holds_fields(cx, at) => Some(Foreign::new(
            "Stilt declares a record type as `type User = { name: str }`",
            "A record type is `type`, its name, `=` and its fields in braces.",
        )),
        "interface" => {
            let found = Foreign::new("Stilt declares an interface as a `trait`", trait_help);
            Some(found.fix("write `trait`", vec![Edit::replace(cx.range(at), "trait")]))
        }
        "extension" => {
            let found = Foreign::new(
                "Stilt adds methods to a type with `impl`",
                "`impl T { … }` adds methods to a type of the same module; a type of another \
                 module gets them through a trait.",
            );
            Some(found.fix("write `impl`", vec![Edit::replace(cx.range(at), "impl")]))
        }
        _ => None,
    }
}

/// Whether the braces after the declaration at `at` hold a field, a name and `:` on their own.
fn holds_fields(cx: &Cx<'_>, at: usize) -> bool {
    let Some(open) = (at..cx.tokens.len()).find(|&i| cx.kind(i) == L_CURLY) else {
        return false;
    };
    cx.inside(open, COLON)
        .into_iter()
        .any(|c| cx.kind(c - 1) == LOWER_IDENT && matches!(cx.kind(c - 2), L_CURLY | SEP | COMMA))
}

/// `async fn`, `mutating fn`, Go's `fn (p T) Name()`, and `throws` in a signature.
fn functions(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    match (cx.kind(at), cx.word(at)) {
        (ASYNC_KW, _) if cx.kind(at + 1) == FN_KW => {
            let found = Foreign::new(
                "Stilt has no `async fn`: a function that runs tasks has `async` in its row",
                "A function whose row holds `async` starts tasks or waits for them, as \
                 `fn f() -> i64 / async`.",
            );
            Some(found.fix("delete `async`", vec![Edit::delete(cx.with_blanks(at))]))
        }
        (AWAIT_KW, _) => Some(Foreign::new(
            "Stilt waits for a task with `.await()` after it, as `t.await()`",
            "`task.spawn(f)` starts a task and gives its handle, and `t.await()` waits for its \
             value.",
        )),
        (_, "mutating") if cx.kind(at + 1) == FN_KW => mutating(cx),
        (L_PAREN, _) if cx.kind_before(1) == FN_KW => Some(Foreign::new(
            "Stilt declares a method in an `impl` block, as `impl Point { fn norm(self) … }`",
            "A method takes `self` as its first parameter, inside `impl` and the type's name.",
        )),
        (_, "throws" | "throw") if cx.kind_before(1) == R_PAREN => {
            let found = Foreign::new(
                "Stilt names what a function raises in its row, as `/ raise<E>`",
                "The row after `/` lists what the function performs: `io`, and the error type \
                 it raises.",
            );
            Some(found.fix("delete `throws`", vec![Edit::delete(cx.with_blanks(at))]))
        }
        _ => None,
    }
}

/// `mutating fn bump(self)`, Swift's method that changes its receiver.
fn mutating(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    let found = Foreign::new(
        "Stilt marks a method that changes its receiver with `inout self`",
        "A method's receiver is a value, `self`; one that changes it takes `inout self`.",
    );
    let open = (at..cx.tokens.len()).find(|&i| matches!(cx.kind(i), L_PAREN | L_CURLY | SEP))?;
    if cx.kind(open) != L_PAREN || cx.kind(open + 1) != SELF_KW {
        return Some(found);
    }
    let edits = vec![
        Edit::delete(cx.with_blanks(at)),
        Edit::insert(cx.range(open + 1).start(), "inout "),
    ];
    Some(found.fix("write `inout self`", edits))
}

/// `switch`, `guard`, `go` and `defer`, which begin a statement, and a variable or binding
/// outside every function.
fn statements(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    if matches!(cx.kind(at), VAR_KW | LET_KW) && cx.kind(at + 1) == LOWER_IDENT && at_top(cx) {
        return Some(Foreign::new(
            "Stilt has no variable outside a function: a `const` never changes",
            "A function changes what its caller gives it as `inout`, so state is passed, not \
             shared.",
        ));
    }
    let keyword = at.checked_sub(1).filter(|&i| cx.statement_start(at) == i)?;
    match cx.word(keyword) {
        "switch" => {
            let found = Foreign::new(
                "Stilt writes `match`, whose arms are `pattern => value`",
                "A `match` runs the first arm whose pattern fits, with no fallthrough, and `_` \
                 matches anything.",
            );
            let open = (at..cx.tokens.len()).find(|&i| cx.kind(i) == L_CURLY);
            let arms = open.is_some_and(|o| {
                !cx.inside(o, FAT_ARROW).is_empty()
                    && (o..cx.closing(o).unwrap_or(o)).all(|i| cx.word(i) != "case")
            });
            if !arms {
                return Some(found);
            }
            Some(found.fix(
                "write `match`",
                vec![Edit::replace(cx.range(keyword), "match")],
            ))
        }
        "guard" => Some(Foreign::new(
            "Stilt has no `guard`: write `if !(…) { … }`, or `let x = o else …`",
            "`else` after a pattern of `let` runs when the pattern doesn't match, and must leave \
             the block.",
        )),
        "go" => Some(Foreign::new(
            "Stilt starts a task with `task.spawn(|| f(x))`",
            "`std.task` starts tasks and waits for them, in a function whose row holds `async`.",
        )),
        "defer" => Some(Foreign::new(
            "Stilt has no `defer`: write the code where the block ends",
            "A value's memory is freed after its last use, so cleanup is only for what a program \
             opens itself.",
        )),
        _ => None,
    }
}

/// Whether the token where the part breaks is outside every bracket.
fn at_top(cx: &Cx<'_>) -> bool {
    let mut depth = 0usize;
    for i in 0..cx.at {
        match cx.kind(i) {
            L_CURLY | L_PAREN | L_BRACK => depth += 1,
            R_CURLY | R_PAREN | R_BRACK => depth = depth.saturating_sub(1),
            _ => {}
        }
    }
    depth == 0
}

/// A function named in upper case, a constant named in lower case, and Go's `type T struct`.
fn names(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    match (cx.kind_before(1), cx.kind(at)) {
        (FN_KW, UPPER_IDENT) => {
            let name = lower(cx.word(at));
            let found = Foreign::new(
                format!("Stilt names a function in lower case, as `{name}`"),
                "A function's name is in snake case; `pub` makes it visible outside its module.",
            );
            Some(renamed(cx, found, (&name, &name), |i| {
                i == at || cx.kind(i + 1) == L_PAREN || cx.kind_before_token(i) == DOT
            }))
        }
        (CONST_KW, LOWER_IDENT) => {
            let name = cx.word(at).to_uppercase();
            let found = Foreign::new(
                format!("Stilt names a constant in upper case, as `{name}`"),
                "A constant's name is in upper case, and its type is written, as \
                 `const LIMIT: i64 = 10`.",
            );
            // A constant without its type gets the type of a literal value.
            let typed = match (cx.kind(at + 1), cx.kind(at + 2), cx.kind(at + 3)) {
                (EQ, value, SEP | EOF) => literal_type(value).map(|t| format!("{name}: {t}")),
                _ => None,
            };
            let declared = typed.as_deref().unwrap_or(&name);
            Some(renamed(cx, found, (&name, declared), |i| {
                let before = cx.kind_before_token(i);
                i == at
                    || !(matches!(before, LET_KW | VAR_KW | FN_KW | DOT | PIPE)
                        || cx.kind(i + 1) == COLON
                        || cx.kind(i + 1) == FAT_ARROW)
            }))
        }
        (UPPER_IDENT, _) if cx.kind_before(2) == TYPE_KW && cx.word(at) == "struct" => {
            let found = Foreign::new(
                "Stilt declares a record type as `type Point = { x: i64 }`",
                "A record type is `type`, its name, `=` and its fields in braces, each written \
                 `name: type`.",
            );
            let open = Some(at + 1).filter(|&i| cx.kind(i) == L_CURLY);
            if open.is_none_or(|o| cx.inside(o, COLON).is_empty()) {
                return Some(found);
            }
            Some(found.fix("write `=`", vec![Edit::replace(cx.range(at), "=")]))
        }
        _ => None,
    }
}

/// `found` with the fix that renames the declaration at `cx.at` to `name`, writing `declared`
/// there, and each other token of the file that writes its name, when `safe` says every one of
/// them names it and no token writes `name` already.
fn renamed(
    cx: &Cx<'_>,
    found: Foreign,
    (name, declared): (&str, &str),
    safe: impl Fn(usize) -> bool,
) -> Foreign {
    let (kind, old) = (cx.kind(cx.at), cx.word(cx.at));
    let uses: Vec<usize> = (0..cx.tokens.len())
        .filter(|&i| cx.kind(i) == kind && cx.word(i) == old)
        .collect();
    let taken = (0..cx.tokens.len()).any(|i| cx.word(i) == name);
    if taken || !uses.iter().all(|&i| safe(i)) {
        return found;
    }
    let edits = uses
        .into_iter()
        .map(|i| Edit::replace(cx.range(i), if i == cx.at { declared } else { name }))
        .collect();
    found.fix(&format!("rename it `{name}`"), edits)
}

/// The type of a literal token, as its default type gives it (numbers.literal-defaults).
fn literal_type(kind: crate::SyntaxKind) -> Option<&'static str> {
    match kind {
        INT => Some("i64"),
        FLOAT => Some("f64"),
        STRING => Some("str"),
        TRUE_KW | FALSE_KW => Some("bool"),
        _ => None,
    }
}

/// A name in snake case.
fn lower(name: &str) -> String {
    let mut out = String::new();
    for (i, c) in name.chars().enumerate() {
        if c.is_uppercase() && i > 0 {
            out.push('_');
        }
        out.extend(c.to_lowercase());
    }
    out
}

/// A parameter without its type, as `fn add(a, b)`, or with its type after a space, as Go's
/// `fn add(a int)`, and a union of types, as `type Id = str | i64`.
fn parameters(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    if cx.kind_before(1) == EQ && cx.kind_before(2) == UPPER_IDENT && cx.kind_before(3) == TYPE_KW {
        let end = cx.statement_end(at);
        return (at..end).any(|i| cx.kind(i) == PIPE).then(|| {
            Foreign::new(
                "Stilt's variant type names each case, as `type Id = | Name(str) | Number(i64)`",
                "A variant type is `type`, its name, `=` and its variants, each after `|`, \
                 each holding its own values.",
            )
        });
    }
    let name = at.checked_sub(1).filter(|&i| cx.kind(i) == LOWER_IDENT)?;
    let in_signature = matches!(cx.kind_before(2), L_PAREN | COMMA)
        && crate::foreign_words::in_parameters(cx, name);
    if !in_signature {
        return None;
    }
    match cx.kind(at) {
        COMMA | R_PAREN => Some(Foreign::new(
            format!(
                "Stilt writes a parameter's type after it, as `{}: i64`",
                cx.word(name)
            ),
            "Types are inferred inside a body, never in a signature, so a reader sees what a \
             function takes.",
        )),
        LOWER_IDENT | UPPER_IDENT => {
            let found = Foreign::new(
                format!(
                    "Stilt writes a parameter's type after `:`, as `{}: i64`",
                    cx.word(name)
                ),
                "A parameter is its name, `:` and its type.",
            );
            let open = crate::foreign_forms::enclosing(cx, at, L_PAREN)?;
            let close = cx.closing(open)?;
            let edits = crate::foreign_forms::items(cx, open, close)
                .into_iter()
                .filter(|&(first, last)| {
                    last > first
                        && cx.kind(first) == LOWER_IDENT
                        && matches!(cx.kind(first + 1), LOWER_IDENT | UPPER_IDENT)
                })
                .map(|(first, _)| Edit::insert(cx.range(first).end(), ":"))
                .collect();
            Some(found.fix("write `:`", edits))
        }
        _ => None,
    }
}
