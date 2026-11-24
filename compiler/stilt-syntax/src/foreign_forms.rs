//! The foreign syntax of expressions and statements that other languages write: argument
//! labels, list comprehensions, `x in xs`, prefixed strings, map literals, trailing closures,
//! `[T]` types, several values after `return`, blocks after `:`, Go's `for` loops and a `catch`
//! with its binding in parentheses (reference/messages.md).

use rowan::TextRange;
use stilt_diag::Edit;

use crate::SyntaxKind::{self, *};
use crate::foreign::{Cx, Foreign};

/// What the syntax error at `cx.at` says, if it comes from one of these forms.
pub(crate) fn forms(cx: &Cx<'_>) -> Option<Foreign> {
    let rules: [fn(&Cx<'_>) -> Option<Foreign>; 10] = [
        labels,
        comprehension,
        membership,
        prefixed_string,
        map_literal,
        trailing_closure,
        bracket_types,
        tuple_return,
        loops,
        catch_parens,
    ];
    rules.iter().find_map(|rule| rule(cx))
}

/// The text from the start of token `i` to the end of token `j`, trimmed: empty when `j`
/// comes before `i`.
fn text<'t>(cx: &Cx<'t>, i: usize, j: usize) -> &'t str {
    if j < i {
        return "";
    }
    cx.text[cx.through(i, j)].trim()
}

/// The bracket of `kind` left open before token `at`, if the innermost one is of that kind.
pub(crate) fn enclosing(cx: &Cx<'_>, at: usize, kind: SyntaxKind) -> Option<usize> {
    let mut depth = 0usize;
    for i in (0..at).rev() {
        match cx.kind(i) {
            R_PAREN | R_BRACK | R_CURLY => depth += 1,
            L_PAREN | L_BRACK | L_CURLY if depth == 0 => return (cx.kind(i) == kind).then_some(i),
            L_PAREN | L_BRACK | L_CURLY => depth -= 1,
            _ => {}
        }
    }
    None
}

/// The tokens directly inside the bracket at `open`, split at its commas, each as its first and
/// last token, separators left out.
pub(crate) fn items(cx: &Cx<'_>, open: usize, close: usize) -> Vec<(usize, usize)> {
    let mut parts = Vec::new();
    let mut start = open + 1;
    for comma in cx.inside(open, COMMA).into_iter().chain([close]) {
        let first = (start..comma).find(|&i| cx.kind(i) != SEP);
        let last = (start..comma).rev().find(|&i| cx.kind(i) != SEP);
        if let (Some(first), Some(last)) = (first, last) {
            parts.push((first, last));
        }
        start = comma + 1;
    }
    parts
}

/// The text of an operand, in parentheses when it holds a space.
fn operand(text: &str) -> String {
    if text.contains(char::is_whitespace) {
        format!("({text})")
    } else {
        text.to_owned()
    }
}

/// `greet(name: "ada")`, Swift's and Python's labeled arguments.
fn labels(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    if cx.kind(at) != COLON || cx.kind_before(1) != LOWER_IDENT {
        return None;
    }
    let open = enclosing(cx, at, L_PAREN)?;
    let callee = open.checked_sub(1)?;
    let declared = callee.checked_sub(1).is_some_and(|i| cx.kind(i) == FN_KW);
    if declared || !matches!(cx.kind(callee), LOWER_IDENT | UPPER_IDENT | R_PAREN) {
        return None;
    }
    let close = cx.closing(open)?;
    let edits = items(cx, open, close)
        .into_iter()
        .filter(|&(first, last)| {
            last > first + 1 && cx.kind(first) == LOWER_IDENT && cx.kind(first + 1) == COLON
        })
        .map(|(first, _)| {
            Edit::delete(TextRange::new(
                cx.range(first).start(),
                cx.with_blanks(first + 1).end(),
            ))
        })
        .collect();
    let found = Foreign::new(
        "Stilt's arguments have no labels: each is given in its parameter's place",
        "A call gives one argument per parameter, in order, as `greet(\"ada\")`.",
    );
    Some(found.fix("delete the labels", edits))
}

/// `[x * 2 for x in xs if x > 0]`, Python's list comprehension.
fn comprehension(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    if cx.kind(at) != FOR_KW {
        return None;
    }
    let open = enclosing(cx, at, L_BRACK)?;
    let close = cx.closing(open)?;
    let inside = cx.inside(open, IN_KW);
    let within = cx.inside(open, IF_KW);
    let r#in = *inside.first()?;
    let cond = within.first().copied().filter(|&i| i > r#in);
    let source = operand(text(cx, r#in + 1, cond.unwrap_or(close) - 1));
    let (value, pattern) = (text(cx, open + 1, at - 1), text(cx, at + 1, r#in - 1));
    if value.is_empty() || pattern.is_empty() || source.is_empty() {
        return None;
    }
    let mapped = format!(".map(|{pattern}| {value})");
    let written = match cond {
        Some(i) => {
            let filtered = format!(
                "{source}.filter(|{pattern}| {})",
                text(cx, i + 1, close - 1)
            );
            if value == pattern {
                filtered
            } else {
                filtered + &mapped
            }
        }
        None => source + &mapped,
    };
    let found = Foreign::new(
        "Stilt makes a list from another with `map` and `filter`, as `xs.map(|x| x * 2)`",
        "`map` gives a new list of each element's result, and `filter` keeps the elements a test \
         holds of.",
    );
    Some(found.fix(
        "write `map`",
        vec![Edit::replace(cx.through(open, close), written)],
    ))
}

/// `x in xs` as a condition, Python's membership test.
fn membership(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    if cx.kind(at) != IN_KW {
        return None;
    }
    let mut start = cx.statement_start(at);
    if (start..at).any(|i| cx.kind(i) == FOR_KW) {
        return None;
    }
    if matches!(cx.kind(start), IF_KW | WHILE_KW) {
        start += 1;
    }
    let negated = cx.word(start) == "not" || cx.kind(start) == BANG;
    let left = if negated { start + 1 } else { start };
    let mut depth = 0usize;
    let end = (at + 1..cx.tokens.len()).find(|&i| match cx.kind(i) {
        L_PAREN | L_BRACK => {
            depth += 1;
            false
        }
        R_PAREN | R_BRACK if depth > 0 => {
            depth -= 1;
            false
        }
        L_CURLY | R_CURLY | R_PAREN | R_BRACK | SEP | COMMA | EOF => depth == 0,
        _ => false,
    })?;
    if left >= at || end <= at + 1 {
        return None;
    }
    let bang = if negated { "!" } else { "" };
    let written = format!(
        "{bang}{}.contains({})",
        operand(text(cx, at + 1, end - 1)),
        text(cx, left, at - 1)
    );
    let found = Foreign::new(
        "Stilt tests whether a list holds a value with `contains`, as `xs.contains(x)`",
        "`contains` is a method of lists, sets, maps (of their keys) and strings.",
    );
    let edit = Edit::replace(cx.through(start, end - 1), written);
    Some(found.fix("write `contains`", vec![edit]))
}

/// `f"…"`, Python's formatted string, and its other prefixes.
fn prefixed_string(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    let prefix = at.checked_sub(1)?;
    let prefixed = matches!(cx.word(prefix), "f" | "r" | "b" | "u" | "fr" | "rf" | "s");
    if !matches!(cx.kind(at), STRING | STRING_HEAD) || !prefixed || !cx.touching(prefix) {
        return None;
    }
    let found = Foreign::new(
        format!("Stilt's strings take no `{}` before them", cx.word(prefix)),
        "Every string inserts the value of each `{…}` in it, as `\"hello {name}\"`, and `{{` \
         writes a brace.",
    );
    Some(found.fix("delete the prefix", vec![Edit::delete(cx.range(prefix))]))
}

/// `{"ada": 36}`, a map literal of Python, JavaScript or Swift.
fn map_literal(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    if cx.kind(at) != COLON || !matches!(cx.kind_before(1), STRING | INT | TRUE_KW | FALSE_KW) {
        return None;
    }
    let open = at.checked_sub(2).filter(|&i| cx.kind(i) == L_CURLY)?;
    let close = cx.closing(open)?;
    let mut pairs = Vec::new();
    for (first, last) in items(cx, open, close) {
        let colon = (first..=last).find(|&i| cx.kind(i) == COLON)?;
        if colon == first || colon == last {
            return None;
        }
        pairs.push(format!(
            "({}, {})",
            text(cx, first, colon - 1),
            text(cx, colon + 1, last)
        ));
    }
    let written = format!("Map.from_entries([{}])", pairs.join(", "));
    let found = Foreign::new(
        "Stilt has no map literal: `Map.from_entries` builds a map from pairs",
        "A map is built from a list of `(key, value)` pairs, or with `Map.new()` and \
         `m[k] = v`.",
    );
    Some(found.fix(
        "write `Map.from_entries`",
        vec![Edit::replace(cx.through(open, close), written)],
    ))
}

/// `xs.map { x in x * 2 }`, Swift's trailing closure.
fn trailing_closure(cx: &Cx<'_>) -> Option<Foreign> {
    let open = cx.at;
    if cx.kind(open) != L_CURLY || cx.kind_before(1) != LOWER_IDENT || cx.kind_before(2) != DOT {
        return None;
    }
    let close = cx.closing(open)?;
    let r#in = *cx.inside(open, IN_KW).first()?;
    let (params, body) = (text(cx, open + 1, r#in - 1), text(cx, r#in + 1, close - 1));
    if params.is_empty() || body.is_empty() {
        return None;
    }
    let written = format!("(|{params}| {body})");
    let found = Foreign::new(
        "Stilt passes a closure inside the call's parentheses, as `xs.map(|x| x * 2)`",
        "A closure is its parameters between `|`, then its body, and a call's arguments are \
         always in its parentheses.",
    );
    let edit = Edit::replace(
        TextRange::new(cx.range(open - 1).end(), cx.range(close).end()),
        written,
    );
    Some(found.fix("pass the closure in parentheses", vec![edit]))
}

/// `[T]` and `[K: V]`, Swift's list and dictionary types.
fn bracket_types(cx: &Cx<'_>) -> Option<Foreign> {
    let open = cx.at;
    let typed = cx.kind_before(1) == THIN_ARROW
        || (cx.kind_before(1) == COLON && cx.kind_before(2) == LOWER_IDENT);
    if cx.kind(open) != L_BRACK || !typed {
        return None;
    }
    let close = cx.closing(open)?;
    if close == open + 1 {
        return None;
    }
    let colon = cx.inside(open, COLON);
    let (message, written) = match colon.first() {
        Some(&c) => (
            "Stilt writes a map type as `Map<K, V>`",
            format!(
                "Map<{}, {}>",
                text(cx, open + 1, c - 1),
                text(cx, c + 1, close - 1)
            ),
        ),
        None => (
            "Stilt writes a list type as `List<T>`",
            format!("List<{}>", text(cx, open + 1, close - 1)),
        ),
    };
    let found = Foreign::new(
        message,
        "Brackets build a list value, as `[1, 2]`; a type names its kind, as `List<i64>`.",
    );
    Some(found.fix(
        "write the type",
        vec![Edit::replace(cx.through(open, close), written)],
    ))
}

/// `return a, b`, Go's and Python's several results.
fn tuple_return(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    let start = cx.statement_start(at);
    if cx.kind(at) != COMMA || start == 0 || cx.kind(start - 1) != RETURN_KW {
        return None;
    }
    let mut depth = 0usize;
    let end = (at..cx.tokens.len()).find(|&i| match cx.kind(i) {
        L_PAREN | L_BRACK | L_CURLY => {
            depth += 1;
            false
        }
        R_PAREN | R_BRACK | R_CURLY if depth > 0 => {
            depth -= 1;
            false
        }
        R_PAREN | R_BRACK | R_CURLY | SEP | EOF => true,
        _ => false,
    })?;
    let found = Foreign::new(
        "Stilt returns several values as one tuple, as `return (a, b)`",
        "A tuple groups values in parentheses. A failure is raised with `raise`, not returned \
         beside the result.",
    );
    let edits = vec![
        Edit::insert(cx.range(start).start(), "("),
        Edit::insert(cx.range(end - 1).end(), ")"),
    ];
    Some(found.fix("return a tuple", edits))
}

/// Go's `for cond {`, `for {` and `for i, x := range xs {`, and a block after `:`.
fn loops(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    let start = cx.statement_start(at);
    let head = cx.kind(start);
    if cx.kind(at) == COLON && matches!(head, IF_KW | WHILE_KW | FOR_KW | ELSE_KW) {
        return Some(Foreign::new(
            "Stilt writes a block in braces, as `if c { … }`, not after `:`",
            "Braces mark every block, so a block's indentation is free.",
        ));
    }
    if head != FOR_KW {
        return None;
    }
    let replaced = |message: &'static str, with: &'static str| {
        let found = Foreign::new(
            message,
            "`while c { … }` runs as long as `c` holds, `loop { … }` until a `break`, and \
             `for x in xs` takes each value of `xs`.",
        );
        Some(found.fix(
            &format!("write `{with}`"),
            vec![Edit::replace(cx.range(start), with)],
        ))
    };
    match cx.kind(at) {
        L_ANGLE | R_ANGLE | LTEQ | GTEQ | EQ2 | NEQ => {
            replaced("Stilt loops while a condition holds with `while`", "while")
        }
        L_CURLY if at == start + 1 => replaced("Stilt loops forever with `loop`", "loop"),
        COMMA if at == start + 2 => range_loop(cx, start),
        _ => None,
    }
}

/// `for i, x := range xs {` and `for i, x in enumerate(xs):`.
fn range_loop(cx: &Cx<'_>, start: usize) -> Option<Foreign> {
    let found = Foreign::new(
        "Stilt loops with each index as `for (i, x) in xs.enumerate(0)`",
        "A `for` takes one pattern, here a tuple of the index and the element.",
    );
    let open = (start..cx.tokens.len()).find(|&i| matches!(cx.kind(i), L_CURLY | SEP | EOF))?;
    let range = (start..open).find(|&i| cx.word(i) == "range");
    let (Some(range), L_CURLY) = (range, cx.kind(open)) else {
        return Some(found);
    };
    let pattern = text(cx, start + 1, start + 3);
    let source = operand(text(cx, range + 1, open - 1));
    let written = format!("({pattern}) in {source}.enumerate(0)");
    let edit = Edit::replace(cx.through(start + 1, open - 1), written);
    Some(found.fix("write `enumerate`", vec![edit]))
}

/// `catch (e) {`, the `catch` of JavaScript, Java and C++.
fn catch_parens(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    if cx.kind(at) != L_CURLY || cx.kind_before(1) != R_PAREN {
        return None;
    }
    let open = cx.opening(at - 1)?;
    if open == 0 || cx.kind(open - 1) != CATCH_KW {
        return None;
    }
    let found = Foreign::new(
        "Stilt writes a `catch` with arms, as `catch e => { … }`",
        "A `catch` takes arms like a `match`'s: a pattern, `=>` and the value.",
    );
    let binding = text(cx, open + 1, at - 2);
    if binding.is_empty() {
        return None;
    }
    let binding = binding.split(':').next().unwrap_or(binding).trim();
    let edit = Edit::replace(cx.through(open, at - 1), format!("{binding} =>"));
    Some(found.fix("write an arm", vec![edit]))
}
