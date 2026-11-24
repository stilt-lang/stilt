//! The heads of expressions.heads, derived from `expr` as `reference/03-syntax.md` defines them
//! under "Heads": the rules of `expr`, `postfix`, `built`, `primary` and `catch_arm` get a copy
//! with the suffix `_h`, in which the struct literal, block, `if`, `match`, loop, `with`, `when`
//! and `unsafe` forms, the handler literal, the staging annotations, the block form of `catch` and
//! the trailing block of a `macro_use` are missing, and which refers to the copies wherever an
//! expression stands outside `(…)` and `[…]`.

use crate::ebnf::Expr;
use crate::expand::Grammar;

/// The rules that a head copies.
const FAMILY: [&str; 5] = ["expr", "postfix", "built", "primary", "catch_arm"];
/// The primary forms that a head leaves out.
const LEFT_OUT_RULES: [&str; 3] = ["struct", "block", "if"];
/// The keywords that start the primary forms a head leaves out.
const LEFT_OUT_KEYWORDS: [&str; 9] = [
    "match", "loop", "while", "for", "with", "when", "unsafe", "handler", "comptime",
];

/// Adds the copy of each rule of the family, and points `head` at the copy of `expr`.
pub(crate) fn derive(grammar: &mut Grammar) -> Result<(), String> {
    for name in FAMILY {
        let body = grammar
            .get(name)
            .ok_or_else(|| format!("the heads need a rule `{name}`"))?
            .clone();
        grammar.set(&format!("{name}_h"), headed(&body, 0));
    }
    for (_, body) in &mut grammar.rules {
        rename_head(body);
    }
    Ok(())
}

fn rename_head(expr: &mut Expr) {
    match expr {
        Expr::Ref(name) if name == "head" => *name = "expr_h".into(),
        Expr::Seq(items) | Expr::Alt(items) => items.iter_mut().for_each(rename_head),
        Expr::Opt(inner) | Expr::Star(inner) => rename_head(inner),
        _ => {}
    }
}

/// The copy of `expr`, found at bracket depth `depth`.
fn headed(expr: &Expr, depth: usize) -> Expr {
    match expr {
        Expr::Ref(name) if depth == 0 && FAMILY.contains(&name.as_str()) => {
            Expr::Ref(format!("{name}_h"))
        }
        Expr::Seq(items) => {
            let mut depth = depth;
            let mut out = Vec::new();
            for item in items {
                if depth == 0 && matches!(item, Expr::Opt(inner) if left_out(inner)) {
                    continue;
                }
                out.push(headed(item, depth));
                match item {
                    Expr::Lit(l) if l == "(" || l == "[" => depth += 1,
                    Expr::Lit(l) if l == ")" || l == "]" => depth = depth.saturating_sub(1),
                    _ => {}
                }
            }
            Expr::Seq(out)
        }
        Expr::Alt(items) => {
            let mut kept: Vec<Expr> = items
                .iter()
                .filter(|branch| !left_out(branch))
                .map(|branch| headed(branch, depth))
                .collect();
            if kept.len() == 1 {
                kept.remove(0)
            } else {
                Expr::Alt(kept)
            }
        }
        Expr::Opt(inner) => Expr::Opt(Box::new(headed(inner, depth))),
        Expr::Star(inner) => Expr::Star(Box::new(headed(inner, depth))),
        _ => expr.clone(),
    }
}

/// Whether the alternative is a form that a head leaves out, by its first element: a struct
/// literal, block, `if`, `match`, loop or staging annotation, or the `{` of the block form of
/// `catch`.
fn left_out(branch: &Expr) -> bool {
    match branch {
        Expr::Ref(name) => LEFT_OUT_RULES.contains(&name.as_str()),
        Expr::Lit(text) => text == "{" || LEFT_OUT_KEYWORDS.contains(&text.as_str()),
        Expr::Seq(items) => items.first().is_some_and(left_out),
        _ => false,
    }
}
