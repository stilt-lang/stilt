//! The tree-sitter grammar of `editors/tree-sitter/`, from the productions of
//! `reference/03-syntax.md` with the heads of expressions.heads, the precedence table of
//! expressions.precedence and the lexemes of `src/lexicon.rs`. A newline that ends a statement is
//! the external token `_line_end`, which `src/scanner.c` reads where the grammar accepts a
//! separator, as lexical.terminator-insertion inserts one (`treesitter_scanner.rs`).

use std::collections::BTreeSet;
use std::fmt::Write;

use crate::ebnf::Expr;
use crate::expand::Grammar;
use crate::lexical::Lexical;
use crate::lexicon;

/// The grammar's path.
pub(crate) const GRAMMAR: &str = "editors/tree-sitter/grammar.js";

/// The sets of rules between which tree-sitter's parser keeps both readings until the text tells
/// them apart, as the productions are ambiguous on their own (syntax.ambiguities). `tree-sitter
/// generate` names each set that a change of the productions needs.
const CONFLICTS: [&[&str]; 19] = [
    &["file"],
    &["sep"],
    &["lower_path"],
    &["list1_field"],
    &["sep", "semicolons"],
    &["lower_path", "path"],
    &["path"],
    &["postfix", "built"],
    &["type_arg", "list1_type"],
    &["postfix_h", "built_h"],
    &["if"],
    &["tokens"],
    &["tokens", "primary"],
    &["type"],
    &["matcher"],
    &["arms_match_arm"],
    &["fn_type"],
    &["arms_catch_arm"],
    &["t_item"],
];

/// The productions as tree-sitter reads them: the heads derived, the doc comments read as
/// comments, a separator allowed after each `{` and a `;` before each `}`.
pub(crate) fn productions(markdown: &str, lexical: &Lexical) -> Result<Grammar, String> {
    let mut grammar = crate::expand::expand(&crate::ebnf::extract(markdown)?)?;
    crate::heads::derive(&mut grammar)?;
    crate::shape::add_tokens(&mut grammar, &lexical.macro_tokens()?);
    for (_, body) in &mut grammar.rules {
        *body = around_braces(&crate::shape::simplify(body));
    }
    // Separators are ignored at the start and the end of the file (lexical.separators).
    let sep = || Expr::Opt(Box::new(Expr::Ref("sep".into())));
    let file = Expr::Ref("file".into());
    grammar
        .rules
        .insert(0, ("source".into(), Expr::Seq(vec![sep(), file, sep()])));
    Ok(grammar)
}

/// The text of `grammar.js`.
pub(crate) fn emit(markdown: &str, lexical: &Lexical, expressions: &str) -> Result<String, String> {
    let grammar = productions(markdown, lexical)?;
    let levels = levels(expressions)?;
    let nullable = nullable(&grammar);
    let mut out = String::from(
        "// The grammar of Stilt for tree-sitter. Generated from reference/03-syntax.md, the \
         precedence\n// table of expressions.precedence and the lexemes of the lexical chapter \
         by\n// `just grammar-generate`; `just grammar` checks it is current.\n\n\
         module.exports = grammar({\n  name: 'stilt',\n  externals: $ => [$._line_end],\n  \
         extras: $ => [/\\s/, $.comment],\n",
    );
    let sets: Vec<String> = CONFLICTS
        .iter()
        .map(|set| {
            format!(
                "[{}]",
                set.iter()
                    .map(|r| format!("$.{r}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        })
        .collect();
    let _ = writeln!(out, "  conflicts: $ => [{}],", sets.join(", "));
    out += "  rules: {\n";
    let start = grammar
        .rules
        .first()
        .map(|(name, _)| name.clone())
        .unwrap_or_default();
    for (name, body) in &grammar.rules {
        // tree-sitter takes no rule but the start rule that matches the empty text: such a rule
        // matches the rest of its text, and is optional where it is used.
        let body = if nullable.contains(name) && *name != start {
            non_empty(body, &nullable).unwrap_or(Expr::Empty)
        } else {
            full(body, &nullable)
        };
        let js = if name == "expr" || name == "expr_h" {
            expression(&body, &grammar, &levels)?
        } else {
            js(&body)
        };
        let _ = writeln!(out, "    {name}: $ => {js},");
    }
    out += &tokens()?;
    out += "  },\n});\n";
    Ok(out)
}

/// `{` followed by an optional separator, and `}` preceded by optional `;`s: a newline before a
/// `}` is never a separator (lexical.separators).
fn around_braces(expr: &Expr) -> Expr {
    let opt = |name: &str| Expr::Opt(Box::new(Expr::Ref(name.into())));
    match expr {
        Expr::Seq(items) => Expr::Seq(
            items
                .iter()
                .flat_map(|item| match item {
                    Expr::Lit(l) if l == "{" => vec![item.clone(), opt("sep")],
                    Expr::Lit(l) if l == "}" => vec![opt("semicolons"), item.clone()],
                    other => vec![around_braces(other)],
                })
                .collect(),
        ),
        Expr::Alt(items) => Expr::Alt(items.iter().map(around_braces).collect()),
        Expr::Opt(inner) => Expr::Opt(Box::new(around_braces(inner))),
        Expr::Star(inner) => Expr::Star(Box::new(around_braces(inner))),
        other => other.clone(),
    }
}

/// The rules that match the empty text.
fn nullable(grammar: &Grammar) -> BTreeSet<String> {
    let mut found = BTreeSet::new();
    loop {
        let before = found.len();
        for (name, body) in &grammar.rules {
            if empty(body, &found) {
                found.insert(name.clone());
            }
        }
        if found.len() == before {
            return found;
        }
    }
}

fn empty(expr: &Expr, nullable: &BTreeSet<String>) -> bool {
    match expr {
        Expr::Lit(_) | Expr::Call(..) => false,
        Expr::Ref(name) => nullable.contains(name),
        Expr::Seq(items) => items.iter().all(|e| empty(e, nullable)),
        Expr::Alt(items) => items.iter().any(|e| empty(e, nullable)),
        Expr::Opt(_) | Expr::Star(_) | Expr::Empty => true,
    }
}

/// The expression, with each rule that matches the empty text made optional where it is used.
fn full(expr: &Expr, nullable: &BTreeSet<String>) -> Expr {
    let all = |items: &[Expr]| items.iter().map(|e| full(e, nullable)).collect();
    match expr {
        Expr::Ref(name) if nullable.contains(name) => Expr::Opt(Box::new(expr.clone())),
        Expr::Seq(items) => Expr::Seq(all(items)),
        Expr::Alt(items) => Expr::Alt(all(items)),
        Expr::Opt(inner) => {
            non_empty(inner, nullable).map_or(Expr::Empty, |e| Expr::Opt(Box::new(e)))
        }
        Expr::Star(inner) => {
            non_empty(inner, nullable).map_or(Expr::Empty, |e| Expr::Star(Box::new(e)))
        }
        other => other.clone(),
    }
}

/// The expression without the empty text, or nothing when it matches only the empty text.
fn non_empty(expr: &Expr, nullable: &BTreeSet<String>) -> Option<Expr> {
    match expr {
        Expr::Empty | Expr::Call(..) => None,
        Expr::Lit(_) | Expr::Ref(_) => Some(expr.clone()),
        Expr::Opt(inner) => non_empty(inner, nullable),
        Expr::Star(inner) => {
            let once = non_empty(inner, nullable)?;
            Some(Expr::Seq(vec![once.clone(), Expr::Star(Box::new(once))]))
        }
        Expr::Alt(items) => {
            let kept: Vec<Expr> = items
                .iter()
                .filter_map(|e| non_empty(e, nullable))
                .collect();
            (!kept.is_empty()).then_some(Expr::Alt(kept))
        }
        Expr::Seq(items) => {
            let (first, rest) = items.split_first()?;
            let rest_full = || full(&Expr::Seq(rest.to_vec()), nullable);
            let mut choices = Vec::new();
            if let Some(head) = non_empty(first, nullable) {
                choices.push(if rest.is_empty() {
                    head
                } else {
                    Expr::Seq(vec![head, rest_full()])
                });
            }
            if empty(first, nullable)
                && let Some(tail) = non_empty(&Expr::Seq(rest.to_vec()), nullable)
            {
                choices.push(tail);
            }
            match choices.len() {
                0 => None,
                1 => choices.pop(),
                _ => Some(Expr::Alt(choices)),
            }
        }
    }
}

/// The expression in tree-sitter's JavaScript.
fn js(expr: &Expr) -> String {
    let all = |items: &[Expr]| items.iter().map(js).collect::<Vec<_>>().join(", ");
    match expr {
        Expr::Lit(text) => format!("{text:?}"),
        Expr::Ref(name) => format!("$.{name}"),
        Expr::Seq(items) | Expr::Alt(items) if items.len() == 1 => js(&items[0]),
        Expr::Seq(items) => format!("seq({})", all(items)),
        Expr::Alt(items) => format!("choice({})", all(items)),
        Expr::Opt(inner) => format!("optional({})", js(inner)),
        Expr::Star(inner) => format!("repeat({})", js(inner)),
        Expr::Empty | Expr::Call(..) => "blank()".into(),
    }
}

/// The levels of expressions.precedence: each spelling of its rows' forms with the row's level, a
/// form that two rows hold, as `-`, with each.
fn levels(markdown: &str) -> Result<Vec<(String, u32)>, String> {
    let lines = crate::lexical::section(markdown, "expressions.precedence")
        .map_err(|_| "reference/08-expressions.md has no paragraph expressions.precedence")?;
    let mut out = Vec::new();
    for line in lines {
        let cells: Vec<&str> = line.split(" | ").collect();
        let Some(level) = cells
            .first()
            .and_then(|c| c.trim_start_matches("| ").parse().ok())
        else {
            continue;
        };
        let forms = cells.get(1).copied().unwrap_or("").replace("\\|", "|");
        for code in forms.split('`').skip(1).step_by(2) {
            out.push((code.to_owned(), level));
        }
    }
    Ok(out)
}

/// The rule `expr`, or its head, with the precedence of each of its forms: a binary operator's
/// level, the prefix operators', `else`'s, and the forms of the loosest level, whose operands
/// extend as far right as they can (expressions.open-ended-forms).
fn expression(body: &Expr, grammar: &Grammar, levels: &[(String, u32)]) -> Result<String, String> {
    let Expr::Alt(forms) = body else {
        return Err("the rule `expr` is not a choice of forms".into());
    };
    let binary = match grammar.get("binary_op") {
        Some(Expr::Alt(ops)) => ops.clone(),
        _ => return Err("the rule `binary_op` is not a choice of operators".into()),
    };
    // A level counts from the tightest, and tree-sitter's precedence from the loosest.
    let prec = |text: &str, pick: fn(u32) -> bool| {
        let found = levels
            .iter()
            .find(|(t, l)| t == text && pick(*l))
            .map(|(_, l)| *l);
        found
            .map(|l| 20 - l)
            .ok_or_else(|| format!("expressions.precedence has no level for `{text}`"))
    };
    let mut out = Vec::new();
    for form in forms {
        out.push(match form {
            Expr::Seq(items) if items.get(1) == Some(&Expr::Ref("binary_op".into())) => {
                let (left, right) = (js(&items[0]), js(&items[2]));
                let each = binary.iter().map(|op| {
                    let Expr::Lit(text) = op else {
                        return Err("an operator that is no token".to_owned());
                    };
                    Ok(format!(
                        "prec.left({}, seq({left}, {text:?}, {right}))",
                        prec(text, |l| l > 3)?
                    ))
                });
                each.collect::<Result<Vec<_>, String>>()?.join(", ")
            }
            Expr::Seq(items) if items.get(1) == Some(&Expr::Lit("else".into())) => {
                format!("prec.right({}, {})", prec("else", |_| true)?, js(form))
            }
            Expr::Seq(items) if matches!(items.first(), Some(Expr::Alt(_))) => {
                format!("prec({}, {})", prec("-", |l| l <= 3)?, js(form))
            }
            Expr::Seq(_) => format!("prec.right({}, {})", 20 - 14, js(form)),
            other => js(other),
        });
    }
    Ok(format!("choice({})", out.join(", ")))
}

/// The rules of the separators and the lexemes.
fn tokens() -> Result<String, String> {
    let regex = |rx: &lexicon::Rx| format!("/{}/", crate::lark::regex(rx));
    let lexemes = lexicon::lexemes();
    let lexeme = |name: &str| {
        lexemes
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, rx)| regex(rx))
            .ok_or_else(|| format!("no lexeme `{name}`"))
    };
    let mut out = String::new();
    out += "    sep: $ => repeat1(choice(';', $._line_end)),\n";
    out += "    semicolons: $ => repeat1(';'),\n";
    for name in [
        "lower",
        "upper",
        "int",
        "string",
        "string_head",
        "string_mid",
        "string_tail",
        "format",
    ] {
        let _ = writeln!(out, "    {name}: $ => {},", lexeme(name)?);
    }
    let _ = writeln!(
        out,
        "    float: $ => token(choice({}, seq({}, '.', {}))),",
        lexeme("float_exponent")?,
        lexeme("int")?,
        lexeme("fraction")?
    );
    let _ = writeln!(out, "    comment: $ => {},", regex(&lexicon::comment()));
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXPRESSIONS: &str = include_str!("../../../reference/08-expressions.md");

    #[test]
    fn levels_follow_the_table_of_precedence() {
        let levels = levels(EXPRESSIONS).unwrap();
        let level = |t: &str| {
            levels
                .iter()
                .filter(|(s, _)| s == t)
                .map(|(_, l)| *l)
                .collect::<Vec<_>>()
        };
        assert_eq!(level("*"), [4]);
        assert_eq!(level("-"), [3, 5]);
        assert_eq!(level("||"), [12]);
        assert_eq!(level("else"), [13]);
    }

    #[test]
    fn no_rule_matches_the_empty_text() {
        let nullable: BTreeSet<String> = ["a".to_owned()].into();
        let star = Expr::Star(Box::new(Expr::Lit("x".into())));
        let seq = Expr::Seq(vec![Expr::Ref("a".into()), star]);
        let made = non_empty(&seq, &nullable).unwrap();
        assert!(!empty(&made, &BTreeSet::new()), "{made:?}");
    }
}
