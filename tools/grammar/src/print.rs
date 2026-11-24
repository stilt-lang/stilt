//! Printing the expressions that both published forms share, and the regular expressions of the
//! lexemes, in the syntax of one of the forms.

use crate::ebnf::Expr;
use crate::lexicon::Rx;

/// How a published form writes what the two forms write differently.
pub(crate) trait Syntax {
    /// The text of a rule's name.
    fn name(&self, rule: &str) -> String;
    /// A regular expression, as the body of a token rule.
    fn rx(&self, rx: &Rx) -> String;
    /// The alternatives of a rule, one to a line.
    fn lines(&self, branches: &[String]) -> String;
}

/// The expression in the syntax of a form. `level` is 0 for the body of a rule, 1 inside a
/// sequence and 2 under a repetition.
pub(crate) fn expr(syntax: &dyn Syntax, e: &Expr, level: u8) -> String {
    match e {
        Expr::Ref(name) => syntax.name(name),
        Expr::Seq(items) => {
            let text = items
                .iter()
                .map(|i| expr(syntax, i, 1))
                .collect::<Vec<_>>()
                .join(" ");
            if level >= 2 {
                format!("({text})")
            } else {
                text
            }
        }
        Expr::Alt(items) => {
            let text = items
                .iter()
                .map(|i| expr(syntax, i, 0))
                .collect::<Vec<_>>()
                .join(" | ");
            if level >= 1 {
                format!("({text})")
            } else {
                text
            }
        }
        Expr::Opt(inner) => format!("{}?", expr(syntax, inner, 2)),
        Expr::Star(inner) => format!("{}*", expr(syntax, inner, 2)),
        Expr::Lit(_) | Expr::Call(..) | Expr::Empty => String::new(),
    }
}

/// The body of a rule, one alternative to a line.
pub(crate) fn body(syntax: &dyn Syntax, e: &Expr) -> String {
    match e {
        Expr::Alt(items) => {
            let branches: Vec<String> = items.iter().map(|i| expr(syntax, i, 0)).collect();
            syntax.lines(&branches)
        }
        other => expr(syntax, other, 0),
    }
}

/// The characters of a set, each escaped by `escape`.
/// A `-` stands last, and a `^` never first, so that neither needs an escape.
pub(crate) fn set_text(
    negated: bool,
    ranges: &[(char, char)],
    escape: fn(char) -> String,
) -> String {
    let single = |c: char| move |&(from, to): &(char, char)| from == c && to == c;
    let mut ordered: Vec<(char, char)> = ranges
        .iter()
        .copied()
        .filter(|r| !single('-')(r) && !single('^')(r))
        .collect();
    ordered.extend(ranges.iter().copied().filter(single('^')));
    ordered.extend(ranges.iter().copied().filter(single('-')));
    let inner: String = ordered
        .iter()
        .map(|&(from, to)| {
            if from == to {
                escape(from)
            } else {
                format!("{}-{}", escape(from), escape(to))
            }
        })
        .collect();
    format!("[{}{inner}]", if negated { "^" } else { "" })
}
