//! The fixes that lexical and syntax diagnostics offer (goal one-diagnostic-shape).

use rowan::{TextRange, TextSize};
use stilt_diag::{Edit, Fix};

use crate::SyntaxKind::{
    COMMA, EOF, FAT_ARROW, L_BRACK, L_CURLY, L_PAREN, R_BRACK, R_CURLY, R_PAREN, SEP,
};
use crate::grammar::is_assign_op;
use crate::stream::Sig;

fn span(start: usize, end: usize) -> TextRange {
    let at = |n: usize| TextSize::from(u32::try_from(n).expect("a source file is under 4 GiB"));
    TextRange::new(at(start), at(end))
}

/// The fix for the `{{` at `at` in a string literal, Python's and Rust's way of writing a
/// brace: each `{{` from there to the end of the literal becomes `\{` (lexical.escapes), and
/// each `}}` a `}`, which is text on its own (lexical.string-literals). Interpolations are left as
/// they are.
pub(crate) fn doubled_braces(text: &str, at: usize) -> Fix {
    let bytes = text.as_bytes();
    let mut edits = Vec::new();
    let mut depth = 0usize;
    let mut i = at;
    while i < bytes.len() && bytes[i] != b'\n' {
        match (bytes[i], bytes.get(i + 1)) {
            (b'"', _) if depth == 0 => break,
            (b'\\', _) => i += 1,
            (b'{', Some(b'{')) if depth == 0 => {
                edits.push(Edit::replace(span(i, i + 2), "\\{"));
                i += 1;
            }
            (b'}', Some(b'}')) if depth == 0 => {
                edits.push(Edit::replace(span(i, i + 2), "}"));
                i += 1;
            }
            (b'{', _) => depth += 1,
            (b'}', _) => depth = depth.saturating_sub(1),
            _ => {}
        }
        i += 1;
    }
    Fix::new("write a brace as `\\{`", edits)
}

/// The fix that deletes the span from `start` to `end`.
pub(crate) fn deletion(title: &str, start: usize, end: usize) -> Fix {
    Fix::new(title, vec![Edit::delete(span(start, end))])
}

/// The token of the `=>` whose arm's body holds the token at `at`, if the tokens between are
/// outside every bracket and on the same line.
fn arm_arrow(tokens: &[Sig], at: usize) -> Option<usize> {
    let mut depth = 0usize;
    for i in (0..at).rev() {
        match tokens[i].kind {
            R_PAREN | R_BRACK | R_CURLY => depth += 1,
            L_PAREN | L_BRACK | L_CURLY | SEP | COMMA if depth == 0 => return None,
            L_PAREN | L_BRACK | L_CURLY => depth -= 1,
            FAT_ARROW if depth == 0 => return Some(i),
            _ => {}
        }
    }
    None
}

/// The index of the token that ends the statement that holds the token at `at`: a separator or
/// a comma outside every bracket, or the bracket that closes the one it is in.
fn statement_end(tokens: &[Sig], at: usize) -> usize {
    let mut depth = 0usize;
    for (i, t) in tokens.iter().enumerate().skip(at) {
        match t.kind {
            L_PAREN | L_BRACK | L_CURLY => depth += 1,
            R_PAREN | R_BRACK | R_CURLY | SEP | COMMA | EOF if depth == 0 => return i,
            R_PAREN | R_BRACK | R_CURLY => depth -= 1,
            _ => {}
        }
    }
    tokens.len()
}

/// The fix for an assignment operator at `at` where the body of an arm ends: the assignment, a
/// statement, written as a block (patterns.match).
pub(crate) fn braced_assignment(tokens: &[Sig], at: usize) -> Option<Fix> {
    if !is_assign_op(tokens.get(at)?.kind) {
        return None;
    }
    let arrow = arm_arrow(tokens, at)?;
    let last = statement_end(tokens, at).checked_sub(1)?;
    Some(Fix::new(
        "write the arm's body as a block",
        vec![
            Edit::insert(tokens[arrow + 1].range.start(), "{ "),
            Edit::insert(tokens[last].range.end(), " }"),
        ],
    ))
}

#[cfg(test)]
mod tests {
    use stilt_diag::apply;

    use super::doubled_braces;

    #[test]
    fn writes_each_pair_of_braces_as_one_brace() {
        let text = r#""{{x}} {y} {{z}}" + "{{""#;
        assert_eq!(
            apply(text, &doubled_braces(text, 1)),
            r#""\{x} {y} \{z}" + "{{""#
        );
    }
}
