//! The tokens of a body as docs.body-size counts them.

use crate::SyntaxKind::*;
use crate::lexer;
use stilt_diag::Position;

/// How many tokens `text`, the source of a body, holds as lexical.tokens lexes them: without
/// comments and without separators, written `;` or inserted, a string literal counting as one token
/// even when it interpolates, as lexical.commented-out-code and
/// lexical.commented-out-code.single-token counts a comment's tokens (docs.body-size). A text with
/// a lexical error counts the tokens before the error.
#[must_use]
pub fn tokens(text: &str) -> usize {
    let lexed = lexer::lex(text, Position { line: 1, col: 1 });
    let mut count = 0;
    // How deep the tokens are inside the interpolations of a string literal.
    let mut depth = 0_usize;
    for token in &lexed.tokens {
        match token.kind {
            kind if kind.is_trivia() || kind == SEMICOLON => {}
            STRING_HEAD => {
                count += usize::from(depth == 0);
                depth += 1;
            }
            STRING_TAIL => depth = depth.saturating_sub(1),
            _ => count += usize::from(depth == 0),
        }
    }
    count
}

#[cfg(test)]
mod tests {
    use super::tokens;

    #[test]
    fn counts_written_tokens() {
        assert_eq!(tokens("{ x }"), 3);
        assert_eq!(tokens("{ o.qty * 2 + o.extra }"), 11);
        assert_eq!(tokens("{\n  let a = 1; // one\n  a\n}"), 7);
        assert_eq!(tokens("{ \"{o.name}: {o.qty:>4}\" }"), 3);
        assert_eq!(tokens("{ let xs: List<List<i64>> = [] }"), 14);
    }
}
