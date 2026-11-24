//! Operators and punctuation (lexical.tokens).

use stilt_diag::codes;

use super::Lexer;
use super::lexicon::PUNCTUATION;
use crate::SyntaxKind::*;

/// Whether `rest` begins with `text`, of at most three bytes, compared byte by byte from the
/// first, which tells most tokens apart, since the lexer asks it of every operator.
fn begins(rest: &[u8], text: &str) -> bool {
    let text = text.as_bytes();
    rest.len() >= text.len() && text.iter().zip(rest).all(|(a, b)| a == b)
}

impl Lexer<'_> {
    /// lexical.tokens: an operator or punctuation token, by maximal munch.
    pub(super) fn punctuation(&mut self) {
        self.begin();
        let rest = &self.bytes[self.pos..];
        let Some(&(text, kind)) = PUNCTUATION.iter().find(|(text, _)| begins(rest, text)) else {
            let c = self.text[self.pos..]
                .chars()
                .next()
                .expect("the lexer stops at the end");
            let message = match c {
                '`' => "unexpected backtick".to_owned(),
                ' '..='~' => format!("unexpected character `{c}`"),
                _ => format!("unexpected character U+{:04X}", u32::from(c)),
            };
            self.fail(codes::E0002, self.mark(), message);
            self.advance_char();
            self.emit(ERROR);
            return;
        };
        self.advance(text.len());
        if let Some(inner) = self.interpolations.last_mut() {
            match kind {
                L_PAREN | L_BRACK | L_CURLY => inner.depth += 1,
                R_PAREN | R_BRACK | R_CURLY if inner.depth > 0 => inner.depth -= 1,
                _ => {}
            }
        }
        if kind == DOT {
            self.dot_end = Some(self.pos);
        }
        self.emit(kind);
    }
}
