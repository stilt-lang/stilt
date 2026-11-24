//! String literals, with their interpolations and their format specs (lexical.string-literals,
//! lexical.interpolation and lexical.format-specs).

use stilt_diag::codes;

use super::{Interpolation, Lexer, Mark, is_digit};
use crate::SyntaxKind::*;
use crate::format_spec;

impl Lexer<'_> {
    /// lexical.string-literals: a string literal, from its opening quote.
    pub(super) fn string(&mut self) {
        self.begin();
        let quote = self.mark();
        self.advance(1);
        self.string_text(true, quote);
    }

    /// lexical.string-literals: the text of a string literal up to its closing quote or its next
    /// interpolation. The token began at the opening quote when `first`, and at the `}` that closed
    /// an interpolation otherwise.
    fn string_text(&mut self, first: bool, quote: Mark) {
        loop {
            if self.at_end() || self.at_newline() {
                self.unterminated(quote);
                self.emit(ERROR);
                return;
            }
            match self.peek(0) {
                b'"' => {
                    self.advance(1);
                    self.emit(if first { STRING } else { STRING_TAIL });
                    return;
                }
                b'{' if self.peek(1) == b'{' => {
                    // lexical.escapes. The pair reads as text, to go on lexing.
                    self.fail(
                        codes::E0006,
                        self.mark(),
                        "a brace is written `\\{`, not `{{`",
                    );
                    self.advance(2);
                }
                b'{' => {
                    self.advance(1);
                    self.emit(if first { STRING_HEAD } else { STRING_MID });
                    self.interpolations.push(Interpolation { depth: 0, quote });
                    return;
                }
                b'\\' => self.escape(),
                _ => self.advance_char(),
            }
        }
    }

    /// lexical.escapes: one escape, from its backslash.
    fn escape(&mut self) {
        let start = self.mark();
        match self.peek(1) {
            b'n' | b't' | b'r' | b'0' | b'\\' | b'"' | b'{' => self.advance(2),
            b'u' if self.peek(2) == b'{' => {
                self.advance(3);
                let hex_start = self.pos;
                while is_digit(16, self.peek(0)) {
                    self.advance(1);
                }
                let count = self.pos - hex_start;
                if self.peek(0) != b'}' || !(1..=6).contains(&count) {
                    self.fail(
                        codes::E0006,
                        start,
                        "`\\u{…}` takes 1 to 6 hexadecimal digits",
                    );
                    return;
                }
                let value = u32::from_str_radix(&self.text[hex_start..self.pos], 16)
                    .expect("at most six hexadecimal digits");
                if char::from_u32(value).is_none() {
                    self.fail(
                        codes::E0006,
                        start,
                        "`\\u{…}` must name a Unicode scalar value",
                    );
                }
                self.advance(1);
            }
            _ => {
                self.fail(codes::E0006, start, "invalid escape");
                self.advance(1);
            }
        }
    }

    /// Ends the innermost interpolation at the `}` under the cursor, and goes on with the rest
    /// of its string.
    pub(super) fn close_interpolation(&mut self) {
        self.begin();
        let inner = self
            .interpolations
            .pop()
            .expect("an interpolation is open at its closing brace");
        self.advance(1);
        self.string_text(false, inner.quote);
    }

    /// lexical.format-specs: the format spec of the innermost interpolation, from the `:` under the
    /// cursor to the `}` that ends the interpolation.
    pub(super) fn format(&mut self) {
        self.begin();
        let colon = self.mark();
        let quote = self
            .interpolations
            .last()
            .expect("a format spec is inside an interpolation")
            .quote;
        self.advance(1);
        let spec_start = self.pos;
        while !self.at_end() && self.peek(0) != b'}' && !self.at_newline() {
            self.advance_char();
        }
        if self.peek(0) != b'}' {
            self.unterminated(quote);
            self.emit(ERROR);
            return;
        }
        let spec = &self.text[spec_start..self.pos];
        if format_spec::parse(spec).is_none() {
            let message = format!("`{spec}` is not a format spec");
            self.fail(codes::E0007, colon, message);
        }
        self.emit(FORMAT);
        self.close_interpolation();
    }
}
