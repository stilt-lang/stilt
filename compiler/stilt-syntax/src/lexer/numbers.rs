//! Number literals (lexical.integer-literals, lexical.float-literals and lexical.digits-after-dot).

use stilt_diag::codes;

use super::{Lexer, Mark, is_digit, is_ident_char};
use crate::SyntaxKind::*;

impl Lexer<'_> {
    /// lexical.integer-literals, lexical.float-literals and lexical.digits-after-dot: a number
    /// literal. A literal that directly follows a `.` token is a decimal integer.
    pub(super) fn number(&mut self) {
        let after_dot = self.dot_end == Some(self.pos);
        self.begin();
        let result = self.number_body(after_dot).and_then(|is_float| {
            if is_ident_char(self.peek(0)) {
                Err((
                    self.mark(),
                    "a number literal can't be followed directly by a letter, a digit or `_`",
                ))
            } else {
                Ok(is_float)
            }
        });
        match result {
            Ok(is_float) => self.emit(if is_float { FLOAT } else { INT }),
            Err((position, message)) => {
                self.fail(codes::E0004, position, message);
                while is_ident_char(self.peek(0)) {
                    self.advance(1);
                }
                self.emit(ERROR);
            }
        }
    }

    /// The literal from the cursor, telling whether it is a float, or where it breaks its
    /// grammar and how.
    fn number_body(&mut self, after_dot: bool) -> Result<bool, (Mark, &'static str)> {
        if after_dot {
            self.no_leading_zero()?;
            self.digits(10)?;
            return Ok(false);
        }
        let base = match (self.peek(0), self.peek(1)) {
            (b'0', b'x') => Some(16),
            (b'0', b'o') => Some(8),
            (b'0', b'b') => Some(2),
            _ => None,
        };
        if let Some(base) = base {
            self.advance(2);
            if !is_digit(base, self.peek(0)) {
                return Err((self.mark(), "a base prefix must be followed by a digit"));
            }
            self.digits(base)?;
            return Ok(false);
        }
        self.no_leading_zero()?;
        self.digits(10)?;
        let fraction = self.peek(0) == b'.' && is_digit(10, self.peek(1));
        if fraction {
            self.advance(1);
            self.digits(10)?;
        }
        let sign = usize::from(matches!(self.peek(1), b'+' | b'-'));
        let exponent = matches!(self.peek(0), b'e' | b'E') && is_digit(10, self.peek(1 + sign));
        if exponent {
            self.advance(1 + sign);
            while is_digit(10, self.peek(0)) {
                self.advance(1);
            }
        }
        Ok(fraction || exponent)
    }

    fn no_leading_zero(&self) -> Result<(), (Mark, &'static str)> {
        if self.peek(0) == b'0' && (is_digit(10, self.peek(1)) || self.peek(1) == b'_') {
            Err((self.mark(), "a decimal literal can't have a leading zero"))
        } else {
            Ok(())
        }
    }

    /// lexical.integer-literals: a run of digits in `base`, with `_` only between two digits. The
    /// cursor is on a digit.
    fn digits(&mut self, base: u32) -> Result<(), (Mark, &'static str)> {
        loop {
            if is_digit(base, self.peek(0)) {
                self.advance(1);
            } else if self.peek(0) == b'_' {
                if !is_digit(base, self.peek(1)) {
                    return Err((self.mark(), "`_` must sit between two digits"));
                }
                self.advance(1);
            } else {
                return Ok(());
            }
        }
    }
}
