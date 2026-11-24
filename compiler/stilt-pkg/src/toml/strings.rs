//! The four kinds of string of TOML 1.0: basic and literal, on one line or on several.

use super::Error;
use super::scan::{Cursor, is_control};

impl Cursor<'_> {
    /// A string of any kind, at its opening quote.
    pub(super) fn string(&mut self) -> Result<String, Error> {
        let quote = self.peek().expect("a string starts at its quote");
        if self.peek_at(1) == Some(quote) && self.peek_at(2) == Some(quote) {
            self.pos += 3;
            // A newline right after the opening delimiter isn't part of the string.
            let _ = self.newline()?;
            self.multi_line(quote)
        } else {
            self.pos += 1;
            self.single_line(quote)
        }
    }

    fn single_line(&mut self, quote: char) -> Result<String, Error> {
        let mut out = String::new();
        loop {
            match self.peek() {
                Some(c) if c == quote => {
                    self.bump();
                    return Ok(out);
                }
                Some('\\') if quote == '"' => {
                    self.bump();
                    out.push(self.escape()?);
                }
                Some(c) if c != '\t' && is_control(c) || c == '\r' => {
                    return Err(self.error("the string isn't closed on its line"));
                }
                Some(c) => {
                    out.push(c);
                    self.bump();
                }
                None => return Err(self.error("the string isn't closed")),
            }
        }
    }

    fn multi_line(&mut self, quote: char) -> Result<String, Error> {
        let mut out = String::new();
        loop {
            match self.peek() {
                Some(c) if c == quote => {
                    let run = self.text[self.pos..]
                        .chars()
                        .take_while(|&q| q == quote)
                        .count();
                    if run < 3 {
                        out.extend(std::iter::repeat_n(quote, run));
                        self.pos += run;
                        continue;
                    }
                    if run > 5 {
                        self.pos += 5;
                        return Err(self.error("a string ends with at most five quotes"));
                    }
                    out.extend(std::iter::repeat_n(quote, run - 3));
                    self.pos += run;
                    return Ok(out);
                }
                Some('\\') if quote == '"' => {
                    self.bump();
                    if !self.line_ending_backslash()? {
                        out.push(self.escape()?);
                    }
                }
                Some('\n' | '\r') => {
                    if self.newline()? {
                        out.push('\n');
                    }
                }
                Some(c) if c != '\t' && is_control(c) => {
                    return Err(self.error("a string holds no control character"));
                }
                Some(c) => {
                    out.push(c);
                    self.bump();
                }
                None => return Err(self.error("the string isn't closed")),
            }
        }
    }

    /// After a `\` in a multi-line basic string: spaces up to a newline, and every space and
    /// newline after it, which the string doesn't hold. Spaces followed by anything else are an
    /// error at what follows them.
    fn line_ending_backslash(&mut self) -> Result<bool, Error> {
        let start = self.pos;
        self.ws();
        if self.newline()? {
            loop {
                self.ws();
                if !self.newline()? {
                    return Ok(true);
                }
            }
        }
        if self.pos > start {
            return Err(self.error("a `\\` before spaces ends its line"));
        }
        Ok(false)
    }

    /// An escape, after its `\`.
    fn escape(&mut self) -> Result<char, Error> {
        let c = self
            .peek()
            .ok_or_else(|| self.error("the string isn't closed"))?;
        let simple = match c {
            'b' => Some('\u{8}'),
            't' => Some('\t'),
            'n' => Some('\n'),
            'f' => Some('\u{c}'),
            'r' => Some('\r'),
            '"' => Some('"'),
            '\\' => Some('\\'),
            'u' | 'U' => None,
            _ => return Err(self.error("no such escape")),
        };
        self.bump();
        if let Some(simple) = simple {
            return Ok(simple);
        }
        let digits = if c == 'u' { 4 } else { 8 };
        let mut value = 0u32;
        for i in 0..digits {
            let d = self.peek().and_then(|c| c.to_digit(16));
            let Some(d) = d else {
                return Err(self.error("expected a hexadecimal digit"));
            };
            value = value * 16 + d;
            if i + 1 == digits && char::from_u32(value).is_none() {
                return Err(self.error("the escape names no Unicode scalar value"));
            }
            self.bump();
        }
        Ok(char::from_u32(value).expect("checked above"))
    }
}
