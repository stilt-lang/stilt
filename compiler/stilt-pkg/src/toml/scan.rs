//! The lexical layer of TOML 1.0: a cursor over the text, and the scalar values, strings,
//! numbers, booleans and dates, each read so that an error is placed at the first character from
//! which no TOML document can continue (packages.manifest-diagnostics, *Diagnostics*).

use super::{Error, ValueKind};

/// A position in the text, and the reading of what is there.
pub(super) struct Cursor<'a> {
    pub(super) text: &'a str,
    pub(super) pos: usize,
}

impl<'a> Cursor<'a> {
    pub(super) fn new(text: &'a str) -> Self {
        Self { text, pos: 0 }
    }

    pub(super) fn peek(&self) -> Option<char> {
        self.text[self.pos..].chars().next()
    }

    /// The character `n` characters ahead.
    pub(super) fn peek_at(&self, n: usize) -> Option<char> {
        self.text[self.pos..].chars().nth(n)
    }

    pub(super) fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.pos += c.len_utf8();
        Some(c)
    }

    pub(super) fn eat(&mut self, c: char) -> bool {
        let found = self.peek() == Some(c);
        if found {
            self.pos += c.len_utf8();
        }
        found
    }

    pub(super) fn error(&self, message: impl Into<String>) -> Error {
        Error {
            at: self.pos,
            message: message.into(),
        }
    }

    pub(super) fn expect(&mut self, c: char, what: &str) -> Result<(), Error> {
        if self.eat(c) {
            Ok(())
        } else {
            Err(self.error(format!("expected {what}")))
        }
    }

    /// Spaces and tabs.
    pub(super) fn ws(&mut self) {
        while matches!(self.peek(), Some(' ' | '\t')) {
            self.pos += 1;
        }
    }

    /// A newline, `\n` or `\r\n`, if one is here. A carriage return alone is an error.
    pub(super) fn newline(&mut self) -> Result<bool, Error> {
        match self.peek() {
            Some('\n') => {
                self.pos += 1;
                Ok(true)
            }
            Some('\r') if self.peek_at(1) == Some('\n') => {
                self.pos += 2;
                Ok(true)
            }
            Some('\r') => Err(self.error("a carriage return only goes before a newline")),
            _ => Ok(false),
        }
    }

    /// A comment, from its `#` to the end of its line, which holds no control character but a
    /// tab.
    pub(super) fn comment(&mut self) -> Result<(), Error> {
        if !self.eat('#') {
            return Ok(());
        }
        while let Some(c) = self.peek() {
            if c == '\n' || (c == '\r' && self.peek_at(1) == Some('\n')) {
                break;
            }
            if is_control(c) {
                return Err(self.error("a comment holds no control character"));
            }
            self.bump();
        }
        Ok(())
    }

    /// Reads `word` exactly, as `true`, `false`, `inf` or `nan`.
    pub(super) fn word(&mut self, word: &str) -> Result<(), Error> {
        for c in word.chars() {
            self.expect(c, &format!("`{word}`"))?;
        }
        Ok(())
    }

    /// One or more digits of `radix`, with single underscores between them.
    fn digits(&mut self, radix: u32) -> Result<String, Error> {
        let mut out = String::new();
        loop {
            match self.peek() {
                Some(c) if c.is_digit(radix) => {
                    out.push(c);
                    self.bump();
                }
                _ => return Err(self.error("expected a digit")),
            }
            while let Some(c) = self.peek().filter(|c| c.is_digit(radix)) {
                out.push(c);
                self.bump();
            }
            if !self.eat('_') {
                return Ok(out);
            }
        }
    }

    /// Exactly `n` decimal digits, as a number.
    fn fixed(&mut self, n: usize) -> Result<u32, Error> {
        let mut value = 0;
        for _ in 0..n {
            match self.peek().and_then(|c| c.to_digit(10)) {
                Some(d) => {
                    value = value * 10 + d;
                    self.bump();
                }
                None => return Err(self.error("expected a digit")),
            }
        }
        Ok(value)
    }

    /// Whether the text here starts with `n` decimal digits followed by `then`.
    fn digits_then(&self, n: usize, then: char) -> bool {
        (0..n).all(|i| self.peek_at(i).is_some_and(|c| c.is_ascii_digit()))
            && self.peek_at(n) == Some(then)
    }

    /// A number, a date or a time, which starts with a digit, a sign, `inf` or `nan`.
    pub(super) fn number(&mut self) -> Result<ValueKind, Error> {
        let start = self.pos;
        let signed = self.eat('+') || self.eat('-');
        match self.peek() {
            Some('i') => return self.word("inf").map(|()| ValueKind::Float),
            Some('n') => return self.word("nan").map(|()| ValueKind::Float),
            _ => {}
        }
        if !signed {
            if self.digits_then(4, '-') {
                return self.date_time();
            }
            if self.digits_then(2, ':') {
                return self.time(false);
            }
            if self.peek() == Some('0')
                && let Some(radix) = match self.peek_at(1) {
                    Some('x') => Some(16),
                    Some('o') => Some(8),
                    Some('b') => Some(2),
                    _ => None,
                }
            {
                self.pos += 2;
                let digits = self.digits(radix)?;
                return integer(&digits, radix, start);
            }
        }
        self.decimal(start)
    }

    /// A decimal integer or float, after its sign.
    fn decimal(&mut self, start: usize) -> Result<ValueKind, Error> {
        let whole = if self.peek() == Some('0') {
            self.bump();
            "0".to_owned()
        } else {
            self.digits(10)?
        };
        let mut float = false;
        if self.eat('.') {
            self.digits(10)?;
            float = true;
        }
        if self.eat('e') || self.eat('E') {
            let _ = self.eat('+') || self.eat('-');
            self.digits(10)?;
            float = true;
        }
        if float {
            return Ok(ValueKind::Float);
        }
        let negative = self.text[start..].starts_with('-');
        integer(
            &format!("{}{whole}", if negative { "-" } else { "" }),
            10,
            start,
        )
    }

    /// A date, with a time and an offset or without, after its first digit.
    fn date_time(&mut self) -> Result<ValueKind, Error> {
        let year = self.fixed(4)?;
        self.expect('-', "`-`")?;
        let month_at = self.pos;
        let month = self.fixed(2)?;
        self.expect('-', "`-`")?;
        let day_at = self.pos;
        let day = self.fixed(2)?;
        if !(1..=12).contains(&month) {
            return Err(Error::at(month_at, "a month runs from 01 to 12"));
        }
        if day == 0 || day > days_in(year, month) {
            return Err(Error::at(day_at, "that month has no such day"));
        }
        let timed = match self.peek() {
            Some('T' | 't') => true,
            Some(' ') => self.peek_at(1).is_some_and(|c| c.is_ascii_digit()),
            _ => false,
        };
        if timed {
            self.bump();
            return self.time(true);
        }
        Ok(ValueKind::Datetime)
    }

    /// A time, and after a date its offset if it has one.
    fn time(&mut self, after_date: bool) -> Result<ValueKind, Error> {
        self.field(2, 23)?;
        self.expect(':', "`:`")?;
        self.field(2, 59)?;
        self.expect(':', "`:`")?;
        self.field(2, 60)?;
        if self.eat('.') {
            self.fixed(1)?;
            while self.peek().is_some_and(|c| c.is_ascii_digit()) {
                self.bump();
            }
        }
        if after_date {
            match self.peek() {
                Some('Z' | 'z') => {
                    self.bump();
                }
                Some('+' | '-') => {
                    self.bump();
                    self.field(2, 23)?;
                    self.expect(':', "`:`")?;
                    self.field(2, 59)?;
                }
                _ => {}
            }
        }
        Ok(ValueKind::Datetime)
    }

    /// A field of `n` digits whose value is at most `max`.
    fn field(&mut self, n: usize, max: u32) -> Result<(), Error> {
        let at = self.pos;
        if self.fixed(n)? > max {
            return Err(Error::at(at, format!("this field is at most {max}")));
        }
        Ok(())
    }
}

/// Whether `c` is a control character that TOML allows only as a tab, a newline or in a
/// newline's carriage return.
pub(super) fn is_control(c: char) -> bool {
    matches!(c, '\u{0}'..='\u{8}' | '\u{a}'..='\u{1f}' | '\u{7f}')
}

fn integer(digits: &str, radix: u32, start: usize) -> Result<ValueKind, Error> {
    i64::from_str_radix(digits, radix)
        .map(ValueKind::Integer)
        .map_err(|_| Error::at(start, "the integer is out of the range of 64 bits"))
}

fn days_in(year: u32, month: u32) -> u32 {
    match month {
        2 if year.is_multiple_of(4) && (!year.is_multiple_of(100) || year.is_multiple_of(400)) => {
            29
        }
        2 => 28,
        4 | 6 | 9 | 11 => 30,
        _ => 31,
    }
}
