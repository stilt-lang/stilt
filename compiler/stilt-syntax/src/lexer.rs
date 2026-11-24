//! The lexer. Rule numbers in comments refer to the Reference's lexical chapter.
//!
//! The lexer turns text into tokens, trivia included, so that the tree holds all of the text. It
//! records the first lexical error, which is the one errors.invalid-source-text reports, and goes
//! on lexing after it, so that the tree also holds the code after the error.

pub(crate) mod lexicon;
mod nesting;
mod numbers;
mod punctuation;
mod strings;
mod words;

use rowan::{TextRange, TextSize};
use stilt_diag::{Code, codes};

use crate::SyntaxKind::{self, *};

pub(crate) use self::nesting::too_deep;
pub(crate) use stilt_diag::Position;

pub use self::words::{PRIMITIVE_TYPES, is_keyword, is_module_segment, is_primitive};
pub(crate) use self::words::{contextual_keyword, foreign_declaration, is_limit};

/// A token, trivia included.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Token {
    pub(crate) kind: SyntaxKind,
    /// The byte offset of the token's start.
    pub(crate) start: u32,
    /// The length of the token in bytes.
    pub(crate) len: u32,
    /// The position of the token's start.
    pub(crate) position: Position,
}

impl Token {
    /// The token's text.
    pub(crate) fn range(&self) -> TextRange {
        TextRange::at(TextSize::from(self.start), TextSize::from(self.len))
    }
}

/// A lexical error.
#[derive(Clone, Debug)]
pub(crate) struct LexError {
    pub(crate) code: Code,
    /// Where the error is reported.
    pub(crate) position: Position,
    /// The text in error, which starts at `position`.
    pub(crate) range: TextRange,
    pub(crate) message: String,
    /// How many tokens the lexer had made when it found the error. They are the tokens that
    /// the Reference's lexer, which stops at the error, would have made.
    pub(crate) tokens_before: usize,
}

/// The result of lexing a text.
#[derive(Debug)]
pub(crate) struct Lexed {
    pub(crate) tokens: Vec<Token>,
    /// The first lexical error.
    pub(crate) error: Option<LexError>,
    /// The position just after the last token that isn't trivia, which is where the end of the
    /// text sits (lexical.terminator-positions).
    pub(crate) end: Position,
    /// The offset of `end`.
    pub(crate) end_offset: u32,
}

/// A place in the text being lexed: an offset and its position.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Mark {
    pub(crate) offset: usize,
    pub(crate) position: Position,
}

/// Lexes `text`, whose first character is at `start`. Text lexed on its own, such as a doc
/// example, starts where it sits in its file.
/// Reads `await` after `fn` as a name, which only the standard library's method of
/// `std.task`'s tasks declares, though the word stays a keyword (tasks.std-task).
pub(crate) fn await_declared(lexed: &mut Lexed) {
    let mut after_fn = false;
    for token in &mut lexed.tokens {
        if token.kind.is_trivia() {
            continue;
        }
        if after_fn && token.kind == AWAIT_KW {
            token.kind = LOWER_IDENT;
        }
        after_fn = token.kind == FN_KW;
    }
}

pub(crate) fn lex(text: &str, start: Position) -> Lexed {
    let mut lexer = Lexer {
        text,
        bytes: text.as_bytes(),
        pos: 0,
        here: start,
        token_start: 0,
        token_position: start,
        tokens: Vec::new(),
        error: None,
        interpolations: Vec::new(),
        dot_end: None,
        end: Mark {
            offset: 0,
            position: start,
        },
    };
    lexer.run();
    Lexed {
        tokens: lexer.tokens,
        error: lexer.error,
        end: lexer.end.position,
        end_offset: to_u32(lexer.end.offset),
    }
}

/// The first breach of lexical.source-text in a text, which is already UTF-8: a byte-order mark, or
/// a carriage return that doesn't come before a newline.
pub(crate) fn encoding_error(text: &str) -> Option<(usize, &'static str)> {
    if text.starts_with('\u{FEFF}') {
        return Some((0, "a source file can't begin with a byte-order mark"));
    }
    let bytes = text.as_bytes();
    let offset =
        (0..bytes.len()).find(|&i| bytes[i] == b'\r' && bytes.get(i + 1) != Some(&b'\n'))?;
    Some((offset, "a carriage return must be followed by a newline"))
}

/// Converts a count to `u32`. Texts over 4 GiB aren't supported.
fn to_u32(n: usize) -> u32 {
    u32::try_from(n).expect("source text is under 4 GiB")
}

fn is_continuation(byte: u8) -> bool {
    byte & 0xC0 == 0x80
}

fn is_ident_char(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

fn is_digit(base: u32, byte: u8) -> bool {
    char::from(byte).is_digit(base)
}

/// An interpolation being lexed (lexical.nested-interpolation).
#[derive(Clone, Copy, Debug)]
struct Interpolation {
    /// Brackets opened inside it and not yet closed.
    depth: u32,
    /// The opening quote of its string, where an error that leaves it open is reported.
    quote: Mark,
}

struct Lexer<'a> {
    text: &'a str,
    bytes: &'a [u8],
    pos: usize,
    /// The position of the byte at `pos`.
    here: Position,
    token_start: usize,
    token_position: Position,
    tokens: Vec<Token>,
    error: Option<LexError>,
    /// The interpolations open at `pos`, innermost last.
    interpolations: Vec<Interpolation>,
    /// The byte offset just after the latest `.` token.
    dot_end: Option<usize>,
    /// Just after the latest token that isn't trivia.
    end: Mark,
}

impl Lexer<'_> {
    /// The byte `k` places ahead, or NUL past the end. Callers that must tell a NUL in the text
    /// from the end compare `pos` with the length.
    fn peek(&self, k: usize) -> u8 {
        self.bytes.get(self.pos + k).copied().unwrap_or(0)
    }

    fn at_end(&self) -> bool {
        self.pos >= self.bytes.len()
    }

    fn at_newline(&self) -> bool {
        self.peek(0) == b'\n' || (self.peek(0) == b'\r' && self.peek(1) == b'\n')
    }

    /// Moves past `n` bytes on the current line.
    fn advance(&mut self, n: usize) {
        for &byte in &self.bytes[self.pos..self.pos + n] {
            if !is_continuation(byte) {
                self.here.col += 1;
            }
        }
        self.pos += n;
    }

    /// Moves past one character on the current line.
    fn advance_char(&mut self) {
        let len = self.text[self.pos..]
            .chars()
            .next()
            .map_or(1, char::len_utf8);
        self.advance(len);
    }

    /// The place under the cursor.
    fn mark(&self) -> Mark {
        Mark {
            offset: self.pos,
            position: self.here,
        }
    }

    /// The start of the token begun last.
    fn token_mark(&self) -> Mark {
        Mark {
            offset: self.token_start,
            position: self.token_position,
        }
    }

    fn begin(&mut self) {
        self.token_start = self.pos;
        self.token_position = self.here;
    }

    /// Ends the token begun last, at `pos`.
    fn emit(&mut self, kind: SyntaxKind) {
        self.tokens.push(Token {
            kind,
            start: to_u32(self.token_start),
            len: to_u32(self.pos - self.token_start),
            position: self.token_position,
        });
        if !kind.is_trivia() {
            self.end = self.mark();
        }
    }

    /// Records a lexical error at `at`, unless an earlier one is recorded. The text in error runs
    /// from `at` to the cursor, and holds at least the character at `at`.
    fn fail(&mut self, code: Code, at: Mark, message: impl Into<String>) {
        if self.error.is_none() {
            let char_end = at.offset
                + self.text[at.offset..]
                    .chars()
                    .next()
                    .map_or(0, char::len_utf8);
            let end = self.pos.max(char_end);
            self.error = Some(LexError {
                code,
                position: at.position,
                range: TextRange::new(
                    TextSize::from(to_u32(at.offset)),
                    TextSize::from(to_u32(end)),
                ),
                message: message.into(),
                tokens_before: self.tokens.len(),
            });
        }
    }

    /// Records that a string literal, or an interpolation in one, runs past the end of its
    /// line, and closes every interpolation open.
    fn unterminated(&mut self, quote: Mark) {
        self.fail(codes::E0005, quote, "unterminated string literal");
        self.interpolations.clear();
    }

    fn run(&mut self) {
        while !self.at_end() {
            let innermost = self.interpolations.last().copied();
            let at_interpolation_level = innermost.is_some_and(|inner| inner.depth == 0);
            match self.peek(0) {
                b' ' | b'\t' => self.whitespace(),
                b'\n' => self.newline(1),
                b'\r' if self.peek(1) == b'\n' => self.newline(2),
                b'/' if self.peek(1) == b'/' => self.comment(),
                b'a'..=b'z' | b'A'..=b'Z' | b'_' => self.word(),
                b'0'..=b'9' => self.number(),
                b'"' => self.string(),
                b':' if at_interpolation_level => self.format(),
                b'}' if at_interpolation_level => self.close_interpolation(),
                _ => self.punctuation(),
            }
        }
        if let Some(inner) = self.interpolations.last().copied() {
            self.unterminated(inner.quote);
        }
    }

    fn whitespace(&mut self) {
        self.begin();
        while matches!(self.peek(0), b' ' | b'\t') {
            self.advance(1);
        }
        self.emit(WHITESPACE);
    }

    /// A newline of `len` bytes. An interpolation can't span lines (lexical.string-literals).
    fn newline(&mut self, len: usize) {
        if let Some(inner) = self.interpolations.last().copied() {
            self.unterminated(inner.quote);
        }
        self.begin();
        self.pos += len;
        self.emit(NEWLINE);
        self.here = Position {
            line: self.here.line + 1,
            col: 1,
        };
    }

    /// lexical.line-comments, lexical.doc-comments and lexical.annotations: a comment, which runs
    /// to the end of its line.
    fn comment(&mut self) {
        self.begin();
        let doc = self.peek(2) == b'/';
        let rest = &self.bytes[self.pos..];
        let mut len = rest.iter().position(|&b| b == b'\n').unwrap_or(rest.len());
        if len > 0 && rest[len - 1] == b'\r' {
            len -= 1;
        }
        self.advance(len);
        self.emit(if doc { DOC_COMMENT } else { COMMENT });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(text: &str) -> Vec<SyntaxKind> {
        lex(text, Position::START)
            .tokens
            .iter()
            .map(|t| t.kind)
            .filter(|k| !k.is_trivia())
            .collect()
    }

    fn error(text: &str) -> (&'static str, u32, u32) {
        let e = lex(text, Position::START)
            .error
            .expect("the text has a lexical error");
        (e.code.as_str(), e.position.line, e.position.col)
    }

    #[test]
    fn digits_after_a_dot_are_an_integer() {
        assert_eq!(kinds("t.0.1"), [LOWER_IDENT, DOT, INT, DOT, INT]);
        assert_eq!(kinds("0..n"), [INT, DOT2, LOWER_IDENT]);
        assert_eq!(kinds("1.5e3"), [FLOAT]);
        assert_eq!(error("t.1e3"), ("E0004", 1, 4));
    }

    #[test]
    fn malformed_numbers() {
        assert_eq!(error("1__0"), ("E0004", 1, 2));
        assert_eq!(error("007"), ("E0004", 1, 1));
        assert_eq!(error("0x"), ("E0004", 1, 3));
        assert_eq!(error("10u8"), ("E0004", 1, 3));
        assert_eq!(error("1e1_0"), ("E0004", 1, 4));
    }

    #[test]
    fn interpolations_nest() {
        assert_eq!(
            kinds(r#""a{f("b{x:>4}")}c""#),
            [
                STRING_HEAD,
                LOWER_IDENT,
                L_PAREN,
                STRING_HEAD,
                LOWER_IDENT,
                FORMAT,
                STRING_TAIL,
                R_PAREN,
                STRING_TAIL
            ]
        );
    }

    #[test]
    fn string_errors() {
        assert_eq!(error("x = \"abc"), ("E0005", 1, 5));
        assert_eq!(error("\"a{x\n}\""), ("E0005", 1, 1));
        assert_eq!(error(r#""a\q""#), ("E0006", 1, 3));
        assert_eq!(error(r#""{{""#), ("E0006", 1, 2));
        assert_eq!(error(r#""{x:05}""#), ("E0007", 1, 4));
    }

    /// lexical.keywords and lexical.reserved-words reserve only the words of the language and of
    /// its later tiers.
    #[test]
    fn reserved_words() {
        assert_eq!(
            kinds("when comptime extern unsafe"),
            [WHEN_KW, COMPTIME_KW, EXTERN_KW, UNSAFE_KW]
        );
        assert_eq!(kinds("as dyn move mut ref static"), [LOWER_IDENT; 6]);
    }

    #[test]
    fn columns_count_characters() {
        assert_eq!(error("\"é\" ¤"), ("E0002", 1, 5));
    }

    #[test]
    fn the_end_follows_the_last_token() {
        let lexed = lex("a // c\n", Position::START);
        assert_eq!(lexed.end, Position { line: 1, col: 2 });
        assert_eq!(lexed.end_offset, 1);
    }

    #[test]
    fn encoding() {
        assert_eq!(encoding_error("a\rb").map(|(offset, _)| offset), Some(1));
        assert_eq!(encoding_error("a\r\nb"), None);
    }
}
