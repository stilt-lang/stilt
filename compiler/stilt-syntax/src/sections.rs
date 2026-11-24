//! A file with a syntax error, read a part at a time (errors.parts and errors.resuming): from its
//! start, and again from each line where reading resumes after a part that breaks, each time lexed
//! anew.
//!
//! A first pass parses each part alone to find where it breaks, which decides where reading
//! resumes and what each part reports. The tokens of every stretch it read then make one
//! stream, whose parts the parser reads again into the file's tree
//! ([`crate::grammar::parse_sections`]).

use rowan::{TextRange, TextSize};
use stilt_diag::Diagnostic;

use crate::SyntaxKind::*;
use crate::grammar;
use crate::lexer::{self, LexError, Lexed, Position, Token};
use crate::parser::{ParseError, Parser};
use crate::stream::{self, Sig};

/// A part of the file's stream: its tokens `from..to`, whether a separator before it parts it
/// from the one before, and whether a lexical error ends it.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Part {
    pub(crate) from: usize,
    pub(crate) to: usize,
    pub(crate) separated: bool,
    pub(crate) ended: bool,
}

/// What reading a file a part at a time found.
pub(crate) struct Reading {
    /// The lexer's tokens of every stretch, in order, which hold all of the text.
    pub(crate) lexed: Lexed,
    /// The parser's tokens of every stretch, ending with the end of the input.
    pub(crate) tokens: Vec<Sig>,
    pub(crate) parts: Vec<Part>,
    /// The first syntax error of each part that has one, and the text in which it holds back
    /// every other diagnostic.
    pub(crate) reports: Vec<(Diagnostic, TextRange)>,
    /// The comments that the Reference's lexer reads, which stops at a lexical error.
    pub(crate) comments: Vec<Token>,
}

/// The words that begin a part, but for `meta`, which begins one when `use` follows it
/// (macros.meta-use).
const WORDS: [&str; 12] = [
    "use", "impl", "pub", "extern", "fn", "type", "trait", "const", "test", "syntax", "effect",
    "macro",
];

/// The offset where each line of `text` starts.
fn line_starts(text: &str) -> Vec<usize> {
    std::iter::once(0)
        .chain(text.match_indices('\n').map(|(i, _)| i + 1))
        .collect()
}

/// The text of line `n`, 1-based, without its newline.
fn line_text<'a>(text: &'a str, lines: &[usize], n: usize) -> &'a str {
    let end = lines.get(n).map_or(text.len(), |&next| next - 1);
    &text[lines[n - 1]..end]
}

/// Whether a line starts, in its first column, with a word that begins a part, as a whole
/// word.
fn starts_part(line: &str) -> bool {
    WORDS.iter().any(|w| starts_with_word(line, w))
        || after_word(line, "meta").is_some_and(|rest| {
            let trimmed = after_blanks(rest);
            trimmed.len() < rest.len() && starts_with_word(trimmed, "use")
        })
}

/// `line` after the spaces and tabs that start it, which are the only whitespace within a line
/// (lexical.whitespace).
fn after_blanks(line: &str) -> &str {
    line.trim_start_matches([' ', '\t'])
}

/// Whether `line` starts with the word `w`, as a whole word.
fn starts_with_word(line: &str, w: &str) -> bool {
    after_word(line, w).is_some()
}

/// The rest of `line` after the word `w` it starts with, as a whole word.
fn after_word<'a>(line: &'a str, w: &str) -> Option<&'a str> {
    line.strip_prefix(w).filter(|rest| {
        !rest
            .bytes()
            .next()
            .is_some_and(|b| b.is_ascii_alphanumeric() || b == b'_')
    })
}

/// Whether `line` is a doc comment. A line that starts with another character, such as a
/// vertical tab, holds a lexical error instead, so that reading never resumes before it.
fn is_doc_line(line: &str) -> bool {
    after_blanks(line).starts_with("///")
}

/// The line where reading resumes after a part that breaks: the first line from `low` to
/// `high` that starts with a word that begins a part, or the first of the doc comments just
/// above it.
fn resumption(text: &str, lines: &[usize], low: usize, high: usize) -> Option<usize> {
    let found = (low..=high.min(lines.len())).find(|&n| starts_part(line_text(text, lines, n)))?;
    let mut first = found;
    while first > 1 && is_doc_line(line_text(text, lines, first - 1)) {
        first -= 1;
    }
    Some(first)
}

/// The 1-based line of an offset.
fn line_of(lines: &[usize], offset: TextSize) -> usize {
    lines.partition_point(|&start| start <= usize::from(offset))
}

/// Lexes the text from `offset`, which starts line `line`, with offsets into the whole text.
fn lex_from(text: &str, offset: usize, line: usize) -> Lexed {
    let start = Position {
        line: u32::try_from(line).expect("fewer than 2^32 lines"),
        col: 1,
    };
    let mut lexed = lexer::lex(&text[offset..], start);
    let shift = u32::try_from(offset).expect("source text is under 4 GiB");
    for token in &mut lexed.tokens {
        token.start += shift;
    }
    lexed.end_offset += shift;
    if let Some(error) = &mut lexed.error {
        error.range += TextSize::from(shift);
    }
    lexed
}

pub(crate) fn read(text: &str) -> Reading {
    let lines = line_starts(text);
    let mut reading = Reading {
        lexed: Lexed {
            tokens: Vec::new(),
            error: None,
            end: Position::START,
            end_offset: 0,
        },
        tokens: Vec::new(),
        parts: Vec::new(),
        reports: Vec::new(),
        comments: Vec::new(),
    };
    let mut line = Some(1);
    while let Some(n) = line {
        line = Stretch::new(text, &lines, n).read(&mut reading);
    }
    reading
}

/// The text from one line where reading starts or resumes, lexed alone.
struct Stretch<'a> {
    text: &'a str,
    lines: &'a [usize],
    lexed: Lexed,
    stop: Option<LexError>,
    tokens: Vec<Sig>,
    examples: Vec<Diagnostic>,
}

impl<'a> Stretch<'a> {
    fn new(text: &'a str, lines: &'a [usize], line: usize) -> Self {
        let offset = lines[line - 1];
        let lexed = lex_from(text, offset, line);
        let stop = lexed.error.clone();
        let mut tokens = stream::stream(text, &lexed, stop.as_ref(), true);
        if let Some(error) = &stop {
            let at = TextRange::empty(error.range.start());
            tokens.push(Sig::virtual_at(EOF, error.position, at));
        }
        let read = stop
            .as_ref()
            .map_or(lexed.tokens.len(), |e| e.tokens_before);
        let examples = lexed.tokens[..read]
            .iter()
            .filter(|t| t.kind == DOC_COMMENT)
            .filter_map(|t| crate::example_error(text, t))
            .collect();
        Self {
            text,
            lines,
            lexed,
            stop,
            tokens,
            examples,
        }
    }

    /// Reads the stretch's parts into `out`, up to the line where reading resumes, which it
    /// returns.
    fn read(self, out: &mut Reading) -> Option<usize> {
        let end = self
            .tokens
            .iter()
            .position(|t| t.kind == EOF)
            .unwrap_or(self.tokens.len());
        let cut = grammar::parts(&self.tokens, end);
        let mut p = Parser::new(&self.tokens);
        let mut parts = Vec::new();
        for (k, &(from, to)) in cut.iter().enumerate() {
            let ended = self.stop.is_some() && k + 1 == cut.len();
            let starts = |i: usize| self.tokens[i].range.start();
            let from_at = starts(from);
            let next = cut.get(k + 1).map(|&(next, _)| starts(next));
            p.limit(None);
            if k > 0 {
                p.bump(SEP);
            }
            p.limit(Some(to));
            let found = grammar::part_error(&mut p);
            let breaks = found.map(|e| e.token).map_or(ended.then_some(to), Some);
            let Some(at) = breaks else {
                self.report(out, None, from_at, next);
                parts.push((from, to, ended));
                continue;
            };
            let lexical = ended && at == to;
            let error = if lexical {
                crate::lexical_error(self.text, self.stop.as_ref().expect("a lexical error"))
            } else {
                crate::grammar_error(
                    self.text,
                    &self.lexed,
                    &self.tokens,
                    found.unwrap_or(ParseError {
                        token: at,
                        expected: None,
                    }),
                )
            };
            if let Some(resume) = self.resumption(&error, (from, to), lexical) {
                let until =
                    TextSize::from(u32::try_from(self.lines[resume - 1]).unwrap_or(u32::MAX));
                let cut = (from..to)
                    .find(|&i| self.tokens[i].position.line as usize >= resume)
                    .unwrap_or(to);
                self.report(out, Some(error), from_at, Some(until));
                parts.push((from, cut, ended && cut == to));
                self.keep(out, &parts, cut, Some(until));
                return Some(resume);
            }
            self.report(out, Some(error), from_at, next);
            parts.push((from, to, ended));
        }
        self.keep(out, &parts, end, None);
        None
    }

    /// The line where reading resumes after the part `from..to`, which breaks at `error`.
    fn resumption(
        &self,
        error: &Diagnostic,
        (from, to): (usize, usize),
        lexical: bool,
    ) -> Option<usize> {
        let first = (from..to)
            .find(|&i| !matches!(self.tokens[i].kind, DOC | MISPLACED_DOC))
            .unwrap_or(from);
        let start = self.tokens[first].position.line as usize;
        let line = line_of(self.lines, error.range.start());
        let low = (start + 1).max(if lexical { line + 1 } else { line });
        let high = if lexical {
            self.lines.len()
        } else {
            self.tokens[to - 1].position.line as usize
        };
        resumption(self.text, self.lines, low, high)
    }

    /// Reports the first syntax error of the part from `from` to `until`, the end of the file
    /// without it: `breaks`, if it breaks there, or the first error of its doc examples.
    fn report(
        &self,
        out: &mut Reading,
        breaks: Option<Diagnostic>,
        from: TextSize,
        until: Option<TextSize>,
    ) {
        let end = until.unwrap_or_else(|| TextSize::of(self.text));
        let within = |d: &&Diagnostic| from <= d.range.start() && d.range.start() < end;
        let first = breaks
            .into_iter()
            .chain(self.examples.iter().filter(within).cloned())
            .min_by_key(|d| d.range.start());
        if let Some(error) = first {
            out.reports.push((error, TextRange::new(from, end)));
        }
    }

    /// Adds the stretch's tokens before the parser's token `end`, or before the offset `until`
    /// for the lexer's, and its `parts`, to `out`.
    fn keep(
        self,
        out: &mut Reading,
        parts: &[(usize, usize, bool)],
        end: usize,
        until: Option<TextSize>,
    ) {
        let raw_base = u32::try_from(out.lexed.tokens.len()).expect("fewer than 2^32 tokens");
        let sig_base = out.tokens.len();
        let raw_end = until.map_or(self.lexed.tokens.len(), |at| {
            self.lexed
                .tokens
                .partition_point(|t| TextSize::from(t.start) < at)
        });
        let read = self
            .stop
            .as_ref()
            .map_or(raw_end, |e| e.tokens_before.min(raw_end));
        out.comments.extend(
            self.lexed.tokens[..read]
                .iter()
                .filter(|t| t.kind == COMMENT)
                .copied(),
        );
        out.lexed
            .tokens
            .extend_from_slice(&self.lexed.tokens[..raw_end]);
        let last = if until.is_none() {
            self.tokens.len()
        } else {
            end
        };
        out.tokens.extend(self.tokens[..last].iter().map(|&t| {
            let mut t = t;
            if !t.is_virtual() {
                t.start += raw_base;
                t.end += raw_base;
            }
            t
        }));
        for (k, &(from, to, ended)) in parts.iter().enumerate() {
            out.parts.push(Part {
                from: sig_base + from,
                to: sig_base + to,
                separated: k > 0,
                ended,
            });
        }
        if until.is_none() {
            out.lexed.end = self.lexed.end;
            out.lexed.end_offset = self.lexed.end_offset;
        }
    }
}
