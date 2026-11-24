//! The lexer, parser and lossless syntax tree of Stilt's `core` tier, as `reference/03-syntax.md`
//! states them. It depends on `stilt-diag` alone (`compiler/README.md`), and on no database.
//!
//! [`parse`] turns a file's text into a tree that holds all of it, comments and whitespace
//! included. A file with a syntax error is read a part at a time, and its tree is that of its
//! parts, each read alone, with the first syntax error of each part that has one (errors.parts and
//! errors.part-reports).

// Every module reads and writes syntax kinds, which are the vocabulary of the grammar, so they
// are named unqualified.
#![allow(clippy::enum_glob_use)]
#![warn(missing_docs)]

pub mod ast;
pub mod capability;
pub mod count;
mod fixes;
mod foreign;
mod foreign_forms;
mod foreign_items;
mod foreign_marks;
mod foreign_words;
pub mod format_spec;
pub mod forms;
mod grammar;
mod kind;
mod lexer;
mod parser;
mod report;
mod sections;
pub mod sexp;
mod stream;
pub mod text;
mod tree;

use rowan::GreenNode;
use stilt_diag::codes;

use crate::grammar::Entry;
use crate::lexer::{Lexed, Token};
use crate::parser::{Event, ParseError, Parser};
use crate::report::{grammar_error, lexical_error};
use crate::stream::Sig;

pub use crate::kind::{Stilt, SyntaxElement, SyntaxKind, SyntaxNode, SyntaxToken};
pub use crate::lexer::{PRIMITIVE_TYPES, is_keyword, is_module_segment, is_primitive};
pub use rowan::{TextRange, TextSize};
pub use stilt_diag::{Diagnostic, LineIndex, Position};

use SyntaxKind::*;

/// The parse of a file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Parse {
    green: GreenNode,
    errors: Vec<Diagnostic>,
    held: Vec<TextRange>,
    warnings: Vec<Diagnostic>,
    unreadable: bool,
}

impl Parse {
    /// The root of the tree.
    #[must_use]
    pub fn syntax(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.green.clone())
    }

    /// The typed root of the tree.
    #[must_use]
    pub fn tree(&self) -> ast::SourceFile {
        ast::SourceFile::root(self.syntax())
    }

    /// The file's first syntax error, if it has one.
    #[must_use]
    pub fn error(&self) -> Option<&Diagnostic> {
        self.errors.first()
    }

    /// The first syntax error of each part of the file that has one, in order
    /// (errors.part-reports).
    #[must_use]
    pub fn errors(&self) -> &[Diagnostic] {
        &self.errors
    }

    /// The text of each part with a syntax error, in which no other diagnostic is reported.
    #[must_use]
    pub fn held(&self) -> &[TextRange] {
        &self.held
    }

    /// Whether a part with a syntax error holds back a diagnostic whose primary span starts at
    /// `offset`.
    #[must_use]
    pub fn holds_back(&self, offset: TextSize) -> bool {
        self.held
            .iter()
            .any(|r| r.start() <= offset && offset < r.end())
    }

    /// Whether the file breaks lexical.source-text or lexical.nesting, and so declares nothing:
    /// every path into its module has the error type.
    #[must_use]
    pub fn unreadable(&self) -> bool {
        self.unreadable
    }

    /// The warnings about commented-out code (lexical.commented-out-code), among the comments that
    /// the lexer reads, those that a part with a syntax error holds back included.
    #[must_use]
    pub fn warnings(&self) -> &[Diagnostic] {
        &self.warnings
    }
}

/// Parses the bytes of a source file. A file that isn't UTF-8, begins with a byte-order mark or
/// holds a carriage return that doesn't come before a newline breaks lexical.source-text, and the
/// breach is its only diagnostic. Its tree is that of its text with each invalid byte replaced.
#[must_use]
pub fn parse_bytes(bytes: &[u8]) -> Parse {
    match decode(bytes) {
        Ok(text) => parse(text),
        Err(error) => unreadable(&String::from_utf8_lossy(bytes), error),
    }
}

/// The parse of a file that breaks lexical.source-text or lexical.nesting, which has no tokens and
/// declares nothing (errors.unknown-names).
fn unreadable(text: &str, error: Diagnostic) -> Parse {
    let lexed = lexer::lex(text, Position::START);
    let end = TextSize::from(lexed.end_offset);
    let tokens = [Sig::virtual_at(EOF, lexed.end, TextRange::empty(end))];
    let (events, _) = run(&tokens, Entry::Parts(false));
    Parse {
        green: tree::build(text, &lexed, &tokens, events),
        errors: vec![error],
        held: vec![TextRange::up_to(TextSize::of(text))],
        warnings: Vec::new(),
        unreadable: true,
    }
}

/// Decodes the bytes of a source file, or returns the first breach of lexical.source-text, as
/// E0001.
fn decode(bytes: &[u8]) -> Result<&str, Diagnostic> {
    match std::str::from_utf8(bytes) {
        Ok(text) => match lexer::encoding_error(text) {
            Some((offset, message)) => Err(encoding_error(text, offset, message)),
            None => Ok(text),
        },
        Err(error) => {
            let valid = std::str::from_utf8(&bytes[..error.valid_up_to()]).unwrap_or_default();
            // A breach before the invalid byte comes first. A carriage return just before it
            // comes before no newline.
            Err(match lexer::encoding_error(valid) {
                Some((offset, message)) => encoding_error(valid, offset, message),
                // The byte isn't text, so the span is the point before it.
                None => Diagnostic::new(
                    codes::E0001,
                    TextRange::empty(offset(error.valid_up_to())),
                    "the file isn't valid UTF-8",
                ),
            })
        }
    }
}

/// The breach of lexical.source-text, at the character at `at` in `text`.
fn encoding_error(text: &str, at: usize, message: &str) -> Diagnostic {
    let len = text[at..].chars().next().map_or(0, char::len_utf8);
    let d = Diagnostic::new(
        codes::E0001,
        TextRange::new(offset(at), offset(at + len)),
        message,
    );
    if at == 0 && text.starts_with('\u{FEFF}') {
        d.with_fix(fixes::deletion("delete the byte-order mark", 0, len))
    } else {
        d
    }
}

/// An offset in a source file, which is under 4 GiB.
fn offset(n: usize) -> TextSize {
    TextSize::from(u32::try_from(n).unwrap_or(u32::MAX))
}

/// Parses the text of a source file.
#[must_use]
pub fn parse(text: &str) -> Parse {
    parse_text(text, false)
}

/// Parses the bytes of a file of the standard library, which alone may declare the method
/// `await` of `std.task`'s tasks, whose name is a keyword (tasks.std-task).
#[must_use]
pub fn parse_native_bytes(bytes: &[u8]) -> Parse {
    match decode(bytes) {
        Ok(text) => parse_text(text, true),
        Err(error) => unreadable(&String::from_utf8_lossy(bytes), error),
    }
}

/// Parses the text of a source file, of the standard library if `native`.
fn parse_text(text: &str, native: bool) -> Parse {
    if let Some((at, message)) = lexer::encoding_error(text) {
        return unreadable(text, encoding_error(text, at, message));
    }
    let mut lexed = lexer::lex(text, Position::START);
    if let Some(error) = lexer::too_deep(&lexed) {
        return unreadable(text, error);
    }
    if native {
        lexer::await_declared(&mut lexed);
    }
    let tokens = stream::stream(text, &lexed, None, true);
    let (events, errors) = run(&tokens, Entry::File);
    let parse = if first_error(text, &lexed, &tokens, &errors, Entry::File).is_none() {
        let green = tree::build(text, &lexed, &tokens, events);
        debug_assert!(
            !SyntaxNode::new_root(green.clone())
                .descendants()
                .any(|node| node.kind() == ERROR),
            "a tree without syntax errors has no error nodes"
        );
        Parse {
            green,
            errors: Vec::new(),
            held: Vec::new(),
            warnings: commented_out_code(text, &lexed.tokens),
            unreadable: false,
        }
    } else {
        in_parts(text)
    };
    debug_assert_eq!(
        SyntaxNode::new_root(parse.green.clone()).text(),
        text,
        "the tree holds all the text"
    );
    parse
}

/// The parse of a file with a syntax error, read a part at a time (errors.parts).
fn in_parts(text: &str) -> Parse {
    let reading = sections::read(text);
    let mut p = Parser::new(&reading.tokens);
    grammar::parse_sections(&mut p, &reading.parts);
    let (events, _) = p.finish();
    let (errors, held) = reading.reports.into_iter().unzip();
    Parse {
        green: tree::build(text, &reading.lexed, &reading.tokens, events),
        errors,
        held,
        warnings: commented_out_code(text, &reading.comments),
        unreadable: false,
    }
}

/// Parses the expression of a doc example or a property, whose text follows its `ex:` or
/// `prop:`.
pub(crate) fn parse_example(text: &str) -> ast::Example {
    let lexed = lexer::lex(text, Position::START);
    let tokens = stream::stream(text, &lexed, None, false);
    let (events, _) = run(&tokens, Entry::Example);
    ast::Example::root(SyntaxNode::new_root(tree::build(
        text, &lexed, &tokens, events,
    )))
}

/// Parses an input of the REPL: one statement, whose tree is the only statement of a block
/// without braces, and its first syntax error (repl.inputs).
#[must_use]
pub fn parse_input(text: &str) -> Parse {
    let lexed = lexer::lex(text, Position::START);
    let tokens = stream::stream(text, &lexed, None, false);
    let (events, errors) = run(&tokens, Entry::Input);
    let error = match lexer::encoding_error(text) {
        Some((at, message)) => Some(encoding_error(text, at, message)),
        None => first_error(text, &lexed, &tokens, &errors, Entry::Input),
    };
    // An input is one statement, so its first syntax error holds back the rest of it, as a
    // part's does (errors.parts).
    let held = match error {
        Some(_) => vec![TextRange::up_to(TextSize::of(text))],
        None => Vec::new(),
    };
    Parse {
        green: tree::build(text, &lexed, &tokens, events),
        errors: error.into_iter().collect(),
        held,
        warnings: Vec::new(),
        unreadable: false,
    }
}

fn run(tokens: &[Sig], entry: Entry) -> (Vec<Event>, Vec<ParseError>) {
    let mut p = Parser::new(tokens);
    grammar::parse(&mut p, entry);
    p.finish()
}

/// The first syntax error of a text, which `lexed` lexes, `tokens` are the tokens of, and the
/// parse of which found `errors` (syntax.first-error).
///
/// - With a lexical error, the parser reads the tokens before it, as if the text ended there.
///   If it accepts all of them, the lexical error is reported.
/// - A file's doc examples are parsed on their own, and the earliest of their errors and the
///   file's own is reported.
fn first_error(
    text: &str,
    lexed: &Lexed,
    tokens: &[Sig],
    errors: &[ParseError],
    entry: Entry,
) -> Option<Diagnostic> {
    let docs = entry == Entry::File;
    let found = match &lexed.error {
        None => errors
            .first()
            .map(|&error| grammar_error(text, lexed, tokens, error)),
        Some(lexical) => {
            let prefix = stream::stream(text, lexed, Some(lexical), docs);
            let (_, errors) = run(&prefix, entry);
            Some(
                errors
                    .first()
                    .filter(|error| error.token < prefix.len())
                    .map_or_else(
                        || lexical_error(text, lexical),
                        |&error| grammar_error(text, lexed, &prefix, error),
                    ),
            )
        }
    };
    if !docs {
        return found;
    }
    // Only the comments before a lexical error are lexed by the Reference's lexer, which stops
    // there.
    let lexed_before = lexed
        .error
        .as_ref()
        .map_or(lexed.tokens.len(), |error| error.tokens_before);
    let examples = lexed.tokens[..lexed_before]
        .iter()
        .filter(|token| token.kind == DOC_COMMENT)
        .filter_map(|token| example_error(text, token));
    found
        .into_iter()
        .chain(examples)
        .min_by_key(|d| d.range.start())
}

/// The first syntax error of a doc example or a property, if the doc comment is one
/// (program.doc-examples; tests.prop-lines).
fn example_error(text: &str, comment: &Token) -> Option<Diagnostic> {
    let start = comment.start as usize;
    let body = &text[start + 3..start + comment.len as usize];
    let spaces = body.bytes().take_while(|&b| b == b' ').count();
    let (prefix, source) = ["ex:", "prop:"]
        .into_iter()
        .find_map(|prefix| Some((prefix, body[spaces..].strip_prefix(prefix)?)))?;
    let offset = u32::try_from(3 + spaces + prefix.len()).expect("a short prefix");
    let lexed = lexer::lex(
        source,
        Position {
            line: comment.position.line,
            col: comment.position.col + offset,
        },
    );
    let tokens = stream::stream(source, &lexed, None, false);
    let (_, errors) = run(&tokens, Entry::Example);
    first_error(source, &lexed, &tokens, &errors, Entry::Example)
        .map(|d| d.shifted(TextSize::from(comment.start + offset)))
}

/// lexical.commented-out-code: the `//` comments whose text parses as statements or items. Doc
/// comments and annotations aren't `//` comments in this sense.
fn commented_out_code(text: &str, tokens: &[Token]) -> Vec<Diagnostic> {
    tokens
        .iter()
        .filter(|token| token.kind == COMMENT)
        .filter_map(|comment| {
            let start = comment.start as usize;
            let body = &text[start + 2..start + comment.len as usize];
            let position = Position {
                line: comment.position.line,
                col: comment.position.col + 2,
            };
            (!body.starts_with('~') && holds_code(body, position)).then(|| {
                let end = start + comment.len as usize;
                Diagnostic::new(codes::W0001, comment.range(), "this comment holds code")
                    .with_fix(fixes::deletion("delete the comment", start, end))
            })
        })
        .collect()
}

/// Whether a comment's text holds code. Text that is a single token is exempt, perhaps after a
/// leading `-` or inside one pair of parentheses, in either order
/// (lexical.commented-out-code.single-token), and so is `()`. A string literal counts as one token,
/// even when it interpolates, and a written `;` counts as a token.
fn holds_code(body: &str, start: Position) -> bool {
    let lexed = lexer::lex(body, start);
    if lexed.error.is_some() {
        return false;
    }
    let written = lexed.tokens.iter().filter(|t| !t.kind.is_trivia()).count();
    let semicolons = lexed.tokens.iter().filter(|t| t.kind == SEMICOLON).count();
    let tokens = stream::stream(body, &lexed, None, false);
    let code: Vec<SyntaxKind> = tokens
        .iter()
        .map(|t| t.kind)
        .filter(|&kind| !matches!(kind, SEP | EOF))
        .collect();
    let exempt = written <= 1
        || (semicolons == 0
            && match bare(&code) {
                [] | [_] => true,
                kinds => one_string(kinds),
            });
    !exempt && run(&tokens, Entry::Code).1.is_empty()
}

fn without_signs(kinds: &[SyntaxKind]) -> &[SyntaxKind] {
    let signs = kinds.iter().take_while(|&&kind| kind == MINUS).count();
    &kinds[signs..]
}

/// The tokens without leading `-` signs, and without one pair of parentheses around them and
/// the signs inside it.
fn bare(kinds: &[SyntaxKind]) -> &[SyntaxKind] {
    let signed = without_signs(kinds);
    if signed.first() == Some(&L_PAREN) && kinds.last() == Some(&R_PAREN) {
        without_signs(&signed[1..signed.len() - 1])
    } else {
        signed
    }
}

/// Whether the tokens make one string literal: the interpolations that the first token opens
/// close only at the last.
fn one_string(kinds: &[SyntaxKind]) -> bool {
    if kinds.first() != Some(&STRING_HEAD) {
        return false;
    }
    let mut depth = 0_usize;
    for (i, &kind) in kinds.iter().enumerate() {
        let last = i + 1 == kinds.len();
        match kind {
            STRING_TAIL if last => return depth == 1,
            _ if last => return false,
            STRING_HEAD => depth += 1,
            STRING_TAIL if depth > 1 => depth -= 1,
            STRING_TAIL => return false,
            _ if depth == 0 => return false,
            _ => {}
        }
    }
    false
}

#[cfg(test)]
mod tests;
