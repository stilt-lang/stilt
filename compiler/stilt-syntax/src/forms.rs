//! Forms read from tokens that no file holds in that order: the fragments a macro's use passes, and
//! the expansions it makes (macros.checked-templates and macros.expansion). The tokens are laid out
//! one after the other, a space between each two, and parsed as one form, as the grammar reads it
//! in a file.

use rowan::{GreenNode, TextRange, TextSize};

use crate::SyntaxKind::{self, *};
use crate::lexer::{Lexed, Position, Token, contextual_keyword, foreign_declaration};
use crate::parser::Parser;
use crate::stream::Sig;
use crate::{SyntaxNode, grammar, tree};

/// A token to parse: its kind, as the parser reads it, and its text. A separator is `SEP`, its
/// text `;`.
#[derive(Clone, Copy, Debug)]
pub struct Piece<'a> {
    /// The token's kind.
    pub kind: SyntaxKind,
    /// The token's text.
    pub text: &'a str,
}

/// The forms of a macro's fragments and templates.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Form {
    /// An expression.
    Expr,
    /// A pattern.
    Pattern,
    /// A type.
    Type,
    /// A block's statements.
    Block,
}

/// The parse of tokens as a form. It holds the tree's green nodes, which threads share, so that
/// a query keeps the parse of a macro's expansion with the expansion (reference/rationale/16-meta.md).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FormParse {
    /// The tree, whose root holds the form's node and every token after it.
    green: GreenNode,
    /// Where each token starts in the tree's text.
    pub starts: Vec<TextSize>,
    /// How many tokens the form takes, from the first.
    pub taken: usize,
    /// The index of the token at which the parser found a syntax error, if it did.
    pub error: Option<usize>,
}

impl FormParse {
    /// The form's node, or `None` when the parser read none.
    #[must_use]
    pub fn node(&self) -> Option<SyntaxNode> {
        SyntaxNode::new_root(self.green.clone()).children().next()
    }

    /// Whether the form takes every token, with no syntax error.
    #[must_use]
    pub fn is_whole(&self, len: usize) -> bool {
        self.error.is_none() && self.taken == len && self.node().is_some()
    }
}

/// Parses the longest form of `form` that the tokens start with.
#[must_use]
pub fn parse_form(pieces: &[Piece<'_>], form: Form) -> FormParse {
    let (text, lexed, starts) = laid_out(pieces);
    let mut sigs: Vec<Sig> = pieces
        .iter()
        .enumerate()
        .map(|(i, piece)| (i, piece, lexed.tokens[i * 2]))
        .map(|(i, piece, raw)| Sig {
            kind: piece.kind,
            start: index(i * 2),
            end: index(i * 2 + 1),
            position: raw.position,
            range: raw.range(),
            contextual: (piece.kind == LOWER_IDENT)
                .then(|| contextual_keyword(piece.text))
                .flatten(),
            foreign: (piece.kind == LOWER_IDENT)
                .then(|| foreign_declaration(piece.text))
                .flatten(),
        })
        .collect();
    let end = TextSize::of(text.as_str());
    let mut eof = Sig::virtual_at(EOF, lexed.end, TextRange::empty(end));
    eof.start = index(lexed.tokens.len());
    eof.end = eof.start;
    sigs.push(eof);
    let mut p = Parser::new(&sigs);
    let start = p.checkpoint();
    let root = p.start();
    grammar::form(&mut p, form);
    let taken = p.pos().min(pieces.len());
    let error = p.error_since(start);
    while !p.at(EOF) {
        p.bump_any();
    }
    root.complete(&mut p, EXAMPLE);
    let (events, _) = p.finish();
    FormParse {
        green: tree::build(&text, &lexed, &sigs, events),
        starts,
        taken,
        error,
    }
}

fn index(i: usize) -> u32 {
    u32::try_from(i).expect("fewer than 2^32 tokens")
}

/// The text of the tokens, a space after each but the last, their lexed tokens, and where each
/// starts.
fn laid_out(pieces: &[Piece<'_>]) -> (String, Lexed, Vec<TextSize>) {
    let mut text = String::new();
    let mut tokens = Vec::with_capacity(pieces.len() * 2);
    let mut starts = Vec::with_capacity(pieces.len());
    for piece in pieces {
        if !text.is_empty() {
            push(&mut text, &mut tokens, WHITESPACE, " ");
        }
        starts.push(TextSize::of(text.as_str()));
        let raw = if piece.kind == SEP {
            SEMICOLON
        } else {
            piece.kind
        };
        push(&mut text, &mut tokens, raw, piece.text);
    }
    // Every token but the first has a space before it, so token `i` is the lexer's `2i`.
    let end = u32::try_from(text.len()).expect("under 4 GiB");
    let lexed = Lexed {
        tokens,
        error: None,
        end: Position {
            line: 1,
            col: end + 1,
        },
        end_offset: end,
    };
    (text, lexed, starts)
}

fn push(text: &mut String, tokens: &mut Vec<Token>, kind: SyntaxKind, spelled: &str) {
    let start = u32::try_from(text.len()).expect("under 4 GiB");
    tokens.push(Token {
        kind,
        start,
        len: u32::try_from(spelled.len()).expect("under 4 GiB"),
        position: Position {
            line: 1,
            col: start + 1,
        },
    });
    text.push_str(spelled);
}

/// The tokens that the parser reads in `text`, as a file's, without the end of the input, each
/// with its kind, a separator, a newline's or a `;`, being `SEP`, and its span in `text`, a
/// separator's being empty, at the end of the token it follows: the tokens of a quote's
/// contents (macros.quote), read again from their text. `None` when the text has a lexical
/// error.
#[must_use]
pub fn read_tokens(text: &str) -> Option<Vec<(SyntaxKind, TextRange)>> {
    let lexed = crate::lexer::lex(text, Position::START);
    if lexed.error.is_some() {
        return None;
    }
    let sigs = crate::stream::stream(text, &lexed, None, false);
    Some(
        sigs.iter()
            .filter(|s| s.kind != EOF)
            .map(|s| {
                let range = if s.kind == SEP {
                    TextRange::empty(s.range.end())
                } else {
                    s.range
                };
                (s.kind, range)
            })
            .collect(),
    )
}

/// A token of a text that a macro lexes (macros.tokens-and-code): its kind as the parser reads it,
/// a separator being `SEP`, its span in the text, and whether a newline inserted it, which gives it
/// an empty span at the end of the token it follows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TextToken {
    /// The token's kind.
    pub kind: SyntaxKind,
    /// Its span in the text.
    pub range: TextRange,
    /// Whether a newline inserted it.
    pub inserted: bool,
}

/// The tokens of `text` as lexical.tokens lexes them, as a file's, without the end of the input, or
/// the place and message of the first character it can't lex.
///
/// # Errors
///
/// The first lexical error, by its offset and its message.
pub fn lex_text(text: &str) -> Result<Vec<TextToken>, (TextSize, String)> {
    let lexed = crate::lexer::lex(text, Position::START);
    if let Some(error) = &lexed.error {
        return Err((error.range.start(), error.message.clone()));
    }
    let sigs = crate::stream::stream(text, &lexed, None, false);
    Ok(sigs
        .iter()
        .filter(|s| s.kind != EOF)
        .map(|s| {
            // A separator that a newline inserts sits on the token before it; a written `;`
            // is its own text.
            let inserted = s.kind == SEP
                && text.get(s.range.start().into()..s.range.end().into()) != Some(";");
            TextToken {
                kind: s.kind,
                range: if inserted {
                    TextRange::empty(s.range.end())
                } else {
                    s.range
                },
                inserted,
            }
        })
        .collect())
}
