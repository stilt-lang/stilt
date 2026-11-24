//! Builds the lossless tree from the parser's events: every token of the text goes into it,
//! trivia included, so the tree's text is the source text.

use std::mem;

use rowan::{GreenNode, GreenNodeBuilder};

use crate::SyntaxKind::{self, *};
use crate::lexer::Lexed;
use crate::parser::{Event, Half};
use crate::stream::Sig;

impl From<SyntaxKind> for rowan::SyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
        Self(kind as u16)
    }
}

/// Builds the tree of `text`, which `lexed` lexes, from the events of a parse of `tokens`.
///
/// Trivia goes into the innermost node open at the next token the parser reads, except that a
/// node starts at its first token: trivia before it goes into its parent.
pub(crate) fn build(
    text: &str,
    lexed: &Lexed,
    tokens: &[Sig],
    mut events: Vec<Event>,
) -> GreenNode {
    let mut sink = Sink {
        text,
        lexed,
        tokens,
        builder: GreenNodeBuilder::new(),
        raw: 0,
        sig: 0,
        depth: 0,
    };
    let mut kinds = Vec::new();
    for i in 0..events.len() {
        match mem::replace(&mut events[i], Event::Tombstone) {
            Event::Start {
                kind,
                forward_parent,
            } => {
                // A node that later nodes wrap starts after them, outermost first.
                kinds.push(kind);
                let mut at = i;
                let mut next = forward_parent;
                while let Some(distance) = next {
                    at += distance as usize;
                    match mem::replace(&mut events[at], Event::Tombstone) {
                        Event::Start {
                            kind,
                            forward_parent,
                        } => {
                            kinds.push(kind);
                            next = forward_parent;
                        }
                        event => unreachable!("a forward parent is a start, not {event:?}"),
                    }
                }
                for kind in kinds.drain(..).rev() {
                    sink.start(kind);
                }
            }
            Event::Finish => sink.finish(),
            Event::Token { kind, half } => sink.token(kind, half),
            Event::Tombstone => {}
        }
    }
    sink.builder.finish()
}

struct Sink<'a> {
    text: &'a str,
    lexed: &'a Lexed,
    tokens: &'a [Sig],
    builder: GreenNodeBuilder<'static>,
    /// The next of the lexer's tokens to put in the tree.
    raw: usize,
    /// The next of the parser's tokens.
    sig: usize,
    depth: usize,
}

impl<'a> Sink<'a> {
    fn start(&mut self, kind: SyntaxKind) {
        if self.depth > 0 {
            let next = self.tokens[self.sig..]
                .iter()
                .find(|t| !t.is_virtual())
                .map_or(self.lexed.tokens.len(), |t| t.start as usize);
            self.flush(next);
        }
        self.builder.start_node(kind.into());
        self.depth += 1;
    }

    fn finish(&mut self) {
        self.depth -= 1;
        if self.depth == 0 {
            self.flush(self.lexed.tokens.len());
        }
        self.builder.finish_node();
    }

    fn token(&mut self, kind: SyntaxKind, half: Half) {
        let sig = self.tokens[self.sig];
        match half {
            Half::Whole => {
                if !sig.is_virtual() {
                    self.flush(sig.start as usize);
                    if matches!(sig.kind, DOC | SEP) {
                        // The comments of a run, with the trivia between them, or the newline
                        // or `;` of a separator: each keeps its own kind.
                        self.flush(sig.end as usize);
                    } else {
                        // One token, under the kind the parser read it as, which differs from
                        // the lexer's only for a contextual keyword.
                        self.builder.token(kind.into(), self.text_of(self.raw));
                        self.raw += 1;
                    }
                }
                self.sig += 1;
            }
            Half::First => {
                self.flush(sig.start as usize);
                self.builder.token(R_ANGLE.into(), ">");
            }
            Half::Second => {
                self.builder.token(R_ANGLE.into(), ">");
                self.raw += 1;
                self.sig += 1;
            }
        }
    }

    /// Puts the lexer's tokens up to `end` into the tree as they are.
    fn flush(&mut self, end: usize) {
        while self.raw < end {
            let kind = self.lexed.tokens[self.raw].kind;
            self.builder.token(kind.into(), self.text_of(self.raw));
            self.raw += 1;
        }
    }

    fn text_of(&self, index: usize) -> &'a str {
        let token = self.lexed.tokens[index];
        &self.text[token.start as usize..(token.start + token.len) as usize]
    }
}
