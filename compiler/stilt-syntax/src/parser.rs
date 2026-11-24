//! The parser's machinery: it reads the tokens of [`crate::stream`] and records events, which
//! [`crate::tree`] turns into a tree. The grammar itself is in [`crate::grammar`].
//!
//! A syntax error is found at the first token that no program can continue from
//! (syntax.grammar-errors). Each rule of the grammar decides on the token under the
//! cursor, as an LR parser would, so the parser finds the same first error as the reference
//! interpreter's, and then recovers to go on building the tree.

use crate::SyntaxKind::{self, *};
use crate::stream::Sig;

/// What the parser did, in order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Event {
    /// A node starts. A node that a later one wraps, as a binary expression wraps its left
    /// operand, points forward to the node that wraps it.
    Start {
        kind: SyntaxKind,
        forward_parent: Option<u32>,
    },
    Finish,
    /// The parser reads the token under the cursor as `kind`, or half of it.
    Token {
        kind: SyntaxKind,
        half: Half,
    },
    /// A start that was abandoned.
    Tombstone,
}

/// The part of a token that a [`Event::Token`] reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Half {
    Whole,
    /// The first `>` of a `>>` that closes two lists of type arguments
    /// (syntax.closing-angle-brackets).
    First,
    /// The second `>` of such a `>>`.
    Second,
}

/// A syntax error, at the index of the token where the parser found it, with what the grammar
/// expected there, when the parser knows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ParseError {
    pub(crate) token: usize,
    pub(crate) expected: Option<Expected>,
}

/// What the grammar expected where a syntax error is found.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Expected {
    /// A token of this kind.
    Token(SyntaxKind),
    /// A `,` or the token of this kind, which ends a list.
    CommaOr(SyntaxKind),
    /// A form, in words, as "an expression".
    Form(&'static str),
}

pub(crate) struct Parser<'t> {
    /// The tokens the parser may read: all of them, or those before a limit.
    tokens: &'t [Sig],
    all: &'t [Sig],
    pos: usize,
    /// Whether the token under the cursor is the second `>` of a `>>`, whose first one the
    /// parser has read.
    half: bool,
    events: Vec<Event>,
    errors: Vec<ParseError>,
    /// The quotes open where the cursor is, inside which `$` begins a splice (macros.splices).
    quotes: u32,
    /// What else the grammar takes at the token under the cursor, after a list's element: a
    /// `,`, besides the bracket that ends the list.
    hint: Option<Expected>,
}

impl<'t> Parser<'t> {
    pub(crate) fn new(tokens: &'t [Sig]) -> Self {
        Self {
            tokens,
            all: tokens,
            pos: 0,
            half: false,
            events: Vec::new(),
            errors: Vec::new(),
            quotes: 0,
            hint: None,
        }
    }

    /// Whether the cursor is inside a quote, where `$` begins a splice (macros.splices).
    pub(crate) fn in_quote(&self) -> bool {
        self.quotes > 0
    }

    /// Reads the contents of a quote with `read`, inside which `$` begins a splice.
    pub(crate) fn quoted<T>(&mut self, read: impl FnOnce(&mut Self) -> T) -> T {
        self.quotes += 1;
        let read = read(self);
        self.quotes -= 1;
        read
    }

    pub(crate) fn finish(self) -> (Vec<Event>, Vec<ParseError>) {
        (self.events, self.errors)
    }

    /// The kind of the token `n` places ahead. Past the tokens, which end early only before a
    /// lexical error, every token reads as the end of the input.
    pub(crate) fn nth(&self, n: usize) -> SyntaxKind {
        if n == 0 && self.half {
            return R_ANGLE;
        }
        self.tokens.get(self.pos + n).map_or(EOF, |t| t.kind)
    }

    pub(crate) fn current(&self) -> SyntaxKind {
        self.nth(0)
    }

    pub(crate) fn at(&self, kind: SyntaxKind) -> bool {
        self.current() == kind
    }

    /// Whether the token under the cursor is an identifier that spells the contextual keyword
    /// `kind`.
    pub(crate) fn at_contextual(&self, kind: SyntaxKind) -> bool {
        self.nth_contextual(0) == Some(kind)
    }

    /// The contextual keyword that the token `n` places ahead spells, if any.
    pub(crate) fn nth_contextual(&self, n: usize) -> Option<SyntaxKind> {
        if n == 0 && self.half {
            return None;
        }
        self.tokens.get(self.pos + n).and_then(|t| t.contextual)
    }

    /// Reads the token under the cursor, which must be `kind`.
    pub(crate) fn bump(&mut self, kind: SyntaxKind) {
        assert!(
            self.at(kind),
            "expected {kind:?}, found {:?}",
            self.current()
        );
        self.bump_any();
    }

    /// Reads the token under the cursor as the contextual keyword `kind` that it spells.
    pub(crate) fn bump_contextual(&mut self, kind: SyntaxKind) {
        assert!(self.at_contextual(kind));
        self.push_token(kind, Half::Whole);
    }

    /// Reads the token under the cursor, whatever it is. The end of the input is never read.
    pub(crate) fn bump_any(&mut self) {
        match self.current() {
            EOF => {}
            _ if self.half => {
                self.half = false;
                self.push_token(R_ANGLE, Half::Second);
            }
            kind => self.push_token(kind, Half::Whole),
        }
    }

    fn push_token(&mut self, kind: SyntaxKind, half: Half) {
        self.hint = None;
        self.events.push(Event::Token { kind, half });
        if half != Half::First {
            self.pos += 1;
        }
    }

    /// Reads the token under the cursor if it is `kind`.
    pub(crate) fn eat(&mut self, kind: SyntaxKind) -> bool {
        if self.at(kind) {
            self.bump(kind);
            true
        } else {
            false
        }
    }

    /// Reads a token of kind `kind`, or records an error.
    pub(crate) fn expect(&mut self, kind: SyntaxKind) -> bool {
        if self.eat(kind) {
            return true;
        }
        let expected = match self.hint {
            Some(Expected::CommaOr(close)) if close == kind => Expected::CommaOr(close),
            _ => Expected::Token(kind),
        };
        self.error_expecting(expected);
        false
    }

    /// Notes that a `,` could stand where the list that `close` ends could end.
    pub(crate) fn hint_comma(&mut self, close: SyntaxKind) {
        self.hint = Some(Expected::CommaOr(close));
    }

    /// Whether the token under the cursor is a `>` that closes a list of type arguments: a `>`,
    /// the second half of a `>>`, or a `>>` that also closes the list around this one.
    pub(crate) fn at_closing_angle(&self) -> bool {
        matches!(self.current(), R_ANGLE | SHR)
    }

    /// Reads the `>` that closes a list of type arguments, splitting a `>>` whose second half
    /// closes the list around this one. An error at that second half is reported at the `>>`,
    /// since the reference interpreter reads it as one token.
    pub(crate) fn expect_closing_angle(&mut self) -> bool {
        match self.current() {
            R_ANGLE => {
                self.bump_any();
                true
            }
            SHR => {
                self.half = true;
                self.events.push(Event::Token {
                    kind: R_ANGLE,
                    half: Half::First,
                });
                true
            }
            _ => {
                self.error();
                false
            }
        }
    }

    /// Records a syntax error at the token under the cursor.
    pub(crate) fn error(&mut self) {
        self.errors.push(ParseError {
            token: self.pos,
            expected: None,
        });
    }

    /// Records a syntax error at the token under the cursor, where the grammar expected `what`.
    pub(crate) fn error_expecting(&mut self, what: Expected) {
        self.errors.push(ParseError {
            token: self.pos,
            expected: Some(what),
        });
    }

    /// Reads tokens into an error node up to one of `stop` outside brackets, a closing bracket
    /// that no bracket here opened, or the end of the input.
    pub(crate) fn skip_until(&mut self, stop: &[SyntaxKind]) {
        let m = self.start();
        let mut depth = 0_u32;
        loop {
            let kind = self.current();
            if kind == EOF || (depth == 0 && stop.contains(&kind)) {
                break;
            }
            match kind {
                L_PAREN | L_BRACK | L_CURLY => depth += 1,
                R_PAREN | R_BRACK | R_CURLY if depth == 0 => break,
                R_PAREN | R_BRACK | R_CURLY => depth -= 1,
                _ => {}
            }
            self.bump_any();
        }
        m.complete(self, ERROR);
    }

    /// Every token, past any limit.
    pub(crate) fn all(&self) -> &'t [Sig] {
        self.all
    }

    /// The index of the token under the cursor.
    pub(crate) fn pos(&self) -> usize {
        self.pos
    }

    /// Makes the token at `end`, and every one after it, read as the end of the input, or with
    /// `None`, lifts the limit.
    pub(crate) fn limit(&mut self, end: Option<usize>) {
        self.tokens = end.map_or(self.all, |end| &self.all[..end]);
    }

    /// What the parser has done so far, to go back to with [`Parser::rewind`].
    pub(crate) fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            events: self.events.len(),
            pos: self.pos,
            errors: self.errors.len(),
            quotes: self.quotes,
        }
    }

    /// The token of the first syntax error since a checkpoint.
    pub(crate) fn error_since(&self, at: Checkpoint) -> Option<usize> {
        self.errors.get(at.errors).map(|e| e.token)
    }

    /// The first syntax error since a checkpoint.
    pub(crate) fn first_error_since(&self, at: Checkpoint) -> Option<ParseError> {
        self.errors.get(at.errors).copied()
    }

    /// How many syntax errors the parser found since a checkpoint.
    pub(crate) fn errors_since(&self, at: Checkpoint) -> usize {
        self.errors.len() - at.errors
    }

    /// Undoes everything the parser did since a checkpoint, its errors included.
    pub(crate) fn rewind(&mut self, at: Checkpoint) {
        self.events.truncate(at.events);
        self.errors.truncate(at.errors);
        self.pos = at.pos;
        self.half = false;
        self.hint = None;
        self.quotes = at.quotes;
    }

    /// Forgets the syntax errors found since a checkpoint.
    pub(crate) fn drop_errors(&mut self, at: Checkpoint) {
        self.errors.truncate(at.errors);
    }

    /// Opens again the node that the parser completed last, to add nodes to its end.
    pub(crate) fn reopen(&mut self) {
        let last = self.events.pop();
        assert_eq!(last, Some(Event::Finish), "the last node is complete");
    }

    /// Completes the node that [`Parser::reopen`] opened again.
    pub(crate) fn close(&mut self) {
        self.events.push(Event::Finish);
    }

    pub(crate) fn start(&mut self) -> Marker {
        let index = self.events.len();
        self.events.push(Event::Tombstone);
        Marker { index }
    }
}

/// What a parser has done, to go back to.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Checkpoint {
    events: usize,
    pos: usize,
    errors: usize,
    quotes: u32,
}

/// A node that has started.
#[derive(Debug)]
#[must_use = "a node that starts must complete or be abandoned"]
pub(crate) struct Marker {
    index: usize,
}

impl Marker {
    pub(crate) fn complete(self, p: &mut Parser<'_>, kind: SyntaxKind) -> CompletedMarker {
        p.events[self.index] = Event::Start {
            kind,
            forward_parent: None,
        };
        p.events.push(Event::Finish);
        CompletedMarker { index: self.index }
    }

    pub(crate) fn abandon(self, p: &mut Parser<'_>) {
        if self.index == p.events.len() - 1 {
            p.events.pop();
        }
    }
}

/// A node that has completed.
#[derive(Clone, Copy, Debug)]
pub(crate) struct CompletedMarker {
    index: usize,
}

impl CompletedMarker {
    /// Starts a node that wraps this one.
    pub(crate) fn precede(self, p: &mut Parser<'_>) -> Marker {
        let parent = p.start();
        let distance = u32::try_from(parent.index - self.index).expect("events fit in u32");
        match &mut p.events[self.index] {
            Event::Start { forward_parent, .. } => *forward_parent = Some(distance),
            event => unreachable!("a completed node starts with a start event, not {event:?}"),
        }
        parent
    }
}
