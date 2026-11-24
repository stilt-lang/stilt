//! The tokens of the formatted file, each with what may go between it and the token before
//! it, and the groups whose tokens go on one line when they fit. The walk of the tree builds
//! them, and the renderer lays them out.

use rustc_hash::FxHashMap;
use stilt_syntax::SyntaxKind::*;
use stilt_syntax::SyntaxToken;

use crate::space::{Class, class, space};
use crate::trivia::Trivia;

/// When the gap before a token holds a line break. A comment in the gap always ends its line.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Break {
    /// Never.
    Flat,
    /// Where the innermost group holding the gap doesn't go on one line and the element after
    /// the gap, with the comma after it, doesn't fit on the rest of the line: the gaps between
    /// the elements of a list of literals, which fills its lines.
    Fill,
    /// Where the innermost group holding the gap doesn't go on one line.
    Soft,
    /// Always.
    Hard,
}

/// How a token takes part in indentation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Role {
    Plain,
    /// A `(`, `[` or `{`, which indents the lines after it by one level: among braces, those of
    /// a record, and those that follow an `else` or a `catch`.
    Open,
    /// The `{` of a block, a `match`, an impl or a trait, which indents the lines after it one
    /// level deeper than the statement it ends the head of.
    OpenBody,
    /// The bracket that closes one.
    Close,
    /// The end of the file, which holds the trivia after the last token.
    End,
}

/// A token of the formatted file.
#[derive(Clone, Debug)]
pub(crate) struct Tok {
    pub(crate) text: String,
    /// Whether one space goes before the token when no line break does.
    pub(crate) space: bool,
    pub(crate) brk: Break,
    pub(crate) trivia: Trivia,
    pub(crate) role: Role,
    /// Whether the token starts an element of the innermost bracket around it.
    pub(crate) start: Start,
    /// Whether the token is a comma at the end of a list, which is written only where the line
    /// breaks after it.
    pub(crate) trailing: bool,
}

/// What a token starts, when it starts a line.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Start {
    /// An element of the innermost bracket around it: a statement, an arm, an item, an argument
    /// or a field.
    Element,
    /// The continuation of an element, a level in.
    Continuation,
    /// The continuation of the head of a control construct, outside any bracket of it, which
    /// is two levels in so that the body isn't mistaken for a part of it.
    Head,
}

/// A run of tokens that goes on one line when it fits, the gap before its first included.
#[derive(Clone, Debug)]
pub(crate) struct Group {
    pub(crate) first: usize,
    pub(crate) last: usize,
    /// Whether the group decides the gap before its first token, which is then part of it.
    /// Otherwise that gap belongs to the group around.
    pub(crate) owned: bool,
    /// Whether nothing in the group forces a line break: a `Hard` gap or a comment.
    pub(crate) can_flat: bool,
    /// The width of the group on one line, without the space before its first token unless the
    /// group owns it.
    pub(crate) width: usize,
    /// The space before the first token, when the group doesn't own it.
    pub(crate) lead: usize,
    /// The token that ends the part of the group that stays on the line of its start when the
    /// group doesn't fit on one line: the `{` of a closure's block, or the `(` of the last
    /// call of a chain. The group then breaks only after it.
    pub(crate) hug: Option<usize>,
    /// Whether nothing forces a line break up to the `hug` token.
    pub(crate) hug_flat: bool,
    /// The width of the group up to the `hug` token.
    pub(crate) hug_width: usize,
    /// The last token of the run after the group that goes on the group's line, whatever its
    /// own groups decide, when the group does: the return type, the row and the limits after a
    /// parameter list, which breaks before they do.
    pub(crate) tied: Option<usize>,
}

/// The tokens and groups of a file.
#[derive(Debug)]
pub(crate) struct Stream {
    pub(crate) toks: Vec<Tok>,
    pub(crate) groups: Vec<Group>,
}

/// Builds a stream from the tokens of a tree, in order.
#[derive(Debug)]
pub(crate) struct Builder {
    trivia: FxHashMap<u32, Trivia>,
    toks: Vec<Tok>,
    groups: Vec<Group>,
    prev: Option<Class>,
    next_break: Break,
    next_element: bool,
    /// The depth of the regions whose gaps never break.
    flat: usize,
    /// Whether the tokens added are in the head of a control construct, and how deep in
    /// brackets of the head.
    deep: Option<usize>,
    /// The `{` of each block that is a closure's body, by token.
    closure_blocks: Vec<usize>,
    /// What the last list added ends with, for the chain that it ends.
    tail: Tail,
}

/// How the last list added ends, for a chain of calls.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Tail {
    /// The `(` of the list, when it holds an element.
    pub(crate) open: Option<usize>,
    /// The `{` of the block that closes it, when a closure's block ends it.
    pub(crate) hug: Option<usize>,
}

impl Builder {
    pub(crate) fn new(trivia: FxHashMap<u32, Trivia>) -> Self {
        Self {
            trivia,
            toks: Vec::new(),
            groups: Vec::new(),
            prev: None,
            next_break: Break::Flat,
            next_element: false,
            flat: 0,
            deep: None,
            closure_blocks: Vec::new(),
            tail: Tail::default(),
        }
    }

    /// Adds a token of the tree.
    pub(crate) fn token(&mut self, token: &SyntaxToken) {
        let trivia = self.take_trivia(token);
        let role = match token.kind() {
            L_PAREN | L_BRACK | L_CURLY => Role::Open,
            R_PAREN | R_BRACK | R_CURLY => Role::Close,
            _ => Role::Plain,
        };
        self.push(token.text().to_owned(), class(token), role, trivia);
    }

    /// Adds the `{` of a block, a `match`, an impl or a trait.
    pub(crate) fn body_open(&mut self, token: &SyntaxToken) {
        let trivia = self.take_trivia(token);
        self.push(
            token.text().to_owned(),
            class(token),
            Role::OpenBody,
            trivia,
        );
    }

    /// The number of tokens added.
    pub(crate) fn len(&self) -> usize {
        self.toks.len()
    }

    /// Notes that the next token is the `{` of a closure's block.
    pub(crate) fn closure_block(&mut self) {
        self.closure_blocks.push(self.toks.len());
    }

    /// The first `{` of a closure's block among the tokens added since token `start`.
    pub(crate) fn closure_block_since(&self, start: usize) -> Option<usize> {
        self.closure_blocks.iter().copied().find(|&i| i >= start)
    }

    /// How the last list added ends.
    pub(crate) fn tail(&self) -> Tail {
        self.tail
    }

    pub(crate) fn set_tail(&mut self, tail: Tail) {
        self.tail = tail;
    }

    /// Adds a comma that the source doesn't spell, at the end of a list, which is written only
    /// where the line breaks after it.
    pub(crate) fn synthetic_trailing_comma(&mut self) {
        self.push(",".to_owned(), Class::Comma, Role::Plain, Trivia::default());
        self.toks.last_mut().expect("the comma").trailing = true;
    }

    /// Runs `f` in the head of a control construct, whose continuation lines go two levels in.
    pub(crate) fn head(&mut self, f: impl FnOnce(&mut Self)) {
        let before = self.deep.replace(0);
        f(self);
        self.deep = before;
    }

    /// Adds a comma that ends a list, which is written only where the line breaks after it.
    pub(crate) fn trailing_comma(&mut self, token: &SyntaxToken) {
        self.token(token);
        let comma = self.toks.last_mut().expect("the comma");
        comma.trailing = !comma.trivia.has_comment();
    }

    /// Leaves out a separator of the tree: a comma between arms. Only spaces can come before it,
    /// since a line that ends with an arm ends it (lexical.terminator-insertion), and a comment
    /// after it goes before the next token.
    pub(crate) fn skip(&mut self, separator: &SyntaxToken) {
        let trivia = self.take_trivia(separator);
        debug_assert!(
            !trivia.newline,
            "a separator on the line of the arm before it"
        );
    }

    /// Leaves out a comma of the tree that the format doesn't write: the one after a `..` that
    /// ends a pattern.
    pub(crate) fn drop(&mut self, separator: &SyntaxToken) {
        self.take_trivia(separator);
    }

    /// Adds a token that the source doesn't spell: a parenthesis around a statement.
    pub(crate) fn synthetic(&mut self, text: &str, class: Class, role: Role, trivia: Trivia) {
        self.push(text.to_owned(), class, role, trivia);
    }

    /// Adds a run of source text as one token, which goes into the file as written.
    pub(crate) fn verbatim(&mut self, text: String, first: &SyntaxToken, class: Class) {
        let trivia = self.take_trivia(first);
        self.push(text, class, Role::Plain, trivia);
    }

    /// Adds a token whose space before it the caller decides, after which the next token is
    /// spaced as after a closing bracket: a token of a macro's declaration, or a use's group as
    /// written, whose tokens no node of an expression classes (macros.formatting). Its text may
    /// span lines, each indented as the renderer writes it.
    pub(crate) fn raw(&mut self, text: String, space: bool, role: Role, trivia: Trivia) {
        self.push(text, Class::Close, role, trivia);
        self.toks.last_mut().expect("the token").space = space;
    }

    /// Takes the trivia before a token of the tree, which no other token then writes.
    pub(crate) fn take_trivia(&mut self, token: &SyntaxToken) -> Trivia {
        self.trivia
            .remove(&u32::from(token.text_range().start()))
            .unwrap_or_default()
    }

    /// The trivia before a token of the tree, left in place.
    pub(crate) fn trivia_of(&self, token: &SyntaxToken) -> Option<&Trivia> {
        self.trivia.get(&u32::from(token.text_range().start()))
    }

    fn push(&mut self, text: String, class: Class, role: Role, trivia: Trivia) {
        let brk = self.next_break;
        let deep = self.deep.is_some_and(|d| d == 0);
        if let Some(d) = &mut self.deep {
            match role {
                Role::Open | Role::OpenBody => *d += 1,
                Role::Close => *d = d.saturating_sub(1),
                _ => {}
            }
        }
        let space = self.prev.is_some_and(|prev| space(prev, class));
        self.toks.push(Tok {
            text,
            space,
            brk,
            trivia,
            role,
            start: if self.next_element {
                Start::Element
            } else if deep {
                Start::Head
            } else {
                Start::Continuation
            },
            trailing: false,
        });
        self.prev = Some(class);
        self.next_break = Break::Flat;
        self.next_element = false;
    }

    /// Makes the gap before the next token break at least as `brk` says.
    pub(crate) fn brk(&mut self, brk: Break) {
        if self.flat == 0 {
            self.next_break = self.next_break.max(brk);
        }
    }

    /// Marks the next token as the start of an element.
    pub(crate) fn element(&mut self) {
        self.next_element = true;
    }

    /// Runs `f` in a region whose gaps never break.
    pub(crate) fn flat(&mut self, f: impl FnOnce(&mut Self)) {
        self.flat += 1;
        f(self);
        self.flat -= 1;
    }

    /// Starts a group at the next token, whose gap belongs to the group around.
    pub(crate) fn open(&mut self) -> usize {
        self.start(false)
    }

    /// Starts a group at the next token, whose gap the group decides.
    pub(crate) fn open_owning(&mut self) -> usize {
        self.start(true)
    }

    fn start(&mut self, owned: bool) -> usize {
        self.groups.push(Group {
            first: self.toks.len(),
            last: usize::MAX,
            owned,
            can_flat: true,
            width: 0,
            lead: 0,
            hug: None,
            hug_flat: false,
            hug_width: 0,
            tied: None,
        });
        self.groups.len() - 1
    }

    /// Ends a group at the last token.
    pub(crate) fn close(&mut self, group: usize) {
        self.groups[group].last = self.toks.len() - 1;
    }

    /// Ties the tokens added since a group closed to it, up to the last: they go on its line
    /// when it goes on one.
    pub(crate) fn tie(&mut self, group: usize) {
        let last = self.toks.len() - 1;
        if last > self.groups[group].last {
            self.groups[group].tied = Some(last);
        }
    }

    /// Ends a group at the last token, which may keep the line of its start up to the token
    /// `hug` when it doesn't fit on one line.
    pub(crate) fn close_hugging(&mut self, group: usize, hug: Option<usize>) {
        self.close(group);
        self.groups[group].hug = hug;
    }

    /// Ends the file with a token that holds the trivia after its last token.
    pub(crate) fn finish(mut self, end: u32) -> Stream {
        let trivia = self.trivia.remove(&end).unwrap_or_default();
        self.toks.push(Tok {
            text: String::new(),
            space: false,
            brk: Break::Hard,
            trivia,
            role: Role::End,
            start: Start::Element,
            trailing: false,
        });
        for group in &mut self.groups {
            measure(&self.toks, group);
        }
        Stream {
            toks: self.toks,
            groups: self.groups,
        }
    }
}

/// The columns that a text takes.
pub(crate) fn width(text: &str) -> usize {
    text.chars().count()
}

/// Whether nothing forces a line break in `toks`, whose first gap is left out when `owned` is
/// false, and their width on one line. A token whose text spans lines, a use's group, forces
/// one, as a comment does.
fn measure_run(toks: &[Tok], owned: bool) -> (bool, usize) {
    let flat = toks.iter().enumerate().all(|(i, t)| {
        ((i == 0 && !owned) || (t.brk != Break::Hard && !t.trivia.has_comment()))
            && !t.text.contains('\n')
    });
    let width = toks
        .iter()
        .enumerate()
        .filter(|(_, t)| !t.trailing)
        .map(|(i, t)| usize::from(t.space && (owned || i > 0)) + width(&t.text))
        .sum();
    (flat, width)
}

/// Works out what the renderer needs to know of a group.
fn measure(toks: &[Tok], group: &mut Group) {
    let run = &toks[group.first..=group.last];
    (group.can_flat, group.width) = measure_run(run, group.owned);
    group.lead = if group.owned {
        0
    } else {
        usize::from(run[0].space)
    };
    if let Some(hug) = group.hug {
        let prefix = &toks[group.first..=hug];
        (group.hug_flat, group.hug_width) = measure_run(prefix, group.owned);
    }
}
