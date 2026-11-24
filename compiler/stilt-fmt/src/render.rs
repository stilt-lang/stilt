//! Lays out a stream of tokens: decides which groups go on one line, breaks the lines, writes
//! the comments and blank lines, and indents.
//!
//! A group goes on one line when nothing in it forces a break and the whole line fits in 100
//! columns: the line up to the group, the group, and the rest of the line after it, the run tied
//! to it on one line and then up to its next possible break. Comments that end lines don't
//! count. A group inside a group on one line is on one line too. A group that doesn't fit breaks
//! at each of its gaps, but a gap that fills its line breaks only where the element after it
//! doesn't fit, and the groups inside it then decide for themselves. A group that ends in a
//! block, or in the arguments of its last call, may instead keep its start on one line and break
//! only after it (a hugging group), when that start fits.
//!
//! Indentation is two spaces per level (syntax.format.indentation). Each `(`, `[` and `{` indents
//! the lines inside it one level deeper than the line it opens on, and its closing bracket, at the
//! start of a line, goes back to that line's level. A line that starts an element, such as a
//! statement or an argument, is at the bracket's level, and a line that continues one is a level
//! deeper. The `{` of a body on a line that continues its statement indents the body one level
//! deeper than the statement, and the lines that continue the head of a control construct are two
//! levels deeper, so that the body doesn't look like part of the head. The `{` after an `else` or a
//! `catch` indents as a bracket does.

use crate::stream::{Break, Group, Role, Start, Stream, Tok, width};
use crate::trivia::Line;

/// The columns a line may take.
const WIDTH: usize = 100;

/// The spaces of one level of indentation.
const INDENT: &str = "  ";

pub(crate) fn render(stream: &Stream, extra: usize) -> String {
    let mut r = Renderer {
        stream,
        width: WIDTH + extra,
        out: String::new(),
        col: 0,
        level: 0,
        brackets: vec![0],
        open: Vec::new(),
        next_group: 0,
        continued: false,
        line_depth: 0,
    };
    for i in 0..stream.toks.len() {
        r.token(i);
    }
    r.out
}

struct Renderer<'a> {
    stream: &'a Stream,
    /// The columns a line may take.
    width: usize,
    out: String,
    /// The column after the last token written.
    col: usize,
    /// The indentation of the current line.
    level: usize,
    /// For each open bracket, the level of the elements inside it.
    brackets: Vec<usize>,
    /// The open groups, innermost last, and how each is laid out.
    open: Vec<(usize, Layout)>,
    /// The next group to open, by its first token.
    next_group: usize,
    /// Whether the current line continues an element.
    continued: bool,
    /// The number of open brackets where the current line starts.
    line_depth: usize,
}

/// How a group is laid out.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Layout {
    /// On one line.
    Flat,
    /// At each of its gaps.
    Broken,
    /// On the line of its start, up to its `hug` token, and after the token as the groups inside
    /// it decide.
    Hugging,
}

impl Renderer<'_> {
    fn token(&mut self, i: usize) {
        let toks = &self.stream.toks;
        let tok = &toks[i];
        let outside = self.breaks(i);
        let owned = self.open_groups(i, outside);
        let breaks = if owned { self.breaks(i) } else { outside };
        if tok.trailing && !self.breaks(i + 1) {
            return;
        }
        if tok.role == Role::End {
            self.end(tok, i == 0);
            return;
        }
        if i == 0 {
            self.lines(&tok.trivia.lines, 0, true, false);
        } else if breaks {
            self.line_break(tok, &toks[i - 1]);
        } else if tok.space {
            self.out.push(' ');
            self.col += 1;
        }
        self.text(&tok.text);
        self.open_bracket(tok);
        let groups = &self.stream.groups;
        while self.open.last().is_some_and(|&(g, _)| groups[g].last == i) {
            self.open.pop();
        }
    }

    /// Writes the text of a token. The lines after the first of a text that spans lines, a use's
    /// group (macros.formatting), are indented by the indentation of the line it starts on, more
    /// than their own, which is relative to that line's.
    fn text(&mut self, text: &str) {
        let mut lines = text.split('\n');
        let first = lines.next().unwrap_or_default();
        self.out.push_str(first);
        self.col += width(first);
        for line in lines {
            self.out.push('\n');
            self.col = 0;
            if !line.is_empty() {
                for _ in 0..self.level {
                    self.out.push_str(INDENT);
                }
                self.col = self.level * INDENT.len();
            }
            self.out.push_str(line);
            self.col += width(line);
        }
    }

    /// Records the level of the lines inside a bracket that a token opens, or closes the
    /// record of one.
    fn open_bracket(&mut self, tok: &Tok) {
        match tok.role {
            Role::Open => self.brackets.push(self.level + 1),
            Role::OpenBody => {
                let inside = *self.brackets.last().expect("the file's level");
                let base = if self.continued && self.brackets.len() <= self.line_depth {
                    inside
                } else {
                    self.level
                };
                self.brackets.push(base + 1);
            }
            Role::Close => {
                self.brackets.pop();
            }
            Role::Plain | Role::End => {}
        }
    }

    /// Opens the groups that start at token `i`, outermost first, deciding for each how it is
    /// laid out. `outside` is whether the gap before the token breaks, as the group around
    /// decides it. Whether a group started that decides the gap itself.
    fn open_groups(&mut self, i: usize, outside: bool) -> bool {
        let mut owned = false;
        let groups = &self.stream.groups;
        while self.next_group < groups.len() && groups[self.next_group].first == i {
            let group = &groups[self.next_group];
            let layout = self.layout(group, i, outside);
            owned |= group.owned;
            self.open.push((self.next_group, layout));
            self.next_group += 1;
        }
        owned
    }

    fn layout(&self, group: &Group, i: usize, outside: bool) -> Layout {
        let (col, lead) = if group.owned {
            (self.col, 0)
        } else if outside {
            (self.level_of(&self.stream.toks[i]) * INDENT.len(), 0)
        } else {
            (self.col, group.lead)
        };
        if group.can_flat && (self.flat() || self.fits(group, col + lead + group.width)) {
            Layout::Flat
        } else if group.hug.is_some()
            && group.hug_flat
            && col + lead + group.hug_width <= self.width
        {
            Layout::Hugging
        } else {
            Layout::Broken
        }
    }

    /// Whether the innermost open group is on one line.
    fn flat(&self) -> bool {
        self.open
            .last()
            .is_some_and(|&(_, layout)| layout == Layout::Flat)
    }

    /// Whether the gap before token `i` breaks the line. Outside every group, lines break where
    /// the stream says.
    fn breaks(&self, i: usize) -> bool {
        let tok = &self.stream.toks[i];
        tok.trivia.has_comment()
            || match tok.brk {
                Break::Hard => true,
                Break::Soft => !self.gap_flat(i),
                Break::Fill => !self.gap_flat(i) && !self.fills(i),
                Break::Flat => false,
            }
    }

    /// Whether the element of a list of literals that starts at token `i`, with the comma after
    /// it, fits on the rest of the line.
    fn fills(&self, i: usize) -> bool {
        let toks = &self.stream.toks;
        let rest: usize = toks[i + 1..]
            .iter()
            .take_while(|t| t.brk == Break::Flat && !t.trivia.has_comment())
            .map(|t| usize::from(t.space) + width(&t.text))
            .sum();
        self.col + usize::from(toks[i].space) + width(&toks[i].text) + rest <= self.width
    }

    /// Whether a gap that the innermost open group decides stays on the line.
    fn gap_flat(&self, i: usize) -> bool {
        self.open.last().is_some_and(|&(g, layout)| match layout {
            Layout::Flat => true,
            Layout::Broken => false,
            Layout::Hugging => {
                let group = &self.stream.groups[g];
                group.hug.is_some_and(|hug| i <= hug) || i == group.last
            }
        })
    }

    /// Whether the rest of the line fits after a group that ends at column `col`: the run tied
    /// to the group on one line, and then up to the next possible break.
    fn fits(&self, group: &Group, mut col: usize) -> bool {
        let toks = &self.stream.toks;
        let mut j = group.last + 1;
        let tied = group.tied.unwrap_or(group.last);
        while col <= self.width && j < toks.len() {
            let tok = &toks[j];
            let shown = if j <= tied {
                if tok.brk == Break::Hard || tok.trivia.has_comment() {
                    break;
                }
                !tok.trailing
            } else {
                if rest_breaks(tok) {
                    break;
                }
                !tok.trailing || toks.get(j + 1).is_some_and(rest_breaks)
            };
            if shown {
                col += usize::from(tok.space) + width(&tok.text);
            }
            j += 1;
        }
        col <= self.width
    }

    /// The level of the line that a token starts.
    fn level_of(&self, tok: &Tok) -> usize {
        let inside = *self.brackets.last().expect("the file's level");
        match (tok.role, tok.start) {
            (Role::Close, _) => inside - 1,
            (_, Start::Element) => inside,
            (_, Start::Continuation) => inside + 1,
            (_, Start::Head) => inside + 2,
        }
    }

    /// Breaks the line before a token, writing the comment that ends the line, and the blank
    /// lines and comment lines in the gap, at the level of the token, or of the entries before
    /// a closing bracket.
    fn line_break(&mut self, tok: &Tok, prev: &Tok) {
        if let Some(comment) = &tok.trivia.trailing {
            self.out.push(' ');
            self.out.push_str(comment);
        }
        self.out.push('\n');
        let inside = *self.brackets.last().expect("the file's level");
        let level = self.level_of(tok);
        self.continued = tok.start != Start::Element && tok.role != Role::Close;
        self.line_depth = self.brackets.len();
        let comments = if tok.role == Role::Close {
            inside
        } else {
            level
        };
        let after_open = matches!(prev.role, Role::Open | Role::OpenBody);
        self.lines(
            &tok.trivia.lines,
            comments,
            after_open,
            tok.role == Role::Close,
        );
        self.indent(level);
    }

    /// Writes the blank lines and comment lines of a gap, each comment at `level`. A blank line
    /// right after an opening bracket, or right before a closing one, is dropped.
    fn lines(&mut self, lines: &[Line], level: usize, after_open: bool, before_close: bool) {
        let start = usize::from(after_open && lines.first() == Some(&Line::Blank));
        let end = lines.len() - usize::from(before_close && lines.last() == Some(&Line::Blank));
        for line in lines.get(start..end).unwrap_or_default() {
            match line {
                Line::Blank => self.out.push('\n'),
                Line::Comment(text) => {
                    self.indent(level);
                    self.out.push_str(text);
                    self.out.push('\n');
                }
            }
        }
    }

    fn indent(&mut self, level: usize) {
        for _ in 0..level {
            self.out.push_str(INDENT);
        }
        self.level = level;
        self.col = level * INDENT.len();
    }

    /// Ends the file: the comment that ends its last line, the comment lines after it, and one
    /// newline. A file with no tokens holds only its comment lines.
    fn end(&mut self, tok: &Tok, empty: bool) {
        if empty {
            self.lines(&tok.trivia.lines, 0, true, true);
            return;
        }
        if let Some(comment) = &tok.trivia.trailing {
            self.out.push(' ');
            self.out.push_str(comment);
        }
        self.out.push('\n');
        self.lines(&tok.trivia.lines, 0, false, true);
    }
}

/// Whether the gap before a token after a group breaks the line, when deciding whether the
/// group fits. The groups after it are taken to break, which is their widest line.
fn rest_breaks(tok: &Tok) -> bool {
    tok.trivia.has_comment()
        || match tok.brk {
            Break::Hard | Break::Soft | Break::Fill => true,
            Break::Flat => false,
        }
}
