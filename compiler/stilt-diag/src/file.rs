//! A source file that diagnostics are reported in, which places their spans.

use rowan::{TextRange, TextSize};

use crate::line_index::{LineIndex, Position};

/// A file's path and text, with the index that turns offsets into positions.
#[derive(Clone, Debug)]
pub struct File<'a> {
    /// The path, as diagnostics name the file.
    pub path: &'a str,
    /// The text.
    pub text: &'a str,
    index: LineIndex,
}

/// A span placed on one line of a file: where it starts, and the text of its line.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Placed<'a> {
    pub(crate) start: Position,
    /// The columns the span covers on its first line, at least one.
    pub(crate) width: usize,
    pub(crate) line: &'a str,
}

impl<'a> File<'a> {
    /// The file at `path`, whose text is `text`.
    #[must_use]
    pub fn new(path: &'a str, text: &'a str) -> Self {
        Self {
            path,
            text,
            index: LineIndex::new(text),
        }
    }

    /// The position of an offset.
    #[must_use]
    pub fn position(&self, offset: TextSize) -> Position {
        self.index.position(self.text, offset)
    }

    /// A span, placed on its first line. A span that runs past its line is cut at the line's
    /// end.
    pub(crate) fn place(&self, range: TextRange) -> Placed<'a> {
        let start = self.position(range.start());
        let line_end = self.index.line_end(self.text, start.line);
        let end = range.end().min(line_end).max(range.start());
        let width = self.text[usize::from(range.start())..usize::from(end)]
            .chars()
            .count();
        Placed {
            start,
            width: width.max(1),
            line: self.index.line(self.text, start.line),
        }
    }

    /// The offsets at which line `line`, counted from 1, starts and ends, its newline excluded.
    pub(crate) fn line_bounds(&self, line: u32) -> (TextSize, TextSize) {
        (
            self.index.line_start(self.text, line),
            self.index.line_end(self.text, line),
        )
    }

    /// The text of line `line`, counted from 1.
    pub(crate) fn line(&self, line: u32) -> &'a str {
        self.index.line(self.text, line)
    }
}
