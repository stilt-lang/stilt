//! Positions of the offsets in a text, as diagnostics report them.

use std::fmt;

use rowan::TextSize;

/// A position in source text: a line and a column, both counted from 1. Columns count Unicode
/// scalar values.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Position {
    /// The line.
    pub line: u32,
    /// The column.
    pub col: u32,
}

impl Position {
    /// The start of a file.
    pub const START: Self = Self { line: 1, col: 1 };
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

/// The starts of a text's lines, which turn byte offsets into positions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LineIndex {
    /// The offset of each line's first byte.
    starts: Vec<TextSize>,
}

impl LineIndex {
    /// The index of a text, which is under 4 GiB, as every source file is.
    #[must_use]
    pub fn new(text: &str) -> Self {
        let starts = std::iter::once(0)
            .chain(text.match_indices('\n').map(|(i, _)| i + 1))
            .map(|offset| TextSize::from(to_u32(offset)))
            .collect();
        Self { starts }
    }

    /// The position of the byte at `offset` in `text`, the text the index was made from. Its
    /// column counts the characters before it on its line, as the lexer's positions do.
    #[must_use]
    pub fn position(&self, text: &str, offset: TextSize) -> Position {
        let line = self.line_of(offset);
        let before = &text[usize::from(self.starts[line])..usize::from(offset)];
        Position {
            line: to_u32(line + 1),
            col: to_u32(before.chars().count() + 1),
        }
    }

    /// The text of line `line`, counted from 1, without its newline.
    #[must_use]
    pub fn line<'a>(&self, text: &'a str, line: u32) -> &'a str {
        let index = line.saturating_sub(1) as usize;
        let start = self
            .starts
            .get(index)
            .map_or(text.len(), |&s| usize::from(s));
        let end = self
            .starts
            .get(index + 1)
            .map_or(text.len(), |&s| usize::from(s));
        let line = text[start..end].trim_end_matches('\n');
        // A `\r\n` ends a line as `\n` does (lexical.source-text).
        line.strip_suffix('\r').unwrap_or(line)
    }

    /// The offset at which line `line`, counted from 1, starts.
    #[must_use]
    pub fn line_start(&self, text: &str, line: u32) -> TextSize {
        let index = line.saturating_sub(1) as usize;
        self.starts
            .get(index)
            .copied()
            .unwrap_or_else(|| TextSize::from(to_u32(text.len())))
    }

    /// The number of lines.
    #[must_use]
    pub fn lines(&self) -> u32 {
        to_u32(self.starts.len())
    }

    /// The offset at which line `line`, counted from 1, ends: that of its newline, the `\r` of a
    /// `\r\n` among them (lexical.source-text), or of the end of the text.
    #[must_use]
    pub fn line_end(&self, text: &str, line: u32) -> TextSize {
        let index = line as usize;
        self.starts.get(index).map_or_else(
            || TextSize::from(to_u32(text.len())),
            |&next| {
                let newline = next - TextSize::from(1);
                let before = usize::from(newline).checked_sub(1);
                match before.map(|b| text.as_bytes().get(b)) {
                    Some(Some(b'\r')) => newline - TextSize::from(1),
                    _ => newline,
                }
            },
        )
    }

    fn line_of(&self, offset: TextSize) -> usize {
        self.starts
            .partition_point(|&start| start <= offset)
            .saturating_sub(1)
    }
}

/// A count in a text under 4 GiB.
fn to_u32(n: usize) -> u32 {
    u32::try_from(n).unwrap_or(u32::MAX)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn columns_count_characters() {
        let text = "ab\n\u{e9}x\n";
        let index = LineIndex::new(text);
        let at = |offset: u32| index.position(text, offset.into());
        assert_eq!(at(0), Position { line: 1, col: 1 });
        assert_eq!(at(3), Position { line: 2, col: 1 });
        assert_eq!(at(5), Position { line: 2, col: 2 });
        assert_eq!(at(7), Position { line: 3, col: 1 });
    }

    #[test]
    fn lines_have_no_newline() {
        let text = "ab\ncd";
        let index = LineIndex::new(text);
        assert_eq!(index.line(text, 1), "ab");
        assert_eq!(index.line(text, 2), "cd");
        assert_eq!(index.line(text, 3), "");
        assert_eq!(index.line_end(text, 1), TextSize::from(2));
        assert_eq!(index.line_end(text, 2), TextSize::from(5));
    }

    #[test]
    fn a_crlf_line_ends_before_its_carriage_return() {
        let text = "ab\r\ncd\r\n";
        let index = LineIndex::new(text);
        assert_eq!(index.line(text, 1), "ab");
        assert_eq!(index.line_end(text, 1), TextSize::from(2));
        assert_eq!(index.line(text, 2), "cd");
    }
}
