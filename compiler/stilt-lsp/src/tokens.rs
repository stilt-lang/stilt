//! Semantic tokens as the protocol encodes them: each token five numbers, its line and start
//! relative to the token before it, its length, its type and its modifiers, in UTF-16 units.
//! The types the protocol predefines are used where they fit, and Stilt's own where none
//! does: `boolean`, `selfKeyword`, `effect`, `rowVariable`, `fragment`, `escapeSequence`,
//! `interpolation` and `formatSpecifier`, with the modifier `controlFlow`. The editor's
//! extension gives each of its own a predefined one to fall back on, and the scopes a theme
//! colors, the same that its grammar gives the same text, so that the colors don't change when
//! the server's tokens arrive.

use serde_json::{Value, json};

use crate::text::utf16_len;
use crate::{Token, TokenSort};

/// The token types, in the order the legend lists them.
const TYPES: [(TokenSort, &str); 24] = [
    (TokenSort::Keyword, "keyword"),
    (TokenSort::Boolean, "boolean"),
    (TokenSort::SelfKeyword, "selfKeyword"),
    (TokenSort::Effect, "effect"),
    (TokenSort::Type, "type"),
    (TokenSort::Trait, "interface"),
    (TokenSort::TypeParameter, "typeParameter"),
    (TokenSort::RowVariable, "rowVariable"),
    (TokenSort::Function, "function"),
    (TokenSort::Method, "method"),
    (TokenSort::Parameter, "parameter"),
    (TokenSort::Variable, "variable"),
    (TokenSort::Field, "property"),
    (TokenSort::Variant, "enumMember"),
    (TokenSort::Module, "namespace"),
    (TokenSort::Macro, "macro"),
    (TokenSort::Fragment, "fragment"),
    (TokenSort::Comment, "comment"),
    (TokenSort::String, "string"),
    (TokenSort::EscapeSequence, "escapeSequence"),
    (TokenSort::Interpolation, "interpolation"),
    (TokenSort::FormatSpecifier, "formatSpecifier"),
    (TokenSort::Number, "number"),
    (TokenSort::Operator, "operator"),
];

/// The modifiers, in the order of their bits in [`crate::modifier`].
const MODIFIERS: [&str; 6] = [
    "declaration",
    "readonly",
    "documentation",
    "mutable",
    "defaultLibrary",
    "controlFlow",
];

/// The legend of the token types and modifiers.
pub(crate) fn legend() -> Value {
    let types: Vec<&str> = TYPES.iter().map(|(_, name)| *name).collect();
    json!({ "tokenTypes": types, "tokenModifiers": MODIFIERS })
}

/// The tokens of `text`, in order, encoded. A token over several lines is split at each line's
/// end, a token that ends inside a character ends before it, and a token that starts inside
/// one, that is empty, or that overlaps the one before it is dropped.
pub(crate) fn encode(text: &str, tokens: &[Token]) -> Vec<u32> {
    let mut data = Vec::with_capacity(tokens.len() * 5);
    let (mut line, mut column) = (0usize, 0usize);
    let mut at = Cursor::default();
    let mut end = 0;
    for t in tokens {
        let (start, stop) = (t.start as usize, text.floor_char_boundary(t.end as usize));
        if start < end || start >= stop || !text.is_char_boundary(start) {
            continue;
        }
        end = stop;
        let kind = TYPES.iter().position(|(s, _)| *s == t.sort).unwrap_or(0);
        let mut piece = start;
        for part in text[start..stop].split_inclusive('\n') {
            let length = utf16_len(part.trim_end_matches(['\n', '\r']));
            let (l, c) = at.advance(text, piece);
            piece += part.len();
            if length == 0 {
                continue;
            }
            let delta_line = l - line;
            let delta_start = if delta_line == 0 { c - column } else { c };
            (line, column) = (l, c);
            data.extend(
                [delta_line, delta_start, length, kind, t.modifiers as usize]
                    .map(|n| u32::try_from(n).unwrap_or(u32::MAX)),
            );
        }
    }
    data
}

/// A position in a text that only moves forward, so that encoding a file's tokens reads it
/// once.
#[derive(Default)]
struct Cursor {
    byte: usize,
    line: usize,
    column: usize,
}

impl Cursor {
    /// The line and the UTF-16 column of byte `to`, which is at or after the cursor.
    fn advance(&mut self, text: &str, to: usize) -> (usize, usize) {
        for c in text[self.byte..to].chars() {
            if c == '\n' {
                self.line += 1;
                self.column = 0;
            } else {
                self.column += c.len_utf16();
            }
        }
        self.byte = to;
        (self.line, self.column)
    }
}

#[cfg(test)]
mod tests {
    use super::encode;
    use crate::{Token, TokenSort};

    #[test]
    fn tokens_are_relative_to_the_one_before_and_split_at_lines() {
        let text = "fn é() {}\n/// a\n";
        let token = |start, end, sort| Token {
            start,
            end,
            sort,
            modifiers: 0,
        };
        let tokens = [
            token(0, 2, TokenSort::Keyword),
            token(3, 5, TokenSort::Function),
            token(11, 17, TokenSort::Comment),
        ];
        // Each type is its index in the legend: `function` is 8, and `comment` 17.
        assert_eq!(
            encode(text, &tokens),
            [0, 0, 2, 0, 0, 0, 3, 1, 8, 0, 1, 0, 5, 17, 0]
        );
    }

    #[test]
    fn a_token_that_ends_inside_a_character_ends_before_it() {
        let text = "a\u{20AC}b\u{1F600}";
        let token = |start, end| Token {
            start,
            end,
            sort: TokenSort::Keyword,
            modifiers: 0,
        };
        // `a€` ends inside `€`, so it holds `a`; `€` alone, cut the same way, holds nothing.
        assert_eq!(encode(text, &[token(0, 3)]), [0, 0, 1, 0, 0]);
        assert_eq!(encode(text, &[token(1, 2)]), Vec::<u32>::new());
        assert_eq!(encode(text, &[token(4, u32::MAX)]), [0, 2, 3, 0, 0]);
    }

    #[test]
    fn the_legend_names_each_sort_once_and_each_modifier_bit_in_order() {
        let legend = super::legend();
        let types = legend["tokenTypes"].as_array().unwrap();
        let mut names: Vec<&str> = types.iter().filter_map(|t| t.as_str()).collect();
        names.sort_unstable();
        names.dedup();
        assert_eq!(names.len(), super::TYPES.len());
        let modifiers = &legend["tokenModifiers"];
        assert_eq!(modifiers[5], "controlFlow");
        assert_eq!(crate::modifier::CONTROL_FLOW, 1 << 5);
    }
}
