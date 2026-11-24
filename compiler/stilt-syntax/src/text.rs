//! The values that literal tokens spell.

use crate::SyntaxKind::*;
use crate::SyntaxToken;

/// The text of a string literal token, or of a part of an interpolated string, with its escapes
/// resolved (lexical.escapes). An invalid escape, which only a file with a syntax error holds,
/// stays as written.
#[must_use]
pub fn string_value(token: &SyntaxToken) -> String {
    let text = token.text();
    // The quote or the `}` before the text, and the quote or the `{` after it.
    let close = match token.kind() {
        STRING | STRING_TAIL => text.strip_suffix('"'),
        STRING_HEAD | STRING_MID => text.strip_suffix('{'),
        _ => None,
    };
    let inner = close.map_or(text, |inner| &inner[1..]);
    unescape(inner)
}

/// The value of a string literal written `text`, its quotes included, with its escapes
/// resolved, as [`string_value`] gives a token's.
#[must_use]
pub fn literal_value(text: &str) -> String {
    let inner = text
        .strip_prefix('"')
        .and_then(|t| t.strip_suffix('"'))
        .unwrap_or(text);
    unescape(inner)
}

fn unescape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        let rest = chars.as_str();
        let escaped = match rest.chars().next() {
            Some('n') => Some('\n'),
            Some('t') => Some('\t'),
            Some('r') => Some('\r'),
            Some('0') => Some('\0'),
            Some(c @ ('\\' | '"' | '{')) => Some(c),
            _ => None,
        };
        if let Some(escaped) = escaped {
            out.push(escaped);
            chars.next();
        } else if let Some(c) = unicode_escape(rest) {
            out.push(c.0);
            chars = rest[c.1..].chars();
        } else {
            out.push('\\');
        }
    }
    out
}

/// The character that `u{X…}` at the start of `rest` names, and its length.
fn unicode_escape(rest: &str) -> Option<(char, usize)> {
    let hex = rest.strip_prefix("u{")?;
    let end = hex.find('}')?;
    let value = u32::from_str_radix(&hex[..end], 16).ok()?;
    Some((char::from_u32(value)?, 2 + end + 1))
}

/// The text of a number literal token without its `_` separators.
#[must_use]
pub fn number_text(token: &SyntaxToken) -> String {
    token.text().replace('_', "")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn escapes() {
        assert_eq!(unescape(r#"a\nb\t\"\{\\\0"#), "a\nb\t\"{\\\0");
        assert_eq!(unescape(r"\u{1F600}x"), "\u{1F600}x");
        assert_eq!(unescape(r"\q"), r"\q");
    }
}
