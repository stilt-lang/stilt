//! Positions of the protocol, a line and a character counted in UTF-16 code units, both from
//! 0, and the bytes of a text they stand for; and the `file:` URIs of paths.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use serde_json::{Value, json};

/// The position of the byte `offset` of `text`: of the character it is in, when it is inside
/// one, and of the end of the text, past it.
pub(crate) fn position(text: &str, offset: usize) -> Value {
    let before = &text[..text.floor_char_boundary(offset)];
    let line = before.matches('\n').count();
    let start = before.rfind('\n').map_or(0, |n| n + 1);
    let character: usize = before[start..].chars().map(char::len_utf16).sum();
    json!({ "line": line, "character": character })
}

/// How many UTF-16 code units `text` takes.
pub(crate) fn utf16_len(text: &str) -> usize {
    text.chars().map(char::len_utf16).sum()
}

/// The range from `start` to `end`, bytes of `text`.
pub(crate) fn range(text: &str, start: u32, end: u32) -> Value {
    json!({ "start": position(text, start as usize), "end": position(text, end as usize) })
}

/// The byte of `text` at a position, or the end of its line, or of the text, past them.
pub(crate) fn offset(text: &str, position: &Value) -> usize {
    let line = position["line"].as_u64().unwrap_or(0);
    let character = position["character"].as_u64().unwrap_or(0);
    let mut start = 0;
    for _ in 0..line {
        match text[start..].find('\n') {
            Some(n) => start += n + 1,
            None => return text.len(),
        }
    }
    let end = text[start..].find('\n').map_or(text.len(), |n| start + n);
    let mut units = 0;
    for (i, c) in text[start..end].char_indices() {
        if units >= character {
            return start + i;
        }
        units += c.len_utf16() as u64;
    }
    end
}

/// The `file:` URI of an absolute path, each byte outside the unreserved characters and `/`
/// written as `%XX`.
#[must_use]
pub fn uri(path: &Path) -> String {
    let mut out = String::from("file://");
    for b in path.to_string_lossy().bytes() {
        if b.is_ascii_alphanumeric() || b"-._~/".contains(&b) {
            out.push(char::from(b));
        } else {
            let _ = write!(out, "%{b:02X}");
        }
    }
    out
}

/// The path of a `file:` URI, if it is one.
pub(crate) fn path(uri: &str) -> Option<PathBuf> {
    let rest = uri.strip_prefix("file://")?;
    let bytes = rest.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%'
            && let Some(b) = rest
                .get(i + 1..i + 3)
                .and_then(|h| u8::from_str_radix(h, 16).ok())
        {
            out.push(b);
            i += 3;
        } else {
            out.push(bytes[i]);
            i += 1;
        }
    }
    Some(PathBuf::from(String::from_utf8_lossy(&out).into_owned()))
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use serde_json::json;

    use super::{offset, path, position, uri};

    #[test]
    fn a_character_beyond_the_basic_plane_counts_two_units() {
        let text = "a\n\u{1F600}é = 1\n";
        assert_eq!(position(text, 2), json!({"line": 1, "character": 0}));
        assert_eq!(position(text, 6), json!({"line": 1, "character": 2}));
        assert_eq!(position(text, 8), json!({"line": 1, "character": 3}));
        assert_eq!(offset(text, &json!({"line": 1, "character": 3})), 8);
        assert_eq!(offset(text, &json!({"line": 1, "character": 99})), 12);
        assert_eq!(
            offset(text, &json!({"line": 9, "character": 0})),
            text.len()
        );
    }

    #[test]
    fn a_byte_inside_a_character_stands_for_the_character() {
        let text = "a\n\u{20AC}\u{1F600}";
        assert_eq!(position(text, 3), json!({"line": 1, "character": 0}));
        assert_eq!(position(text, 4), json!({"line": 1, "character": 0}));
        assert_eq!(position(text, 7), json!({"line": 1, "character": 1}));
        assert_eq!(position(text, 99), json!({"line": 1, "character": 3}));
    }

    #[test]
    fn a_path_and_its_uri_go_both_ways() {
        let p = Path::new("/tmp/a b/é.lt");
        assert_eq!(uri(p), "file:///tmp/a%20b/%C3%A9.lt");
        assert_eq!(path(&uri(p)).as_deref(), Some(p));
    }
}
