//! Format specs, whose grammar is lexical.format-specs: `[[fill]align][width][.precision][kind]`.
//! Their meaning is std.width-fill-and-alignment, std.precision, std.integer-kinds,
//! std.scientific-notation and std.format-special-values.

/// A format spec.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FormatSpec {
    /// The character that pads the value to its width, a space unless written.
    pub fill: char,
    /// `<`, `^` or `>`, if written.
    pub align: Option<char>,
    /// The width, 0 unless written.
    pub width: u32,
    /// The precision, if written.
    pub precision: Option<u32>,
    /// `x`, `X`, `o`, `b` or `e`, if written.
    pub kind: Option<char>,
}

/// The largest width and the largest precision.
const LIMIT: u32 = 65535;

fn is_align(byte: u8) -> bool {
    matches!(byte, b'<' | b'^' | b'>')
}

/// Parses the text of a spec, which follows its `:`.
#[must_use]
pub fn parse(text: &str) -> Option<FormatSpec> {
    let bytes = text.as_bytes();
    let first = text.chars().next();
    let first_len = first.map_or(0, char::len_utf8);
    // A fill of `{` would read as the start of an interpolation.
    let (fill, align, mut i) = match first {
        Some(c) if bytes.len() > first_len && is_align(bytes[first_len]) && c != '{' => {
            (c, Some(char::from(bytes[first_len])), first_len + 1)
        }
        _ if !bytes.is_empty() && is_align(bytes[0]) => (' ', Some(char::from(bytes[0])), 1),
        _ => (' ', None, 0),
    };
    let (width, after) = number(bytes, i)?;
    i = after;
    let precision = if bytes.get(i) == Some(&b'.') {
        let (precision, after) = number(bytes, i + 1)?;
        if after == i + 1 {
            return None;
        }
        i = after;
        Some(precision)
    } else {
        None
    };
    let kind = match bytes.get(i) {
        Some(&b) if b"xXobe".contains(&b) => {
            i += 1;
            Some(char::from(b))
        }
        _ => None,
    };
    (i == bytes.len()).then_some(FormatSpec {
        fill,
        align,
        width,
        precision,
        kind,
    })
}

/// A number up to [`LIMIT`] starting at byte `i`, and the offset after it: 0 and `i` when no
/// digit is there. A number has no leading zero, so `05` is no width.
fn number(bytes: &[u8], i: usize) -> Option<(u32, usize)> {
    if bytes.get(i) == Some(&b'0') && bytes.get(i + 1).is_some_and(u8::is_ascii_digit) {
        return None;
    }
    let mut value = 0;
    let mut j = i;
    while let Some(&digit) = bytes.get(j).filter(|b| b.is_ascii_digit()) {
        value = value * 10 + u32::from(digit - b'0');
        if value > LIMIT {
            return None;
        }
        j += 1;
    }
    Some((value, j))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parts() {
        let spec = parse("*^12.3e").expect("a valid spec");
        assert_eq!(
            spec,
            FormatSpec {
                fill: '*',
                align: Some('^'),
                width: 12,
                precision: Some(3),
                kind: Some('e')
            }
        );
        assert_eq!(parse("<").map(|s| s.align), Some(Some('<')));
        assert_eq!(parse("<<").map(|s| s.fill), Some('<'));
        assert_eq!(parse("é>3").map(|s| s.fill), Some('é'));
    }

    #[test]
    fn limits_and_leading_zeros() {
        assert!(parse("65535.65535").is_some());
        assert!(parse("65536").is_none());
        assert!(parse(".65536").is_none());
        assert!(parse("0").is_some());
        assert!(parse("05").is_none());
        assert!(parse("0>5").is_some());
        assert!(parse(".").is_none());
        assert!(parse("{>3").is_none());
        assert!(parse("3x!").is_none());
    }
}
