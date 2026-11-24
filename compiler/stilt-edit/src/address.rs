//! The addresses of parts (edits.paths, edits.body-addresses and edits.hash): a path, `/body` for a
//! body, and `#` with the four lowercase hexadecimal digits of a hash.

use std::fmt;

/// An address: the path of a declaration, whether it names the body, and the hash it was
/// written with.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Address {
    /// The path of the declaration.
    pub path: String,
    /// Whether the address names the body.
    pub body: bool,
    /// The four hexadecimal digits of the hash the address was written with, if any.
    pub hash: Option<String>,
}

/// Why a text isn't an address, in a phrase that completes "the address ... ".
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Malformed {
    /// What is wrong, as a phrase.
    pub reason: String,
    /// The byte range of the text it is about.
    pub at: std::ops::Range<usize>,
}

impl Address {
    /// Reads an address. With `hash`, the hash is required; without it, it is optional.
    ///
    /// # Errors
    ///
    /// [`Malformed`] when the text is no path (edits.paths), or its hash isn't `#` and four
    /// lowercase hexadecimal digits.
    pub fn parse(text: &str, hash: bool) -> Result<Self, Malformed> {
        let (head, digits) = split_hash(text);
        let digits = match (digits, hash) {
            (Some(d), _) => Some(d),
            (None, true) => {
                return Err(Malformed {
                    reason: "has no hash".to_owned(),
                    at: text.len()..text.len(),
                });
            }
            (None, false) => None,
        };
        let (path, body) = match head.strip_suffix("/body") {
            Some(path) => (path, true),
            None => (head, false),
        };
        if let Some(reason) = bad_path(path) {
            return Err(Malformed {
                reason,
                at: 0..path.len(),
            });
        }
        if let Some(d) = digits {
            let good = d.len() == 4 && d.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'));
            if !good {
                return Err(Malformed {
                    reason: format!("has a hash of {}", describe(d)),
                    at: head.len()..text.len(),
                });
            }
        }
        Ok(Self {
            path: path.to_owned(),
            body,
            hash: digits.map(str::to_owned),
        })
    }
}

impl fmt::Display for Address {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.path)?;
        if self.body {
            write!(f, "/body")?;
        }
        if let Some(hash) = &self.hash {
            write!(f, "#{hash}")?;
        }
        Ok(())
    }
}

/// How the digits after a `#` are described: by their count when they are hexadecimal digits of
/// the wrong count, and otherwise by what is wrong with them.
fn describe(digits: &str) -> String {
    let hex = digits
        .bytes()
        .all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'));
    let lower = |n: usize| match n {
        0 => "no digits".to_owned(),
        1 => "one digit".to_owned(),
        n => format!("{n} digits"),
    };
    if hex {
        lower(digits.len())
    } else {
        format!("{}, not all lowercase hexadecimal", lower(digits.len()))
    }
}

/// The text before a trailing `#` and what follows it. A `#` inside a quoted test name isn't
/// one.
fn split_hash(text: &str) -> (&str, Option<&str>) {
    let mut quoted = false;
    let mut escaped = false;
    let mut at = None;
    for (i, c) in text.char_indices() {
        match c {
            '\\' if quoted && !escaped => {
                escaped = true;
                continue;
            }
            '"' if !escaped => quoted = !quoted,
            '#' if !quoted => at = Some(i),
            _ => {}
        }
        escaped = false;
    }
    match at {
        Some(i) => (&text[..i], Some(&text[i + 1..])),
        None => (text, None),
    }
}

/// What is wrong with a path, if anything: it is names separated by dots, the last of which may
/// be a quoted test name.
fn bad_path(path: &str) -> Option<String> {
    if path.is_empty() {
        return Some("names no path".to_owned());
    }
    let mut rest = path;
    loop {
        if let Some(quoted) = rest.strip_prefix('"') {
            return match string_end(quoted) {
                Some(n) if n + 1 == quoted.len() => None,
                _ => Some("has a test name that doesn't end the path".to_owned()),
            };
        }
        let len = rest
            .bytes()
            .take_while(|b| b.is_ascii_alphanumeric() || *b == b'_')
            .count();
        if len == 0 {
            return Some("has an empty name in its path".to_owned());
        }
        rest = &rest[len..];
        match rest.strip_prefix('.') {
            Some(more) => rest = more,
            None if rest.is_empty() => return None,
            None => return Some(format!("has `{}` in its path", rest.chars().next()?)),
        }
    }
}

/// The index of the quote that closes a string whose text, after its opening quote, is `s`.
fn string_end(s: &str) -> Option<usize> {
    let mut escaped = false;
    for (i, c) in s.char_indices() {
        match c {
            '\\' if !escaped => escaped = true,
            '"' if !escaped => return Some(i),
            _ => escaped = false,
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::Address;

    fn parse(text: &str) -> Result<Address, String> {
        Address::parse(text, true).map_err(|m| m.reason)
    }

    #[test]
    fn reads_the_addresses_of_each_kind_of_part() {
        let a = parse("main.totals/body#a91f").unwrap();
        assert_eq!((a.path.as_str(), a.body), ("main.totals", true));
        assert_eq!(a.to_string(), "main.totals/body#a91f");
        let a = parse("pretty.Order.Pretty.pretty#0000").unwrap();
        assert!(!a.body);
        let a = parse("main.\"a/body#b\"/body#1234").unwrap();
        assert_eq!((a.path.as_str(), a.body), ("main.\"a/body#b\"", true));
        let a = parse("main.\"a/body\"#1234").unwrap();
        assert_eq!((a.path.as_str(), a.body), ("main.\"a/body\"", false));
    }

    #[test]
    fn refuses_what_is_no_address() {
        assert!(parse("main.totals").is_err());
        assert!(
            parse("main.totals/body#a91")
                .unwrap_err()
                .contains("3 digits")
        );
        assert!(parse("main.totals#A91F").is_err());
        assert!(parse("main..totals#a91f").is_err());
        assert!(parse("#a91f").is_err());
        assert!(parse("main.total s#a91f").is_err());
        assert!(Address::parse("main.totals", false).is_ok());
    }
}
