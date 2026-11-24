//! Reading the values of header annotations (conformance.header-annotations) and the codes of
//! inline entries (conformance.inline-annotations).

use super::Tier;

/// The panic kinds of effects.panic-kinds, shared.when-on-value-already-held, and c.lending-buffer,
/// that a conformance test can expect. `check-error` is raised only in a program with errors, which
/// `run` runs all the same (program.programs-with-errors).
const PANIC_KINDS: [&str; 13] = [
    "bounds",
    "missing-key",
    "divide-by-zero",
    "unreachable",
    "assert",
    "explicit",
    "hole",
    "utf8-boundary",
    "overflow",
    "check-error",
    "deadlock",
    "unwrap",
    "nul-in-string",
];

pub(crate) fn is_code(code: &str, prefix: char) -> bool {
    code.strip_prefix(prefix)
        .is_some_and(|digits| digits.len() == 4 && digits.bytes().all(|b| b.is_ascii_digit()))
}

pub(super) fn parse_tier(value: &str) -> Result<Tier, String> {
    match value {
        "core" => Ok(Tier::Core),
        "advanced" => Ok(Tier::Advanced),
        "meta" => Ok(Tier::Meta),
        "systems" => Ok(Tier::Systems),
        _ => Err(format!("unknown tier `{value}`")),
    }
}

/// The paragraph IDs of a `rule` annotation, separated by commas (conformance.rule-citations).
/// An ID is two or three parts separated by `.`, each words of lowercase letters and digits
/// joined by `-`, as `values.independent-copies`.
pub(super) fn parse_rules(value: &str) -> Result<Vec<String>, String> {
    let ids: Vec<String> = value.split(',').map(|id| id.trim().to_owned()).collect();
    let is_word = |word: &str| {
        !word.is_empty()
            && word
                .bytes()
                .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit())
    };
    let is_id = |id: &String| {
        let parts: Vec<&str> = id.split('.').collect();
        (2..=3).contains(&parts.len()) && parts.iter().all(|part| part.split('-').all(is_word))
    };
    match ids.iter().find(|id| !is_id(id)) {
        Some(id) => Err(format!(
            "`{id}` is not a paragraph ID such as `values.independent-copies`"
        )),
        None => Ok(ids),
    }
}

pub(crate) fn parse_exit(value: &str) -> Result<i32, String> {
    value
        .parse::<u8>()
        .map(i32::from)
        .map_err(|_| format!("`{value}` is not an exit status from 0 to 255"))
}

pub(super) fn parse_panic(value: &str) -> Result<String, String> {
    if PANIC_KINDS.contains(&value) {
        Ok(value.to_owned())
    } else {
        Err(format!("unknown panic kind `{value}`"))
    }
}

/// Reads a location `path:line:col`, with a line and column from 1.
pub(super) fn parse_location(value: &str) -> Result<String, String> {
    let mut parts = value.rsplitn(3, ':');
    let numbers_ok = parts
        .by_ref()
        .take(2)
        .all(|n| n.parse::<usize>().is_ok_and(|n| n > 0));
    match parts.next() {
        Some(path) if numbers_ok && !path.is_empty() && !path.contains(' ') => Ok(value.to_owned()),
        _ => Err(format!("`{value}` is not a location such as `main.lt:4:7`")),
    }
}

pub(super) fn utf8(bytes: Vec<u8>) -> Result<String, String> {
    String::from_utf8(bytes).map_err(|_| "only `stdin` may hold bytes that aren't UTF-8".to_owned())
}

/// Reads a quoted string that makes up the whole value.
pub(super) fn parse_quoted(value: &str) -> Result<Vec<u8>, String> {
    let (text, rest) = quoted(value)?;
    if !rest.is_empty() {
        return Err(format!("unexpected text after the closing quote: `{rest}`"));
    }
    Ok(text)
}

/// Reads words separated by spaces, where a double-quoted word may hold spaces and escapes.
pub(super) fn parse_words(value: &str) -> Result<Vec<String>, String> {
    let mut words = Vec::new();
    let mut rest = value.trim_start_matches(' ');
    while !rest.is_empty() {
        if rest.starts_with('"') {
            let (word, after) = quoted(rest)?;
            if !after.is_empty() && !after.starts_with(' ') {
                return Err("a quoted word must be followed by a space".to_owned());
            }
            words.push(utf8(word)?);
            rest = after;
        } else {
            let end = rest.find(' ').unwrap_or(rest.len());
            let word = &rest[..end];
            if word.contains(['"', '\\']) {
                return Err(format!("`{word}` must be quoted"));
            }
            words.push(word.to_owned());
            rest = &rest[end..];
        }
        rest = rest.trim_start_matches(' ');
    }
    Ok(words)
}

/// Reads a quoted string at the start of `text`, and returns its bytes with the text that
/// follows. `\xNN` is the byte with the hexadecimal value `NN`.
fn quoted(text: &str) -> Result<(Vec<u8>, &str), String> {
    let body = text
        .strip_prefix('"')
        .ok_or_else(|| format!("expected a quoted string, found `{text}`"))?;
    let mut value = Vec::new();
    let mut chars = body.char_indices();
    while let Some((index, c)) = chars.next() {
        match c {
            '"' => return Ok((value, &body[index + 1..])),
            '\\' => match chars.next() {
                Some((_, 'n')) => value.push(b'\n'),
                Some((_, 'r')) => value.push(b'\r'),
                Some((_, 't')) => value.push(b'\t'),
                Some((_, '"')) => value.push(b'"'),
                Some((_, '\\')) => value.push(b'\\'),
                Some((_, 'x')) => {
                    let digits: String = chars.by_ref().take(2).map(|(_, d)| d).collect();
                    let byte = u8::from_str_radix(&digits, 16)
                        .ok()
                        .filter(|_| {
                            digits.len() == 2 && digits.bytes().all(|d| d.is_ascii_hexdigit())
                        })
                        .ok_or_else(|| format!("`\\x{digits}` needs two hexadecimal digits"))?;
                    value.push(byte);
                }
                Some((_, other)) => return Err(format!("unknown escape `\\{other}`")),
                None => break,
            },
            _ => {
                let mut buffer = [0; 4];
                value.extend_from_slice(c.encode_utf8(&mut buffer).as_bytes());
            }
        }
    }
    Err("unterminated quoted string".to_owned())
}
