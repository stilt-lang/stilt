//! The tokens that hold pieces of different sorts: a doc comment, whose example or property is code
//! (tests.prop-lines), and whose code in backticks is left to the editor's grammar, which marks it
//! as code; and a string, or a piece of an interpolated one, whose escapes are marked apart from
//! its text and whose braces open and close its interpolations (lexical.escapes and
//! lexical.interpolation).

use stilt_lsp::modifier::{DOCUMENTATION, LIBRARY};
use stilt_lsp::{Token, TokenSort};
use stilt_syntax::SyntaxKind::*;
use stilt_syntax::SyntaxToken;

/// A doc comment: documentation, and after `ex:` or `prop:`, its code read word by word.
pub(super) fn doc(token: &SyntaxToken, found: &mut Vec<Token>) {
    let start = u32::from(token.text_range().start());
    let text = token.text();
    let body = text.strip_prefix("///").unwrap_or(text);
    let lead = text.len() - body.trim_start().len();
    let trimmed = body.trim_start();
    let marker = ["ex:", "prop:"]
        .into_iter()
        .find(|m| trimmed.starts_with(m));
    let at = |n: usize| start + u32::try_from(n).unwrap_or(0);
    let Some(marker) = marker else {
        for (from, to) in prose(text) {
            found.push(piece(at(from), at(to), TokenSort::Comment, 0));
        }
        return;
    };
    found.push(piece(start, at(lead), TokenSort::Comment, 0));
    found.push(piece(
        at(lead),
        at(lead + marker.len()),
        TokenSort::Keyword,
        0,
    ));
    let code = lead + marker.len();
    for (from, to, sort, modifiers) in words(&text[code..]) {
        found.push(piece(at(code + from), at(code + to), sort, modifiers));
    }
}

/// The spans of a doc line of prose outside its code in backticks, from each closing backtick
/// to the next opening one. A backtick that no other closes opens no code.
fn prose(text: &str) -> Vec<(usize, usize)> {
    let ticks: Vec<usize> = text.match_indices('`').map(|(i, _)| i).collect();
    let mut spans = Vec::new();
    let mut from = 0;
    for [open, close] in ticks.as_chunks::<2>().0 {
        if *open > from {
            spans.push((from, *open));
        }
        from = close + 1;
    }
    if from < text.len() {
        spans.push((from, text.len()));
    }
    spans
}

fn piece(start: u32, end: u32, sort: TokenSort, modifiers: u32) -> Token {
    Token {
        start,
        end,
        sort,
        modifiers: modifiers | DOCUMENTATION,
    }
}

/// The words, numbers and strings of a line of code, each with its span, sort and modifiers:
/// a keyword, a variant or a function where a `(` follows, a type, or a variable.
fn words(code: &str) -> Vec<(usize, usize, TokenSort, u32)> {
    let bytes = code.as_bytes();
    let mut found = Vec::new();
    let mut i = 0;
    let word = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    while i < bytes.len() {
        let start = i;
        let b = bytes[i];
        if b == b'"' {
            i += 1;
            while i < bytes.len() && bytes[i] != b'"' {
                i += if bytes[i] == b'\\' { 2 } else { 1 };
            }
            i = (i + 1).min(bytes.len());
            found.push((start, i, TokenSort::String, 0));
        } else if b.is_ascii_alphanumeric() || b == b'_' {
            while i < bytes.len() && word(bytes[i]) {
                i += 1;
            }
            let library = if stilt_syntax::is_primitive(&code[start..i]) {
                LIBRARY
            } else {
                0
            };
            found.push((start, i, sort(code, start, i), library));
            if let Some((sort, modifiers)) = (stilt_syntax::is_keyword(&code[start..i]))
                .then(|| super::keywords::word(&code[start..i]))
            {
                let last = found.len() - 1;
                found[last] = (start, i, sort, modifiers);
            }
        } else {
            i += code[i..].chars().next().map_or(1, char::len_utf8);
        }
    }
    found
}

/// The prelude's variants (std.option-result-and-ordering), which a doc example names without a
/// payload.
const PRELUDE_VARIANTS: [&str; 7] = ["None", "Some", "Ok", "Err", "Less", "Equal", "Greater"];

/// What the word from `start` to `end` of a line of code is, read by the tokens around it as
/// the editor's grammar reads it, so that the two agree. An uppercase name is a variant where a
/// payload follows it, where it is one of the prelude's, or where no `{`, `.`, `<` or `>`
/// follows it and it isn't an annotation's type, since an expression names a type only before
/// a struct literal's braces, a function of its own or its type arguments (types.no-type-arguments;
/// declarations.no-aliases); a type otherwise, as a name of one letter or in capitals is. A
/// lowercase name is a module before a `.` and an uppercase name, but for a primitive type, a
/// function where a `(` follows, and a variable otherwise.
fn sort(code: &str, start: usize, end: usize) -> TokenSort {
    let word = &code[start..end];
    let (before, after) = (code[..start].trim_end(), code[end..].trim_start());
    let letters = word.trim_start_matches('_').as_bytes();
    let upper = letters.first().is_some_and(u8::is_ascii_uppercase);
    let shaped = letters
        .get(1)
        .is_some_and(|b| b.is_ascii_lowercase() || b.is_ascii_digit());
    let annotated = before.ends_with(':') && !before.ends_with("::") || before.ends_with("->");
    // What a comparison tests is a value, and a `{` after it opens a block, since a head holds
    // no struct literal (expressions.head-contents).
    let compared = before.ends_with("==") || before.ends_with("!=");
    let typed = after.starts_with(['{', '.', '<', '>']) && !compared;
    let dotted_upper = after.strip_prefix('.').is_some_and(|rest| {
        rest.trim_start()
            .starts_with(|c: char| c.is_ascii_uppercase())
    });
    let called = code[end..].starts_with('(');
    if word.starts_with(|c: char| c.is_ascii_digit()) {
        TokenSort::Number
    } else if stilt_syntax::is_primitive(word) {
        TokenSort::Type
    } else if upper
        && shaped
        && (called || PRELUDE_VARIANTS.contains(&word) || !annotated && !typed)
    {
        TokenSort::Variant
    } else if upper {
        TokenSort::Type
    } else if dotted_upper {
        TokenSort::Module
    } else if after.starts_with('(') {
        TokenSort::Function
    } else {
        TokenSort::Variable
    }
}

/// A string, or a piece of an interpolated one: its text, its escapes, and the braces at its
/// ends that open or close an interpolation (lexical.escapes and lexical.interpolation).
pub(super) fn string(token: &SyntaxToken, found: &mut Vec<Token>) {
    let range = token.text_range();
    let start = u32::from(range.start());
    let text = token.text();
    let at = |n: usize| start + u32::try_from(n).unwrap_or(0);
    let plain = |from: usize, to: usize, sort| Token {
        start: at(from),
        end: at(to),
        sort,
        modifiers: 0,
    };
    let closes = matches!(token.kind(), STRING_MID | STRING_TAIL) && text.starts_with('}');
    let opens = matches!(token.kind(), STRING_HEAD | STRING_MID) && text.ends_with('{');
    let from = usize::from(closes);
    let to = text.len() - usize::from(opens && text.len() > from);
    if closes {
        found.push(plain(0, 1, TokenSort::Interpolation));
    }
    let mut piece = from;
    for (escape, length) in escapes(&text[from..to]) {
        if from + escape > piece {
            found.push(plain(piece, from + escape, TokenSort::String));
        }
        found.push(plain(
            from + escape,
            from + escape + length,
            TokenSort::EscapeSequence,
        ));
        piece = from + escape + length;
    }
    if to > piece {
        found.push(plain(piece, to, TokenSort::String));
    }
    if to < text.len() {
        found.push(plain(to, text.len(), TokenSort::Interpolation));
    }
}

/// Where each escape of a string's text starts, with its length: a `\` and the character
/// after it, or `\u{…}` up to its closing brace.
fn escapes(text: &str) -> Vec<(usize, usize)> {
    let bytes = text.as_bytes();
    let mut found = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] != b'\\' || i + 1 >= bytes.len() {
            i += 1;
            continue;
        }
        let length = if bytes[i + 1] == b'u' && bytes.get(i + 2) == Some(&b'{') {
            text[i..].find('}').map_or(2, |close| close + 1)
        } else {
            1 + text[i + 1..].chars().next().map_or(1, char::len_utf8)
        };
        found.push((i, length));
        i += length;
    }
    found
}

#[cfg(test)]
mod tests {
    use super::{escapes, prose};

    #[test]
    fn prose_leaves_out_its_code_in_backticks() {
        assert_eq!(prose("/// The `n`th one"), [(0, 8), (11, 17)]);
        assert_eq!(prose("/// `a` and `b`"), [(0, 4), (7, 12)]);
        assert_eq!(prose("/// an ` alone"), [(0, 14)]);
    }

    #[test]
    fn an_escape_is_a_backslash_and_a_character_or_a_code_point() {
        assert_eq!(escapes(r#""a\nb\u{1F600}\"""#), [(2, 2), (5, 9), (14, 2)]);
        assert_eq!(escapes("\"plain\""), []);
    }
}
