//! The grammar of the VS Code extension, in `TextMate` form, written from its template with the
//! words and tokens of the Reference, and the table of the keywords that direct control that the
//! language server's semantic tokens mark, so that both color a word alike.
//!
//! The template is the grammar with placeholders in its regular expressions:
//!
//! | Placeholder | Becomes |
//! | --- | --- |
//! | `{{header}}` | The line that says the grammar is generated, and how |
//! | `{{class NAME}}` | The words of the class `NAME` of [`CLASSES`], as alternatives |
//! | `{{other-keywords}}` | The keywords and reserved words that no class holds |
//! | `{{primitive-types}}`, `{{limits}}` | The primitive type names; the limits of `without` |
//! | `{{tokens GROUP, …}}` | The tokens of the groups of lexical.tokens |
//! | `{{token TEXT}}` | The token `TEXT` |
//!
//! A token matches only where maximal munch reads it, so `<` doesn't match the start of `<=`.

use std::fmt::Write;

use crate::lexical::Lexical;
use crate::names::COMPILER;

/// The template, the grammar it gives, and the language server's table of control keywords.
pub(crate) const TEMPLATE: &str = "editors/vscode/syntaxes/stilt.tmLanguage.template.json";
pub(crate) const PATH: &str = "editors/vscode/syntaxes/stilt.tmLanguage.json";
pub(crate) const CONTROL_PATH: &str = "compiler/stilt-ide/src/editor/tokens/control.rs";

/// The classes of words that the editors color apart: those that direct control (a branch, a
/// loop, a jump, a failure or a handler's), declare, bind, mark a parameter's mode or a stage, are
/// reserved for a later tier, or are values. Each word is a keyword, a reserved word or a
/// contextual keyword of the Reference.
const CLASSES: [(&str, &[&str]); 8] = [
    (
        "control",
        &[
            "if", "else", "match", "for", "in", "while", "loop", "break", "continue", "return",
            "yield", "try", "catch", "raise", "because", "assert", "with", "resume", "await",
            "when",
        ],
    ),
    (
        "declaration",
        &[
            "const", "effect", "extern", "fn", "handler", "impl", "macro", "module", "pub",
            "syntax", "test", "trait", "type", "use", "where",
        ],
    ),
    ("binding", &["let", "var"]),
    ("mode", &["inout", "escaping"]),
    ("staging", &["comptime", "async"]),
    ("reserved", &["unsafe"]),
    ("boolean", &["true", "false"]),
    ("self", &["self", "Self"]),
];

/// The grammar that the template gives with the Reference's lists.
pub(crate) fn emit(template: &str, lexical: &Lexical) -> Result<String, String> {
    check_classes(lexical)?;
    let mut out = String::new();
    let mut rest = template;
    while let Some(start) = rest.find("{{") {
        let end = rest[start..]
            .find("}}")
            .ok_or_else(|| format!("{TEMPLATE}: a `{{{{` without its `}}}}`"))?;
        out += &rest[..start];
        out += &json(&expand(rest[start + 2..start + end].trim(), lexical)?);
        rest = &rest[start + end + 2..];
    }
    Ok(out + rest)
}

/// The text a placeholder stands for, as a regular expression.
fn expand(placeholder: &str, lexical: &Lexical) -> Result<String, String> {
    let (name, argument) = placeholder.split_once(' ').unwrap_or((placeholder, ""));
    Ok(match name {
        "header" => format!(
            "Generated from {TEMPLATE} and the words and tokens of reference/02-lexical.md by \
             `just grammar-generate`; `just grammar` checks it is current."
        ),
        "class" => words(class(argument)?.iter().copied()),
        "other-keywords" => {
            let classed: Vec<&str> = CLASSES
                .iter()
                .flat_map(|(_, ws)| ws.iter().copied())
                .collect();
            let rest = lexical.words().into_iter().filter(|w| !classed.contains(w));
            let rest = words(rest);
            // An empty list of alternatives would match the empty text.
            if rest.is_empty() {
                "(?!)".to_owned()
            } else {
                rest
            }
        }
        "primitive-types" => words(lexical.primitives.iter().map(String::as_str)),
        "limits" => words(lexical.limits.iter().map(String::as_str)),
        "tokens" => {
            let mut tokens = Vec::new();
            for group in argument.split(',') {
                tokens.extend(lexical.group(group.trim())?.iter().map(String::as_str));
            }
            alternatives(lexical, &crate::sources::longest_first(&tokens))
        }
        "token" if lexical.all_tokens().contains(&argument) => alternatives(lexical, &[argument]),
        "token" => {
            return Err(format!(
                "{TEMPLATE}: `{argument}` is no token of lexical.tokens"
            ));
        }
        _ => {
            return Err(format!(
                "{TEMPLATE}: no placeholder `{{{{{placeholder}}}}}`"
            ));
        }
    })
}

fn class(name: &str) -> Result<&'static [&'static str], String> {
    CLASSES
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, words)| *words)
        .ok_or_else(|| format!("{TEMPLATE}: no class `{name}` in tools/grammar/src/textmate.rs"))
}

/// Checks that each word of a class is one the Reference reserves or reads as a keyword somewhere.
fn check_classes(lexical: &Lexical) -> Result<(), String> {
    let words = lexical.words();
    for (name, class) in CLASSES {
        for word in class {
            if !words.contains(word) && !lexical.contextual.iter().any(|c| c == word) {
                return Err(format!(
                    "the class `{name}` of tools/grammar/src/textmate.rs holds `{word}`, which \
                     reference/02-lexical.md doesn't list as a keyword"
                ));
            }
        }
    }
    Ok(())
}

fn words<'a>(words: impl Iterator<Item = &'a str>) -> String {
    words.collect::<Vec<_>>().join("|")
}

/// The tokens as alternatives, each that matches only where maximal munch reads it: not before a
/// character that would make it a longer token.
fn alternatives(lexical: &Lexical, tokens: &[&str]) -> String {
    let all = lexical.all_tokens();
    let token = |t: &&str| {
        let mut after: Vec<char> = all
            .iter()
            .filter(|u| u.len() > t.len() && u.starts_with(*t))
            .filter_map(|u| u[t.len()..].chars().next())
            .collect();
        after.sort_unstable();
        after.dedup();
        let escaped: String = t.chars().map(|c| escape(c, "\\^$.|?*+()[]{}")).collect();
        match after.as_slice() {
            [] => escaped,
            [one] => format!("{escaped}(?!{})", escape(*one, "\\^$.|?*+()[]{}")),
            many => {
                let class: String = many.iter().map(|&c| escape(c, "\\^-[]")).collect();
                format!("{escaped}(?![{class}])")
            }
        }
    };
    tokens.iter().map(token).collect::<Vec<_>>().join("|")
}

fn escape(c: char, special: &str) -> String {
    if special.contains(c) {
        format!("\\{c}")
    } else {
        c.to_string()
    }
}

/// The text as it stands inside a JSON string.
fn json(text: &str) -> String {
    text.replace('\\', "\\\\").replace('"', "\\\"")
}

/// The language server's table of the keywords that direct control, the class `control`.
pub(crate) fn control() -> Result<String, String> {
    let words = class("control")?;
    let mut out = format!(
        "//! The keywords that direct control, which the language server's semantic tokens mark \
         with\n//! `controlFlow`, as the editor grammar gives them `keyword.control`: the class \
         `control` of\n//! `tools/grammar/src/textmate.rs`. Generated by `just grammar-generate`, \
         and checked current by\n//! `just grammar`.\n\nuse stilt_syntax::SyntaxKind::{{self, \
         *}};\n\n/// Each keyword's kind, with its word.\npub(super) const CONTROL: [(SyntaxKind, \
         &str); {}] = [\n",
        words.len()
    );
    for word in words {
        let _ = writeln!(out, "    ({}, {word:?}),", COMPILER.keyword(word));
    }
    Ok(out + "];\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    const LEXICAL: &str = include_str!("../../../reference/02-lexical.md");
    const SYNTAX: &str = include_str!("../../../reference/03-syntax.md");

    #[test]
    fn tokens_match_only_their_longest_reading() {
        let lexical = crate::lexical::read(LEXICAL, SYNTAX).unwrap();
        assert_eq!(expand("token <", &lexical).unwrap(), "<(?![<=])");
        assert_eq!(expand("token ..", &lexical).unwrap(), "\\.\\.(?!=)");
        assert_eq!(expand("token -", &lexical).unwrap(), "-(?![%=>])");
        assert_eq!(expand("tokens Holes", &lexical).unwrap(), "\\?");
        assert!(expand("token ?.", &lexical).is_err());
        assert!(expand("class nothing", &lexical).is_err());
    }
}
