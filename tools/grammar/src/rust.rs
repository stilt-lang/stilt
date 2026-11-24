//! The compiler's tables of words and tokens, `compiler/stilt-syntax/src/lexer/lexicon.rs`.

use std::fmt::Write;

use crate::lexical::Lexical;
use crate::names::COMPILER;

/// The path of the compiler's tables.
pub(crate) const PATH: &str = "compiler/stilt-syntax/src/lexer/lexicon.rs";

/// The text of the compiler's tables, laid out as rustfmt lays it out.
pub(crate) fn emit(lexical: &Lexical) -> Result<String, String> {
    let words = lexical.words();
    let keywords: Vec<(&str, String)> = words.iter().map(|w| (*w, COMPILER.keyword(w))).collect();
    let contextual: Vec<(&str, String)> = lexical
        .contextual
        .iter()
        .map(|w| (w.as_str(), COMPILER.keyword(w)))
        .collect();
    let limits: Vec<(&str, String)> = lexical
        .limits
        .iter()
        .map(|w| (w.as_str(), COMPILER.keyword(w)))
        .collect();
    let punctuation = crate::sources::longest_first(&lexical.all_tokens())
        .into_iter()
        .map(|t| Ok((t, COMPILER.token(t)?)))
        .collect::<Result<Vec<_>, String>>()?;
    let primitives: Vec<String> = lexical
        .primitives
        .iter()
        .map(|p| format!("{p:?}"))
        .collect();
    let mut out = String::from(
        "//! The words and tokens of `reference/02-lexical.md`, and the limits of the `limit` \
         production of\n\
         //! `reference/03-syntax.md`. Generated from the Reference by `just grammar-generate`, \
         and checked\n\
         //! current by `just grammar`.\n\nuse crate::SyntaxKind::{self, *};\n",
    );
    out += &pairs(
        "The keywords of lexical.keywords, then the words that lexical.reserved-words reserves.",
        "pub(crate) const KEYWORDS",
        &keywords,
    );
    out += &pairs(
        "The contextual keywords of lexical.contextual-keywords, which the lexer leaves as \
         identifiers\n/// and the parser reads as keywords where its grammar accepts them.",
        "pub(crate) const CONTEXTUAL",
        &contextual,
    );
    out += &pairs(
        "The limits of a `without` clause, the alternatives of the production `limit`.",
        "pub(crate) const LIMITS",
        &limits,
    );
    out += &pairs(
        "The operators and punctuation of lexical.tokens, longest first, for maximal munch.",
        "pub(crate) const PUNCTUATION",
        &punctuation,
    );
    let head = format!(
        "pub const PRIMITIVE_TYPES: [&str; {}] = [",
        primitives.len()
    );
    out += "\n/// The primitive type names of lexical.primitive-type-names.\n";
    out += &mixed(&head, &primitives);
    Ok(out)
}

/// A table of spellings and kinds, one to a line.
fn pairs(doc: &str, item: &str, entries: &[(&str, String)]) -> String {
    let mut out = format!(
        "\n/// {doc}\n{item}: [(&str, SyntaxKind); {}] = [\n",
        entries.len()
    );
    for (text, kind) in entries {
        let _ = writeln!(out, "    ({text:?}, {kind}),");
    }
    out + "];\n"
}

/// An array of short items, on the line of `head` when it fits in 100 columns, and otherwise
/// filling lines of 100 columns, as rustfmt lays out short items.
fn mixed(head: &str, items: &[String]) -> String {
    let one = format!("{head}{}];\n", items.join(", "));
    if one.len() <= 101 {
        return one;
    }
    let mut out = format!("{head}\n");
    let mut line = String::from("   ");
    for item in items {
        if line.len() + 1 + item.len() + 1 > 100 {
            out += &line;
            out.push('\n');
            line = String::from("   ");
        }
        let _ = write!(line, " {item},");
    }
    out + &line + "\n];\n"
}
