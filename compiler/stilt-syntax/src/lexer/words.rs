//! Words: identifiers, keywords and the wildcard (lexical.identifiers, lexical.keywords and
//! lexical.wildcard).

use stilt_diag::codes;

pub use super::lexicon::PRIMITIVE_TYPES;
use super::lexicon::{CONTEXTUAL, KEYWORDS, LIMITS};
use super::{Lexer, is_ident_char};
use crate::SyntaxKind::{self, *};

/// Whether a word is a keyword (lexical.keywords and lexical.reserved-words), so that it can't be
/// an identifier.
#[must_use]
pub fn is_keyword(text: &str) -> bool {
    keyword(text).is_some()
}

/// Whether `word` is `text`, telling most words apart by their length and first byte before
/// comparing their bytes, since the lexer asks it of every word.
fn spells(word: &str, text: &str) -> bool {
    word.len() == text.len() && word.as_bytes().first() == text.as_bytes().first() && word == text
}

/// The keyword of lexical.keywords that `text` spells, if any.
fn keyword(text: &str) -> Option<SyntaxKind> {
    KEYWORDS
        .iter()
        .find(|(word, _)| spells(word, text))
        .map(|&(_, kind)| kind)
}

/// Whether `name` is a primitive type's name, as `i32` or `str`.
#[must_use]
pub fn is_primitive(name: &str) -> bool {
    PRIMITIVE_TYPES.contains(&name)
}

/// Whether a word can be a segment of a module's name (program.module-names), and so a package's
/// name (packages.package-table): a lowercase identifier, whose first letter is lowercase, that is
/// neither a keyword, a reserved word nor a primitive type name.
#[must_use]
pub fn is_module_segment(word: &str) -> bool {
    !word.is_empty()
        && word.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
        && !word.starts_with(|c: char| c.is_ascii_digit())
        && word
            .bytes()
            .find(u8::is_ascii_alphabetic)
            .is_some_and(|b| b.is_ascii_lowercase())
        && !is_keyword(word)
        && !is_primitive(word)
}

/// The contextual keyword that an identifier spells, if any.
pub(crate) fn contextual_keyword(text: &str) -> Option<SyntaxKind> {
    CONTEXTUAL
        .iter()
        .find(|(word, _)| spells(word, text))
        .map(|&(_, kind)| kind)
}

/// Whether a contextual keyword is a limit of a `without` clause (lexical.contextual-keywords).
pub(crate) fn is_limit(kind: SyntaxKind) -> bool {
    LIMITS.iter().any(|&(_, limit)| limit == kind)
}

impl Lexer<'_> {
    /// lexical.identifiers, lexical.keywords and lexical.wildcard: an identifier, a keyword or the
    /// wildcard.
    pub(super) fn word(&mut self) {
        self.begin();
        let len = self.bytes[self.pos..]
            .iter()
            .position(|&b| !is_ident_char(b))
            .unwrap_or(self.bytes.len() - self.pos);
        self.advance(len);
        let text = &self.text[self.token_start..self.pos];
        let kind = if text == "_" {
            UNDERSCORE
        } else if let Some(keyword) = keyword(text) {
            keyword
        } else {
            match text.bytes().find(u8::is_ascii_alphabetic) {
                Some(letter) if letter.is_ascii_uppercase() => UPPER_IDENT,
                Some(_) => LOWER_IDENT,
                None => {
                    let message = format!("`{text}` has no letter");
                    self.fail(codes::E0003, self.token_mark(), message);
                    ERROR
                }
            }
        };
        self.emit(kind);
    }
}

/// What a part that begins with `word` declares, when another language begins a declaration
/// with it (syntax.parts and errors.broken-parts): `FN` for a function, `TYPE_DECL` for a type,
/// `TRAIT` for a trait, `ERROR` for nothing, and `FN_KW` for `mutating`, which comes before `fn`.
pub(crate) fn foreign_declaration(word: &str) -> Option<SyntaxKind> {
    match word {
        "def" | "func" | "function" | "fun" => Some(FN),
        "struct" | "class" | "enum" => Some(TYPE_DECL),
        "interface" | "protocol" => Some(TRAIT),
        "extension" => Some(ERROR),
        "mutating" => Some(FN_KW),
        _ => None,
    }
}
