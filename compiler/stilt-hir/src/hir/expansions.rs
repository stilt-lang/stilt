//! The expansions of a body's macro uses (macros.expansion), which its diagnostics' notes name
//! (macros.errors-in-expansions) and `stilt show --expanded` prints in place of the uses
//! (macros.showing).

use stilt_diag::Diagnostic;
use stilt_syntax::forms::Form;
use stilt_syntax::{SyntaxKind, TextRange};

use super::Name;

/// The expansion of a use.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expansion {
    /// The use, where the user wrote it: relative to the body's start, as the body's other
    /// positions are. The uses that templates write are placed at the use of the outermost.
    pub at: TextRange,
    /// The macro, as the use names it, as `tools.greet`.
    pub name: Name,
    /// The template the expansion is made of.
    pub template: Template,
    /// The form the expansion stands as.
    pub form: Form,
    /// Its tokens, each fresh name with the number of its expansion, which is written after a
    /// `#`, as `tmp#1`.
    pub tokens: Vec<ShownTok>,
    /// The expansion its use is in, by index, and the tokens of that one's that the use is,
    /// from the first to just past the last.
    pub parent: Option<(u32, u32, u32)>,
}

/// A token of an expansion as it is shown: its kind, its text, and for a fresh name, its
/// number.
pub type ShownTok = (SyntaxKind, Name, Option<u32>);

/// Where a template is, for a note to show it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Template {
    /// In the body's file, at this span of it, in the file's own positions.
    Here(TextRange),
    /// In another file, written so.
    Elsewhere(String),
}

impl Expansion {
    /// The diagnostic `d` of the body, with a note that names the macro and shows its
    /// template, when the expansion's own tokens put it at the use (macros.errors-in-expansions).
    #[must_use]
    pub fn noted(&self, d: Diagnostic) -> Diagnostic {
        let text = match &self.template {
            Template::Here(_) => format!("`{}!` expands to this", self.name),
            Template::Elsewhere(text) => format!("`{}!` expands to `{text}`", self.name),
        };
        if d.range != self.at || d.notes.iter().any(|n| n.text == text) {
            return d;
        }
        match &self.template {
            Template::Here(at) => d.with_note_in_file(*at, text),
            Template::Elsewhere(_) => d.with_note(self.path(), text),
        }
    }

    /// The diagnostic `d`, found in the expansion at the user's tokens, with a note on the
    /// macro's path that names it when they are those of one of the use's parts, unless a note
    /// names it already (macros.errors-in-expansions; goal compile-time-errors-at-user-code).
    #[must_use]
    pub fn named(&self, d: Diagnostic) -> Diagnostic {
        let named = format!("`{}!`", self.name);
        if d.range == self.at || d.notes.iter().any(|n| n.text.contains(&named)) {
            return d;
        }
        d.with_note(self.path(), format!("in the expansion of {named}"))
    }

    /// The macro's path, as the use writes it.
    fn path(&self) -> TextRange {
        let len = u32::try_from(self.name.len()).unwrap_or(u32::MAX);
        TextRange::at(self.at.start(), len.into())
    }
}

/// A body's diagnostic with the note of the first expansion that places it, if one does, and
/// otherwise, when it lies in the tokens of a use's parts, which only the use's expansion
/// checks, with a note that names the innermost use's macro.
#[must_use]
pub fn noted(expansions: &[Expansion], d: Diagnostic) -> Diagnostic {
    if let Some(e) = expansions.iter().find(|e| e.at == d.range) {
        return e.noted(d);
    }
    let around = (expansions.iter())
        .filter(|e| e.at.contains_range(d.range))
        .min_by_key(|e| e.at.len());
    match around {
        Some(e) => e.named(d),
        None => d,
    }
}

/// The text of the expansion at `index`, with the expansions of the uses its template writes
/// in their places.
#[must_use]
pub fn expanded_text(expansions: &[Expansion], index: usize) -> String {
    text_of(expansions, index, false)
}

/// [`expanded_text`] with each fresh name written as its template or quote wrote it, without
/// its number, which parses as the expansion's form does.
#[must_use]
pub fn expanded_source(expansions: &[Expansion], index: usize) -> String {
    text_of(expansions, index, true)
}

fn text_of(expansions: &[Expansion], index: usize, plain: bool) -> String {
    let own = &expansions[index];
    let mut inner: Vec<(usize, u32, u32)> = expansions
        .iter()
        .enumerate()
        .filter_map(|(i, e)| match e.parent {
            Some((parent, start, end)) if parent as usize == index => Some((i, start, end)),
            _ => None,
        })
        .collect();
    inner.sort_by_key(|&(_, start, _)| start);
    // Each piece is a token, or an inner expansion, with the kinds of its first and last
    // tokens.
    let mut pieces: Vec<(SyntaxKind, SyntaxKind, String)> = Vec::new();
    let token = |(kind, text, number): &ShownTok| {
        let text = match number {
            Some(n) if !plain => format!("{text}#{n}"),
            _ => text.to_string(),
        };
        (*kind, *kind, text)
    };
    let mut at = 0;
    for (i, start, end) in inner {
        if (start as usize) < at {
            continue;
        }
        pieces.extend(own.tokens[at..start as usize].iter().map(token));
        let inner = &expansions[i].tokens;
        let kind = |t: Option<&ShownTok>| t.map_or(SyntaxKind::ERROR, |t| t.0);
        pieces.push((
            kind(inner.first()),
            kind(inner.last()),
            text_of(expansions, i, plain),
        ));
        at = end as usize;
    }
    pieces.extend(own.tokens[at.min(own.tokens.len())..].iter().map(token));
    spaced(&pieces)
}

/// Tokens written with the spaces the canonical format puts between them, closely enough to
/// read: none inside brackets or around a `.`, and none before `,`, `;` or `:`.
fn spaced(pieces: &[(SyntaxKind, SyntaxKind, String)]) -> String {
    use SyntaxKind::{
        BANG, COLON, COMMA, DOT, L_BRACK, L_CURLY, L_PAREN, LOWER_IDENT, QUESTION, R_BRACK,
        R_CURLY, R_PAREN, SEP, STRING_HEAD, STRING_MID, STRING_TAIL, UPPER_IDENT,
    };
    let mut out = String::new();
    let mut last: Option<SyntaxKind> = None;
    for (kind, end, text) in pieces {
        // A block in an interpolation keeps a space from its braces, which would read as one
        // escaped.
        let braces = matches!(
            (last, *kind),
            (Some(STRING_HEAD | STRING_MID), L_CURLY) | (Some(R_CURLY), STRING_MID | STRING_TAIL)
        );
        let glued = !braces
            && matches!(
                (last, *kind),
                (
                    None | Some(L_PAREN | L_BRACK | DOT | STRING_HEAD | STRING_MID | BANG),
                    _
                ) | (Some(LOWER_IDENT), BANG)
                    | (
                        _,
                        R_PAREN | R_BRACK | COMMA | SEP | COLON | DOT | STRING_MID | STRING_TAIL
                    )
                    | (
                        Some(LOWER_IDENT | UPPER_IDENT | R_PAREN | R_BRACK | QUESTION),
                        L_PAREN | L_BRACK
                    )
            );
        if !glued {
            out.push(' ');
        }
        out.push_str(text);
        last = Some(*end);
    }
    out
}
