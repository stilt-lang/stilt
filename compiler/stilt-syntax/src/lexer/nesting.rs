//! How deep a file's brackets and interpolations nest (lexical.nesting).

use rowan::{TextRange, TextSize};
use stilt_diag::{Diagnostic, codes};

use super::Lexed;
use crate::SyntaxKind::{
    L_BRACK, L_CURLY, L_PAREN, R_BRACK, R_CURLY, R_PAREN, STRING_HEAD, STRING_MID, STRING_TAIL,
};

/// How many levels a file may nest.
const LEVELS: u32 = 256;

/// The breach of lexical.nesting, E0008, at the bracket that opens a level with [`LEVELS`] open,
/// or at the quote of the string literal whose interpolation does, among the tokens before the
/// first lexical error.
pub(crate) fn too_deep(lexed: &Lexed) -> Option<Diagnostic> {
    let before = lexed
        .error
        .as_ref()
        .map_or(lexed.tokens.len(), |e| e.tokens_before);
    let mut open = 0;
    for token in &lexed.tokens[..before] {
        // A middle part of a string ends one interpolation and begins the next.
        if matches!(
            token.kind,
            R_PAREN | R_BRACK | R_CURLY | STRING_TAIL | STRING_MID
        ) {
            open = u32::saturating_sub(open, 1);
        }
        if !matches!(
            token.kind,
            L_PAREN | L_BRACK | L_CURLY | STRING_HEAD | STRING_MID
        ) {
            continue;
        }
        if open == LEVELS {
            let at = if token.kind == STRING_HEAD {
                TextRange::at(TextSize::from(token.start), TextSize::from(1))
            } else {
                token.range()
            };
            let message = format!(
                "this opens a level {} deep; a file nests at most {LEVELS}",
                LEVELS + 1
            );
            return Some(Diagnostic::new(codes::E0008, at, message));
        }
        open += 1;
    }
    None
}
