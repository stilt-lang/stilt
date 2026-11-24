//! Whether a module writes the features of records and variadics that put it in the advanced tier
//! (records.advanced-tier; variadics.advanced-tier; program.module-tier): an anonymous record type,
//! literal or pattern, a record bound, an open record type, an update of an anonymous or bounded
//! record, or a pack among a declaration's generics. Each is a form of its own in the syntax. A
//! module that only calls a function with a record bound or a pack that another module declares
//! writes none, and stays in core.

use stilt_db::{Db, SourceFile};
use stilt_syntax::SyntaxKind::{DOT2, L_CURLY, RECORD_EXPR, RECORD_PAT, RECORD_TYPE, TYPE_PARAM};
use stilt_syntax::SyntaxNode;

/// Whether a file's module writes an anonymous or open record's form, or declares a pack.
#[must_use]
pub fn writes_shapes(db: &dyn Db, file: SourceFile) -> bool {
    stilt_db::parse(db, file)
        .syntax()
        .descendants()
        .any(|n| match n.kind() {
            RECORD_TYPE | RECORD_EXPR => true,
            RECORD_PAT => first_token_is(&n, L_CURLY),
            TYPE_PARAM => first_token_is(&n, DOT2),
            _ => false,
        })
}

/// Whether a node's first element is the token `kind`: an anonymous record pattern's `{`,
/// which no path comes before, or a pack's `..`.
fn first_token_is(n: &SyntaxNode, kind: stilt_syntax::SyntaxKind) -> bool {
    n.children_with_tokens()
        .find(|e| !e.kind().is_trivia())
        .is_some_and(|e| e.kind() == kind)
}
