//! The types that inference gives the variables a function binds (types.inferred-per-body), which
//! `stilt show` writes in where the source leaves them out, as in `let xs: List<i64> = [1, 2]`
//! (Inferred facts, "Seven commands").

use stilt_db::{Database, Program, SourceFile};
use stilt_diag::LineIndex;
use stilt_syntax::ast::{self, AstNode as _};
use stilt_syntax::{SyntaxNode, TextRange, TextSize};

use crate::text;

/// The pattern of a `let` or a `var` that writes no type, with the type that inference gives it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Local {
    /// The line where the pattern ends.
    pub line: u32,
    /// Where the pattern ends in its file, where its type goes.
    pub end: TextSize,
    /// The pattern as the source writes it.
    pub pattern: String,
    pub ty: String,
}

/// The patterns of the `let` and `var` statements of the body `index` of a file's module that
/// write no type, closures' included, in the order they are written, with their types.
pub(super) fn untyped(db: &Database, program: Program, file: SourceFile, index: u32) -> Vec<Local> {
    let bound = stilt_types::facts::local_types(db, program, file, index);
    if bound.is_empty() {
        return Vec::new();
    }
    let root = stilt_db::parse(db, file).syntax();
    let text = text(db, file);
    let lines = LineIndex::new(&text);
    bound
        .into_iter()
        .filter(|b| writes_type(&root, b.at) == Some(false))
        .map(|b| Local {
            line: lines.position(&text, b.at.end()).line,
            end: b.at.end(),
            pattern: text[usize::from(b.at.start())..usize::from(b.at.end())].to_owned(),
            ty: b.ty,
        })
        .collect()
}

/// Whether the `let` or the `var` whose pattern is at `at` writes its type, if one is there.
fn writes_type(root: &SyntaxNode, at: TextRange) -> Option<bool> {
    let token = root.token_at_offset(at.start()).right_biased()?;
    token.parent_ancestors().find_map(|n| {
        let (pattern, ty) = match ast::Stmt::cast(n)? {
            ast::Stmt::LetStmt(l) => (l.pattern(), l.ty()),
            ast::Stmt::VarStmt(v) => (v.pattern(), v.ty()),
            _ => return None,
        };
        let starts = pattern?.syntax().text_range().start() == at.start();
        starts.then_some(ty.is_some())
    })
}
