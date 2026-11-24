//! The views of statements and blocks.

use super::{AstNode, Expr, Pattern, Type, child, children, nth, tokens};
use crate::SyntaxKind::{self, *};
use crate::{SyntaxNode, SyntaxToken};

nodes! {
    /// A block.
    Block = BLOCK,
    /// `let`.
    LetStmt = LET_STMT,
    /// `var`.
    VarStmt = VAR_STMT,
    /// `assert`.
    AssertStmt = ASSERT_STMT,
    /// `yield`, in a projection's body (projections.yield).
    YieldStmt = YIELD_STMT,
    /// An assignment.
    AssignStmt = ASSIGN_STMT,
    /// An expression statement.
    ExprStmt = EXPR_STMT,
}

enums! {
    /// A statement.
    Stmt { LetStmt, VarStmt, AssertStmt, YieldStmt, AssignStmt, ExprStmt, }
}

impl Block {
    /// The statements, in order.
    pub fn stmts(&self) -> impl Iterator<Item = Stmt> + use<> {
        children(&self.0)
    }
}

/// The parts of `let` and `var`.
macro_rules! binding {
    ($($name:ident),*) => {$(
        impl $name {
            /// The pattern it binds.
            #[must_use]
            pub fn pattern(&self) -> Option<Pattern> {
                child(&self.0)
            }

            /// The annotated type.
            #[must_use]
            pub fn ty(&self) -> Option<Type> {
                child(&self.0)
            }

            /// The expression after `=`.
            #[must_use]
            pub fn value(&self) -> Option<Expr> {
                child(&self.0)
            }
        }
    )*};
}

binding!(LetStmt, VarStmt);

impl AssertStmt {
    /// The condition it asserts.
    #[must_use]
    pub fn expr(&self) -> Option<Expr> {
        child(&self.0)
    }
}

impl YieldStmt {
    /// The place yielded.
    #[must_use]
    pub fn expr(&self) -> Option<Expr> {
        child(&self.0)
    }
}

impl AssignStmt {
    /// The place it assigns to.
    #[must_use]
    pub fn place(&self) -> Option<Expr> {
        nth(&self.0, 0)
    }

    /// The assignment operator, `=` or a compound one such as `+=`.
    #[must_use]
    pub fn op(&self) -> Option<SyntaxToken> {
        tokens(&self.0).find(|t| !t.kind().is_trivia())
    }

    /// The value it assigns.
    #[must_use]
    pub fn value(&self) -> Option<Expr> {
        nth(&self.0, 1)
    }
}

impl ExprStmt {
    /// The expression.
    #[must_use]
    pub fn expr(&self) -> Option<Expr> {
        child(&self.0)
    }
}
