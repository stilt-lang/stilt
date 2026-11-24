//! The views of control flow: `try` and its `catch`, `raise`, `return`, `break`, `continue`,
//! `if`, `match` and the loops.

use super::{AstNode, Block, Expr, Pattern, after, child, children, has, nth, token};
use crate::SyntaxKind::{self, *};
use crate::{SyntaxNode, SyntaxToken};

nodes! {
    /// `try`, perhaps with a `catch`.
    TryExpr = TRY_EXPR,
    /// The `catch` of a `try`.
    CatchClause = CATCH_CLAUSE,
    /// An arm of a `match` or a `catch`.
    Arm = ARM,
    /// The guard of an arm.
    Guard = GUARD,
    /// The reason of a catch-all.
    Because = BECAUSE,
    /// `raise`.
    RaiseExpr = RAISE_EXPR,
    /// `return`.
    ReturnExpr = RETURN_EXPR,
    /// `break`.
    BreakExpr = BREAK_EXPR,
    /// `continue`.
    ContinueExpr = CONTINUE_EXPR,
    /// `if`.
    IfExpr = IF_EXPR,
    /// The condition of an `if` that tests a type parameter's bounds, `T: Show` (meta.bound-tests,
    /// meta.bound-tests).
    BoundTest = BOUND_TEST,
    /// `match`.
    MatchExpr = MATCH_EXPR,
    /// `loop`.
    LoopExpr = LOOP_EXPR,
    /// `while`.
    WhileExpr = WHILE_EXPR,
    /// `for`.
    ForExpr = FOR_EXPR,
    /// The range a `for` iterates over.
    Range = RANGE,
    /// A staging annotation, `comptime` before an `if`, a `match` or a `for`
    /// (meta.staging-annotations).
    ComptimeExpr = COMPTIME_EXPR,
    /// `unsafe because "reason" { … }` (c.unsafe-because).
    UnsafeExpr = UNSAFE_EXPR,
}

/// What a `for` iterates over: a range, or an expression.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Iterable {
    #[allow(missing_docs)]
    Range(Range),
    #[allow(missing_docs)]
    Expr(Expr),
}

impl AstNode for Iterable {
    fn cast(node: SyntaxNode) -> Option<Self> {
        Range::cast(node.clone())
            .map(Self::Range)
            .or_else(|| Expr::cast(node).map(Self::Expr))
    }

    fn syntax(&self) -> &SyntaxNode {
        match self {
            Self::Range(n) => n.syntax(),
            Self::Expr(n) => n.syntax(),
        }
    }
}

impl UnsafeExpr {
    /// The `unsafe` keyword.
    #[must_use]
    pub fn unsafe_token(&self) -> Option<SyntaxToken> {
        token(&self.0, UNSAFE_KW)
    }

    /// The reason after `because`, a string literal.
    #[must_use]
    pub fn reason(&self) -> Option<SyntaxToken> {
        child::<Because>(&self.0).and_then(|b| b.reason())
    }

    /// The block it marks.
    #[must_use]
    pub fn body(&self) -> Option<Block> {
        child(&self.0)
    }
}

impl ComptimeExpr {
    /// The form it annotates: an `if`, a `match` or a `for`.
    #[must_use]
    pub fn form(&self) -> Option<Expr> {
        child(&self.0)
    }

    /// The `comptime` keyword.
    #[must_use]
    pub fn comptime_token(&self) -> Option<SyntaxToken> {
        token(&self.0, COMPTIME_KW)
    }
}

impl TryExpr {
    /// The expression it tries.
    #[must_use]
    pub fn expr(&self) -> Option<Expr> {
        child(&self.0)
    }

    /// Its `catch` and the arms that follow it.
    #[must_use]
    pub fn catch_clause(&self) -> Option<CatchClause> {
        child(&self.0)
    }
}

impl CatchClause {
    /// The arms, in order.
    pub fn arms(&self) -> impl Iterator<Item = Arm> + use<> {
        children(&self.0)
    }
}

impl Arm {
    /// The pattern it matches.
    #[must_use]
    pub fn pattern(&self) -> Option<Pattern> {
        child(&self.0)
    }

    /// Its `if` guard.
    #[must_use]
    pub fn guard(&self) -> Option<Guard> {
        child(&self.0)
    }

    /// Its `because` and the reason it gives.
    #[must_use]
    pub fn because(&self) -> Option<Because> {
        child(&self.0)
    }

    /// The expression after `=>`.
    #[must_use]
    pub fn body(&self) -> Option<Expr> {
        child(&self.0)
    }
}

impl Guard {
    /// The condition after `if`.
    #[must_use]
    pub fn expr(&self) -> Option<Expr> {
        child(&self.0)
    }
}

impl Because {
    /// The reason, a string literal.
    #[must_use]
    pub fn reason(&self) -> Option<SyntaxToken> {
        token(&self.0, STRING)
    }
}

impl RaiseExpr {
    /// The value it raises.
    #[must_use]
    pub fn expr(&self) -> Option<Expr> {
        child(&self.0)
    }
}

impl ReturnExpr {
    /// The value it returns, if it is written.
    #[must_use]
    pub fn expr(&self) -> Option<Expr> {
        child(&self.0)
    }
}

impl IfExpr {
    /// Whether it is an `if let` (expressions.if-let).
    #[must_use]
    pub fn is_let(&self) -> bool {
        has(&self.0, LET_KW)
    }

    /// The pattern of an `if let`.
    #[must_use]
    pub fn pattern(&self) -> Option<Pattern> {
        child(&self.0)
    }

    /// The condition of an `if`, or the expression an `if let` matches; none for a bound test.
    #[must_use]
    pub fn condition(&self) -> Option<Expr> {
        if self.bound_test().is_some() {
            return None;
        }
        nth(&self.0, 0)
    }

    /// The bound test that is the condition, if it is one (meta.bound-tests).
    #[must_use]
    pub fn bound_test(&self) -> Option<BoundTest> {
        child(&self.0)
    }

    /// The block that runs when the condition holds.
    #[must_use]
    pub fn then_block(&self) -> Option<Block> {
        let at = usize::from(self.bound_test().is_none());
        nth::<Expr>(&self.0, at).and_then(|e| match e {
            Expr::Block(block) => Some(block),
            _ => None,
        })
    }

    /// What follows `else`: a block or another `if`.
    #[must_use]
    pub fn else_branch(&self) -> Option<Expr> {
        after(&self.0, ELSE_KW)
    }
}

impl BoundTest {
    /// The type parameter tested.
    #[must_use]
    pub fn name(&self) -> Option<super::Name> {
        child(&self.0)
    }

    /// Its bounds, as a generic writes them.
    pub fn bounds(&self) -> impl Iterator<Item = super::Bound> + use<> {
        child::<super::BoundList>(&self.0)
            .into_iter()
            .flat_map(|bounds| children(&bounds.0))
    }
}

impl MatchExpr {
    /// The value it matches.
    #[must_use]
    pub fn scrutinee(&self) -> Option<Expr> {
        child(&self.0)
    }

    /// The arms, in order.
    pub fn arms(&self) -> impl Iterator<Item = Arm> + use<> {
        children(&self.0)
    }
}

impl LoopExpr {
    /// The block it repeats.
    #[must_use]
    pub fn body(&self) -> Option<Block> {
        child(&self.0)
    }
}

// The condition of a `while` and the iterable of a `for` are heads, which hold no block of
// their own (expressions.heads), so the loop's body is its last block.

impl WhileExpr {
    /// The condition checked before each turn.
    #[must_use]
    pub fn condition(&self) -> Option<Expr> {
        nth(&self.0, 0)
    }

    /// The block it repeats.
    #[must_use]
    pub fn body(&self) -> Option<Block> {
        children(&self.0).last()
    }
}

impl ForExpr {
    /// The pattern that each element binds.
    #[must_use]
    pub fn pattern(&self) -> Option<Pattern> {
        child(&self.0)
    }

    /// What follows `in`: an expression or a range.
    #[must_use]
    pub fn iterable(&self) -> Option<Iterable> {
        after(&self.0, IN_KW)
    }

    /// The block it runs for each element.
    #[must_use]
    pub fn body(&self) -> Option<Block> {
        children(&self.0).last()
    }
}

impl Range {
    /// The bound before `..`.
    #[must_use]
    pub fn start(&self) -> Option<Expr> {
        nth(&self.0, 0)
    }

    /// The bound after `..` or `..=`.
    #[must_use]
    pub fn end(&self) -> Option<Expr> {
        nth(&self.0, 1)
    }

    /// Whether the range includes its end: `..=`.
    #[must_use]
    pub fn is_inclusive(&self) -> bool {
        has(&self.0, DOT2EQ)
    }
}
