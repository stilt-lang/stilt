//! The views of effects and handlers (handlers.declaring-effect and handlers.handler-literals;
//! tasks.async): an effect's declaration and its operations, the effects of rows, handler types and
//! literals, `with` and `resume`.

use super::{
    AstNode, Block, Docs, Expr, Fn, GenericList, NameRef, NamedType, Param, ParamList, Path,
    RetType, Row, Type, TypeArgList, TypeParam, child, children, has, token,
};
use crate::SyntaxKind::{self, *};
use crate::{SyntaxNode, SyntaxToken};

nodes! {
    /// An effect's declaration (handlers.declaring-effect).
    Effect = EFFECT,
    /// An operation of an effect.
    Operation = OPERATION,
    /// An effect in a row, as `Prices` or `State<i64>` (handlers.effects-in-rows).
    RowEffect = ROW_EFFECT,
    /// `async` in a row, or as the effect of a handler (tasks.async).
    RowAsync = ROW_ASYNC,
    /// A handler's type, `handler E -> R / row` (handlers.handler-types).
    HandlerType = HANDLER_TYPE,
    /// A handler literal (handlers.handler-literals).
    HandlerExpr = HANDLER_EXPR,
    /// `with h₁, h₂ { … }` (handlers.with).
    WithExpr = WITH_EXPR,
    /// `resume(v)` (handlers.resuming).
    ResumeExpr = RESUME_EXPR,
    /// `when a, b { … }` (shared.when).
    WhenExpr = WHEN_EXPR,
}

impl Effect {
    /// The doc comments before the declaration.
    #[must_use]
    pub fn docs(&self) -> Option<Docs> {
        child(&self.0)
    }

    /// Whether the declaration is written `pub`.
    #[must_use]
    pub fn is_pub(&self) -> bool {
        has(&self.0, PUB_KW)
    }

    /// The effect's name.
    #[must_use]
    pub fn name(&self) -> Option<super::Name> {
        child(&self.0)
    }

    /// The effect's type parameters.
    pub fn params(&self) -> impl Iterator<Item = TypeParam> + use<> {
        child::<GenericList>(&self.0)
            .into_iter()
            .flat_map(|list| children(&list.0))
    }

    /// The operations it declares, in order.
    pub fn operations(&self) -> impl Iterator<Item = Operation> + use<> {
        children(&self.0)
    }
}

impl Operation {
    /// The doc comments above the operation.
    #[must_use]
    pub fn docs(&self) -> Option<Docs> {
        child(&self.0)
    }

    /// The operation's name.
    #[must_use]
    pub fn name(&self) -> Option<super::Name> {
        child(&self.0)
    }

    /// Its parameters, in parentheses.
    #[must_use]
    pub fn param_list(&self) -> Option<ParamList> {
        child(&self.0)
    }

    /// Its parameters, in order.
    pub fn params(&self) -> impl Iterator<Item = Param> + use<> {
        self.param_list().into_iter().flat_map(|l| l.params())
    }

    /// The `->` and the result type.
    #[must_use]
    pub fn ret_type(&self) -> Option<RetType> {
        child(&self.0)
    }

    /// The row after `/`.
    #[must_use]
    pub fn row(&self) -> Option<Row> {
        child(&self.0)
    }
}

impl RowEffect {
    /// The effect's path.
    #[must_use]
    pub fn path(&self) -> Option<Path> {
        child(&self.0)
    }

    /// The effect's type arguments, in order.
    pub fn args(&self) -> impl Iterator<Item = Type> + use<> {
        child::<TypeArgList>(&self.0)
            .into_iter()
            .flat_map(|list| children(&list.0))
    }
}

impl RowAsync {
    /// The `async` keyword.
    #[must_use]
    pub fn token(&self) -> Option<SyntaxToken> {
        token(&self.0, ASYNC_KW)
    }
}

/// The effect a handler type or literal names.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum EffectRef {
    /// A path to an effect, with its type arguments.
    Named(NamedType),
    /// `async`, which only `std.task` gives handlers of (tasks.async).
    Async(RowAsync),
}

impl EffectRef {
    /// The node that names the effect.
    #[must_use]
    pub fn syntax(&self) -> &SyntaxNode {
        match self {
            Self::Named(n) => n.syntax(),
            Self::Async(a) => a.syntax(),
        }
    }
}

fn effect_ref(node: &SyntaxNode) -> Option<EffectRef> {
    node.children().find_map(|n| {
        NamedType::cast(n.clone())
            .map(EffectRef::Named)
            .or_else(|| RowAsync::cast(n).map(EffectRef::Async))
    })
}

impl HandlerType {
    /// The effect it handles, with its type arguments.
    #[must_use]
    pub fn effect(&self) -> Option<EffectRef> {
        effect_ref(&self.0)
    }

    /// The result `R` of a handler that takes control.
    #[must_use]
    pub fn answer(&self) -> Option<RetType> {
        child(&self.0)
    }

    /// The row after `/`, which its operations' bodies may perform.
    #[must_use]
    pub fn row(&self) -> Option<Row> {
        child(&self.0)
    }
}

impl HandlerExpr {
    /// The effect it handles, with its type arguments.
    #[must_use]
    pub fn effect(&self) -> Option<EffectRef> {
        effect_ref(&self.0)
    }

    /// The result `R` of a handler that takes control.
    #[must_use]
    pub fn answer(&self) -> Option<RetType> {
        child(&self.0)
    }

    /// The operations it implements, each a function.
    pub fn fns(&self) -> impl Iterator<Item = Fn> + use<> {
        children(&self.0)
    }
}

impl WithExpr {
    /// The handlers, each a head, which is never a block.
    pub fn handlers(&self) -> impl Iterator<Item = Expr> + use<> {
        children(&self.0).filter(|e| !matches!(e, Expr::Block(_)))
    }

    /// The block that runs under the handlers.
    #[must_use]
    pub fn body(&self) -> Option<Block> {
        child(&self.0)
    }
}

impl WhenExpr {
    /// The names it holds, in order.
    pub fn names(&self) -> impl Iterator<Item = NameRef> + use<> {
        children(&self.0)
    }

    /// The block that runs while it holds the names.
    #[must_use]
    pub fn body(&self) -> Option<Block> {
        child(&self.0)
    }
}

impl ResumeExpr {
    /// The value it resumes the operation with, if it is written.
    #[must_use]
    pub fn expr(&self) -> Option<Expr> {
        child(&self.0)
    }
}
