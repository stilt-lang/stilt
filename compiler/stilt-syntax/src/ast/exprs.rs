//! The views of expressions, but for those of control flow.

use super::{
    AstNode, Block, BreakExpr, ComptimeExpr, ContinueExpr, ForExpr, HandlerExpr, IfExpr, LoopExpr,
    MacroUse, MatchExpr, NameRef, Path, Pattern, QuoteExpr, RaiseExpr, ResumeExpr, ReturnExpr,
    SpliceExpr, SpliceName, SpliceSpread, TryExpr, Type, UnsafeExpr, WhenExpr, WhileExpr, WithExpr,
    child, children, has, nth, token, tokens,
};
use crate::SyntaxKind::{self, *};
use crate::{SyntaxNode, SyntaxToken, text};

nodes! {
    /// A literal.
    Literal = LITERAL,
    /// An interpolated string.
    Interp = INTERP,
    /// An interpolation of an interpolated string.
    Splice = SPLICE,
    /// `self`.
    SelfExpr = SELF_EXPR,
    /// `Self`.
    SelfTypeExpr = SELF_TYPE_EXPR,
    /// A hole, `?`.
    HoleExpr = HOLE_EXPR,
    /// The start of a key path: `.name`.
    KeyPathExpr = KEY_PATH_EXPR,
    /// An expression in parentheses.
    ParenExpr = PAREN_EXPR,
    /// A tuple.
    TupleExpr = TUPLE_EXPR,
    /// A list.
    ListExpr = LIST_EXPR,
    /// A field.
    FieldExpr = FIELD_EXPR,
    /// A call.
    CallExpr = CALL_EXPR,
    /// The arguments of a call.
    ArgList = ARG_LIST,
    /// An argument.
    Arg = ARG,
    /// An index.
    IndexExpr = INDEX_EXPR,
    /// A struct literal.
    StructExpr = STRUCT_EXPR,
    /// An anonymous record literal, or an update of an anonymous or bounded record
    /// (records.anonymous-literals and records.update).
    RecordExpr = RECORD_EXPR,
    /// A spread, `..e`: of pack tuples (variadics.spread-expressions), or an update's base
    /// (records.update).
    SpreadExpr = SPREAD_EXPR,
    /// A field of a struct literal.
    FieldInit = FIELD_INIT,
    /// `-e` or `!e`.
    PrefixExpr = PREFIX_EXPR,
    /// A binary operator.
    BinaryExpr = BINARY_EXPR,
    /// `a else b`.
    ElseExpr = ELSE_EXPR,
    /// A closure.
    ClosureExpr = CLOSURE_EXPR,
    /// A parameter of a closure.
    ClosureParam = CLOSURE_PARAM,
}

enums! {
    /// An expression.
    Expr {
        Literal, Interp, NameRef, SelfExpr, SelfTypeExpr, HoleExpr, KeyPathExpr, ParenExpr,
        TupleExpr, ListExpr, FieldExpr, CallExpr, IndexExpr, StructExpr, RecordExpr, SpreadExpr,
        PrefixExpr, BinaryExpr,
        ElseExpr, TryExpr, RaiseExpr, ReturnExpr, BreakExpr, ContinueExpr, ClosureExpr, Block,
        IfExpr, MatchExpr, LoopExpr, WhileExpr, ForExpr, MacroUse, HandlerExpr, WithExpr,
        ResumeExpr, WhenExpr, ComptimeExpr, UnsafeExpr, QuoteExpr, SpliceExpr, SpliceSpread,
    }
}

impl Literal {
    /// The literal's token.
    #[must_use]
    pub fn token(&self) -> Option<SyntaxToken> {
        tokens(&self.0).find(|t| !t.kind().is_trivia())
    }
}

/// A part of an interpolated string.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InterpPart {
    /// Text, its escapes resolved.
    Text(String),
    /// An interpolation.
    Splice(Splice),
}

impl Interp {
    /// The parts, in order. Text parts may be empty.
    #[must_use]
    pub fn parts(&self) -> Vec<InterpPart> {
        self.0
            .children_with_tokens()
            .filter_map(|element| match element {
                rowan::NodeOrToken::Token(t)
                    if matches!(t.kind(), STRING_HEAD | STRING_MID | STRING_TAIL) =>
                {
                    Some(InterpPart::Text(text::string_value(&t)))
                }
                rowan::NodeOrToken::Node(n) => Splice::cast(n).map(InterpPart::Splice),
                rowan::NodeOrToken::Token(_) => None,
            })
            .collect()
    }
}

impl Splice {
    /// The interpolated expression.
    #[must_use]
    pub fn expr(&self) -> Option<Expr> {
        child(&self.0)
    }

    /// The format spec, without its `:`.
    #[must_use]
    pub fn spec(&self) -> Option<String> {
        token(&self.0, FORMAT).map(|t| t.text()[1..].to_owned())
    }
}

impl KeyPathExpr {
    /// The field after the `.`.
    #[must_use]
    pub fn member(&self) -> Option<SyntaxToken> {
        tokens(&self.0).find(|t| matches!(t.kind(), LOWER_IDENT | INT))
    }
}

impl ParenExpr {
    /// The expression in the parentheses.
    #[must_use]
    pub fn expr(&self) -> Option<Expr> {
        child(&self.0)
    }
}

impl TupleExpr {
    /// The elements, in order.
    pub fn exprs(&self) -> impl Iterator<Item = Expr> + use<> {
        children(&self.0)
    }
}

impl ListExpr {
    /// The elements, in order.
    pub fn exprs(&self) -> impl Iterator<Item = Expr> + use<> {
        children(&self.0)
    }
}

impl FieldExpr {
    /// The expression before the `.`.
    #[must_use]
    pub fn base(&self) -> Option<Expr> {
        child(&self.0)
    }

    /// The field's name, or its index in a tuple.
    #[must_use]
    pub fn member(&self) -> Option<SyntaxToken> {
        tokens(&self.0)
            .skip_while(|t| t.kind() != DOT)
            .find(|t| matches!(t.kind(), LOWER_IDENT | UPPER_IDENT | INT | AWAIT_KW))
    }

    /// The splice that names the member, in a quote (macros.splices).
    #[must_use]
    pub fn splice(&self) -> Option<SpliceName> {
        child(&self.0)
    }
}

impl CallExpr {
    /// The expression called.
    #[must_use]
    pub fn callee(&self) -> Option<Expr> {
        child(&self.0)
    }

    /// The arguments, in order.
    pub fn args(&self) -> impl Iterator<Item = Arg> + use<> {
        child::<ArgList>(&self.0)
            .into_iter()
            .flat_map(|list| children(&list.0))
    }
}

impl Arg {
    /// Whether the argument is written `inout`.
    #[must_use]
    pub fn is_inout(&self) -> bool {
        has(&self.0, INOUT_KW)
    }

    /// The argument's expression.
    #[must_use]
    pub fn expr(&self) -> Option<Expr> {
        child(&self.0)
    }
}

impl IndexExpr {
    /// The expression indexed.
    #[must_use]
    pub fn base(&self) -> Option<Expr> {
        nth(&self.0, 0)
    }

    /// The index, in the brackets.
    #[must_use]
    pub fn index(&self) -> Option<Expr> {
        nth(&self.0, 1)
    }
}

impl StructExpr {
    /// The record type's path.
    #[must_use]
    pub fn path(&self) -> Option<Path> {
        child(&self.0)
    }

    /// The base of an update, `..base` (records.update).
    #[must_use]
    pub fn base(&self) -> Option<SpreadExpr> {
        child(&self.0)
    }

    /// The fields, in order.
    pub fn fields(&self) -> impl Iterator<Item = FieldInit> + use<> {
        children(&self.0)
    }

    /// The spreads of fields among its fields, in a quote (macros.spreads).
    pub fn spreads(&self) -> impl Iterator<Item = SpliceSpread> + use<> {
        children(&self.0)
    }
}

impl RecordExpr {
    /// The base of an update, `..base` (records.update).
    #[must_use]
    pub fn base(&self) -> Option<SpreadExpr> {
        child(&self.0)
    }

    /// The fields, in order.
    pub fn fields(&self) -> impl Iterator<Item = FieldInit> + use<> {
        children(&self.0)
    }

    /// The spreads of fields among its fields, in a quote (macros.spreads).
    pub fn spreads(&self) -> impl Iterator<Item = SpliceSpread> + use<> {
        children(&self.0)
    }
}

impl SpreadExpr {
    /// The expression after `..`.
    #[must_use]
    pub fn expr(&self) -> Option<Expr> {
        child(&self.0)
    }
}

impl FieldInit {
    /// The field's name.
    #[must_use]
    pub fn field(&self) -> Option<NameRef> {
        child(&self.0)
    }

    /// The splice that names the field, in a quote (macros.splices).
    #[must_use]
    pub fn splice(&self) -> Option<SpliceName> {
        child(&self.0)
    }

    /// The field's value, absent when it is the variable of the field's name.
    #[must_use]
    pub fn value(&self) -> Option<Expr> {
        if self.splice().is_some() {
            child(&self.0)
        } else {
            nth(&self.0, 1)
        }
    }
}

impl PrefixExpr {
    /// `-` or `!`.
    #[must_use]
    pub fn op(&self) -> Option<SyntaxToken> {
        tokens(&self.0).find(|t| !t.kind().is_trivia())
    }

    /// The operand.
    #[must_use]
    pub fn expr(&self) -> Option<Expr> {
        child(&self.0)
    }
}

impl BinaryExpr {
    /// The left operand.
    #[must_use]
    pub fn lhs(&self) -> Option<Expr> {
        nth(&self.0, 0)
    }

    /// The operator.
    #[must_use]
    pub fn op(&self) -> Option<SyntaxToken> {
        tokens(&self.0).find(|t| !t.kind().is_trivia())
    }

    /// The right operand.
    #[must_use]
    pub fn rhs(&self) -> Option<Expr> {
        nth(&self.0, 1)
    }
}

impl ElseExpr {
    /// The value before `else`.
    #[must_use]
    pub fn lhs(&self) -> Option<Expr> {
        nth(&self.0, 0)
    }

    /// The value after `else`.
    #[must_use]
    pub fn rhs(&self) -> Option<Expr> {
        nth(&self.0, 1)
    }
}

impl ClosureExpr {
    /// The parameters, in order.
    pub fn params(&self) -> impl Iterator<Item = ClosureParam> + use<> {
        children(&self.0)
    }

    /// The body, after `=>`.
    #[must_use]
    pub fn body(&self) -> Option<Expr> {
        child(&self.0)
    }
}

impl ClosureParam {
    /// Whether the parameter is marked `inout`, which makes its pattern a name
    /// (expressions.inout-closure-parameters and expressions.closures and
    /// expressions.closure-parameter-types).
    #[must_use]
    pub fn is_inout(&self) -> bool {
        has(&self.0, INOUT_KW)
    }

    /// The pattern the parameter binds.
    #[must_use]
    pub fn pattern(&self) -> Option<Pattern> {
        child(&self.0)
    }

    /// The parameter's written type.
    #[must_use]
    pub fn ty(&self) -> Option<Type> {
        child(&self.0)
    }
}
