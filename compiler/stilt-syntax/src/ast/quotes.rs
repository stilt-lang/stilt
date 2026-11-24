//! The views of procedural macros' forms (macros.quote and macros.splices): quotes and their
//! splices, and a use where a type stands.

use super::{AstNode, Block, Expr, FieldInit, MacroGroup, NameRef, Path, Pattern, Type, child};
use crate::SyntaxKind::{self, *};
use crate::{SyntaxNode, SyntaxToken};

nodes! {
    /// A quote: `quote { … }`, `quote type { … }`, `quote pattern { … }` or
    /// `quote field { … }` (macros.quote).
    QuoteExpr = QUOTE_EXPR,
    /// A splice where an expression stands, `$x` or `$(e)` (macros.splices).
    SpliceExpr = SPLICE_EXPR,
    /// A splice where a pattern stands.
    SplicePat = SPLICE_PAT,
    /// A splice where a type stands.
    SpliceType = SPLICE_TYPE,
    /// A splice where a field or a member is named.
    SpliceName = SPLICE_NAME,
    /// A spread among the elements of a list, a tuple or a call's arguments, or among a record
    /// literal's fields, `$..x` or `$..(e)`.
    SpliceSpread = SPLICE_SPREAD,
    /// A use of a procedural macro where a type stands (macros.procedural-uses).
    MacroType = MACRO_TYPE,
}

/// The form a quote writes (macros.quote).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum QuoteForm {
    /// `quote { … }`, a block's statements, whose code is that block.
    Block,
    /// `quote type { … }`, a type.
    Type,
    /// `quote pattern { … }`, a pattern.
    Pattern,
    /// `quote field { … }`, one field of a record literal.
    Field,
}

impl QuoteExpr {
    /// The form the quote writes, by the word after `quote`.
    #[must_use]
    pub fn form(&self) -> QuoteForm {
        let word = self
            .0
            .children_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            .map(|t| t.kind())
            .find(|k| matches!(k, TYPE_KW | PATTERN_KW | FIELD_KW));
        match word {
            Some(TYPE_KW) => QuoteForm::Type,
            Some(PATTERN_KW) => QuoteForm::Pattern,
            Some(FIELD_KW) => QuoteForm::Field,
            _ => QuoteForm::Block,
        }
    }

    /// The block of `quote { … }`.
    #[must_use]
    pub fn block(&self) -> Option<Block> {
        child(&self.0)
    }

    /// The type of `quote type { … }`.
    #[must_use]
    pub fn ty(&self) -> Option<Type> {
        child(&self.0)
    }

    /// The pattern of `quote pattern { … }`.
    #[must_use]
    pub fn pattern(&self) -> Option<Pattern> {
        child(&self.0)
    }

    /// The field of `quote field { … }`, or the spread it holds.
    #[must_use]
    pub fn field(&self) -> Option<FieldInit> {
        child(&self.0)
    }

    /// The spread of `quote field { $..fs }`.
    #[must_use]
    pub fn spread(&self) -> Option<SpliceSpread> {
        child(&self.0)
    }

    /// The brackets that hold the quote's contents: its block's, or those after its word.
    #[must_use]
    pub fn brackets(&self) -> Option<(SyntaxToken, SyntaxToken)> {
        let holder = match self.block() {
            Some(b) => b.syntax().clone(),
            None => self.0.clone(),
        };
        let mut tokens = holder
            .children_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token);
        let open = tokens.find(|t| t.kind() == L_CURLY)?;
        let close = tokens.filter(|t| t.kind() == R_CURLY).last()?;
        Some((open, close))
    }
}

/// What a splice names: a variable of the macro's code, or an expression of it in parentheses.
fn spliced(node: &SyntaxNode) -> Option<Expr> {
    child(node)
}

impl SpliceExpr {
    /// The expression of the macro's code that the splice holds: its variable, or the
    /// expression in its parentheses.
    #[must_use]
    pub fn value(&self) -> Option<Expr> {
        spliced(&self.0)
    }
}

impl SplicePat {
    /// The expression after `$`.
    #[must_use]
    pub fn value(&self) -> Option<Expr> {
        spliced(&self.0)
    }
}

impl SpliceType {
    /// The expression after `$`.
    #[must_use]
    pub fn value(&self) -> Option<Expr> {
        spliced(&self.0)
    }
}

impl SpliceName {
    /// The expression after `$`.
    #[must_use]
    pub fn value(&self) -> Option<Expr> {
        spliced(&self.0)
    }
}

impl SpliceSpread {
    /// The expression after `$..`.
    #[must_use]
    pub fn value(&self) -> Option<Expr> {
        spliced(&self.0)
    }
}

/// A splice of any place, with the value it holds.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AnySplice {
    /// A splice where an expression goes.
    Expr(SpliceExpr),
    /// A splice where a pattern goes.
    Pat(SplicePat),
    /// A splice where a type goes.
    Type(SpliceType),
    /// A splice where a name goes.
    Name(SpliceName),
    /// A spread, `$..x`.
    Spread(SpliceSpread),
}

impl AnySplice {
    /// The splice a node is, if it is one.
    #[must_use]
    pub fn cast(node: SyntaxNode) -> Option<Self> {
        Some(match node.kind() {
            SPLICE_EXPR => Self::Expr(SpliceExpr(node)),
            SPLICE_PAT => Self::Pat(SplicePat(node)),
            SPLICE_TYPE => Self::Type(SpliceType(node)),
            SPLICE_NAME => Self::Name(SpliceName(node)),
            SPLICE_SPREAD => Self::Spread(SpliceSpread(node)),
            _ => return None,
        })
    }

    /// The splice's node.
    #[must_use]
    pub fn syntax(&self) -> &SyntaxNode {
        match self {
            Self::Expr(s) => s.syntax(),
            Self::Pat(s) => s.syntax(),
            Self::Type(s) => s.syntax(),
            Self::Name(s) => s.syntax(),
            Self::Spread(s) => s.syntax(),
        }
    }

    /// The expression of the macro's code that the splice holds.
    #[must_use]
    pub fn value(&self) -> Option<Expr> {
        spliced(self.syntax())
    }

    /// The variable the splice names, when it is written `$x`.
    #[must_use]
    pub fn name(&self) -> Option<NameRef> {
        child(self.syntax())
    }

    /// The kind of the splice's node.
    #[must_use]
    pub fn kind(&self) -> SyntaxKind {
        self.syntax().kind()
    }
}

impl MacroType {
    /// The macro's path.
    #[must_use]
    pub fn path(&self) -> Option<Path> {
        child(&self.0)
    }

    /// Its tokens, in brackets.
    #[must_use]
    pub fn group(&self) -> Option<MacroGroup> {
        child(&self.0)
    }
}
