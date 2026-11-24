//! The views of patterns.

use super::{
    AstNode, MacroPat, Name, NameRef, Path, SpliceName, SplicePat, child, children, has, tokens,
};
use crate::SyntaxKind::{self, *};
use crate::{SyntaxNode, SyntaxToken};

nodes! {
    /// `_`.
    WildcardPat = WILDCARD_PAT,
    /// A binding.
    BindPat = BIND_PAT,
    /// A literal pattern.
    LiteralPat = LITERAL_PAT,
    /// A constant or a variant without a payload.
    PathPat = PATH_PAT,
    /// A variant with a payload.
    VariantPat = VARIANT_PAT,
    /// A record pattern.
    RecordPat = RECORD_PAT,
    /// A field of a record pattern.
    FieldPat = FIELD_PAT,
    /// The `..` of a record or list pattern.
    RestPat = REST_PAT,
    /// A tuple pattern.
    TuplePat = TUPLE_PAT,
    /// A pattern in parentheses.
    ParenPat = PAREN_PAT,
    /// A list pattern.
    ListPat = LIST_PAT,
    /// Alternatives.
    OrPat = OR_PAT,
}

enums! {
    /// A pattern.
    Pattern {
        WildcardPat, BindPat, LiteralPat, PathPat, VariantPat, RecordPat, TuplePat, ParenPat,
        ListPat, OrPat, MacroPat, SplicePat,
    }
}

impl BindPat {
    /// The name it binds.
    #[must_use]
    pub fn name(&self) -> Option<Name> {
        child(&self.0)
    }
}

impl LiteralPat {
    /// The literal's token.
    #[must_use]
    pub fn literal(&self) -> Option<SyntaxToken> {
        tokens(&self.0).find(|t| matches!(t.kind(), INT | STRING | TRUE_KW | FALSE_KW))
    }

    /// Whether the literal is a negative integer.
    #[must_use]
    pub fn is_negative(&self) -> bool {
        has(&self.0, MINUS)
    }
}

impl PathPat {
    /// The path of the constant or variant it matches.
    #[must_use]
    pub fn path(&self) -> Option<Path> {
        child(&self.0)
    }
}

impl VariantPat {
    /// The variant's path.
    #[must_use]
    pub fn path(&self) -> Option<Path> {
        child(&self.0)
    }

    /// The patterns of its payload, in order.
    pub fn patterns(&self) -> impl Iterator<Item = Pattern> + use<> {
        children(&self.0)
    }
}

impl RecordPat {
    /// The record type's path.
    #[must_use]
    pub fn path(&self) -> Option<Path> {
        child(&self.0)
    }

    /// The fields, in order.
    pub fn fields(&self) -> impl Iterator<Item = FieldPat> + use<> {
        children(&self.0)
    }

    /// Whether the pattern ends with `..`.
    #[must_use]
    pub fn has_rest(&self) -> bool {
        child::<RestPat>(&self.0).is_some()
    }
}

impl FieldPat {
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

    /// The pattern of the field, absent when the field binds a variable of its own name.
    #[must_use]
    pub fn pattern(&self) -> Option<Pattern> {
        child(&self.0)
    }
}

impl RestPat {
    /// The variable that binds the rest of a list.
    #[must_use]
    pub fn name(&self) -> Option<Name> {
        child(&self.0)
    }
}

impl TuplePat {
    /// The elements, in order.
    pub fn patterns(&self) -> impl Iterator<Item = Pattern> + use<> {
        children(&self.0)
    }
}

impl ParenPat {
    /// The pattern in the parentheses.
    #[must_use]
    pub fn pattern(&self) -> Option<Pattern> {
        child(&self.0)
    }
}

impl ListPat {
    /// The elements, in order.
    pub fn patterns(&self) -> impl Iterator<Item = Pattern> + use<> {
        children(&self.0)
    }

    /// Its `..` rest, with the name that binds it.
    #[must_use]
    pub fn rest(&self) -> Option<RestPat> {
        child(&self.0)
    }
}

impl OrPat {
    /// The alternatives, in order.
    pub fn patterns(&self) -> impl Iterator<Item = Pattern> + use<> {
        children(&self.0)
    }
}
