//! The views of generics: the lists of type parameters, row variables and value parameters that
//! functions, types, traits and impls declare, their bounds, and `where` clauses.

use super::{AstNode, Name, Path, RecordType, Type, TypeArgList, child, children, has, token};
use crate::SyntaxKind::{self, *};
use crate::{SyntaxNode, SyntaxToken};

nodes! {
    /// A list of generics or type parameters.
    GenericList = GENERIC_LIST,
    /// A type parameter, with its bounds.
    TypeParam = TYPE_PARAM,
    /// A row variable that a function declares.
    RowParam = ROW_PARAM,
    /// A value parameter, `n: T` (generics.value-parameters).
    ValueParam = VALUE_PARAM,
    /// The bounds of a type parameter or of a member type.
    BoundList = BOUND_LIST,
    /// A trait as a bound, with its arguments if it is given them (traits.bound-arguments).
    Bound = BOUND,
    /// A `where` clause (traits.where).
    WhereClause = WHERE_CLAUSE,
    /// A member type and its bounds, in a `where` clause.
    WhereBound = WHERE_BOUND,
}

enums! {
    /// A generic: a type parameter, a row variable or a value parameter.
    Generic { TypeParam, RowParam, ValueParam, }
}

impl GenericList {
    /// The parameters, in order.
    pub fn generics(&self) -> impl Iterator<Item = Generic> + use<> {
        children(&self.0)
    }
}

impl TypeParam {
    /// The parameter's name.
    #[must_use]
    pub fn name(&self) -> Option<Name> {
        child(&self.0)
    }

    /// The bounds: traits, each with its arguments if it is given them, and record bounds.
    pub fn bounds(&self) -> impl Iterator<Item = Bound> + use<> {
        child::<BoundList>(&self.0)
            .into_iter()
            .flat_map(|bounds| children(&bounds.0))
    }

    /// Whether it is a pack, `..Ts` (variadics.packs).
    #[must_use]
    pub fn is_pack(&self) -> bool {
        has(&self.0, DOT2)
    }
}

impl Bound {
    /// The record type of a record bound (records.record-bounds).
    #[must_use]
    pub fn record(&self) -> Option<RecordType> {
        child(&self.0)
    }

    /// The path to the trait.
    #[must_use]
    pub fn path(&self) -> Option<Path> {
        child(&self.0)
    }

    /// The trait's arguments, none when it is given none.
    pub fn args(&self) -> impl Iterator<Item = Type> + use<> {
        child::<TypeArgList>(&self.0)
            .into_iter()
            .flat_map(|list| children(&list.0))
    }

    /// Whether the trait is written with arguments.
    #[must_use]
    pub fn has_args(&self) -> bool {
        child::<TypeArgList>(&self.0).is_some()
    }
}

impl WhereClause {
    /// The `where` keyword.
    #[must_use]
    pub fn where_token(&self) -> Option<SyntaxToken> {
        token(&self.0, WHERE_KW)
    }

    /// The bounds, in order.
    pub fn bounds(&self) -> impl Iterator<Item = WhereBound> + use<> {
        children(&self.0)
    }
}

impl WhereBound {
    /// The member type's path, as `C.Item`.
    #[must_use]
    pub fn path(&self) -> Option<Path> {
        child(&self.0)
    }

    /// The bounds after `:`, in order.
    pub fn bounds(&self) -> impl Iterator<Item = Bound> + use<> {
        child::<BoundList>(&self.0)
            .into_iter()
            .flat_map(|bounds| children(&bounds.0))
    }
}

impl RowParam {
    /// The row parameter's name.
    #[must_use]
    pub fn name(&self) -> Option<Name> {
        child(&self.0)
    }
}

impl Generic {
    /// The generic's name.
    #[must_use]
    pub fn name(&self) -> Option<Name> {
        match self {
            Generic::TypeParam(p) => p.name(),
            Generic::RowParam(p) => p.name(),
            Generic::ValueParam(p) => p.name(),
        }
    }

    /// Whether it is a pack, `..Ts` (variadics.packs).
    #[must_use]
    pub fn is_pack(&self) -> bool {
        matches!(self, Generic::TypeParam(p) if p.is_pack())
    }
}

impl ValueParam {
    /// The value parameter's name.
    #[must_use]
    pub fn name(&self) -> Option<Name> {
        child(&self.0)
    }

    /// The parameter's type, which is checked after parsing (generics.value-parameters).
    #[must_use]
    pub fn ty(&self) -> Option<Type> {
        child(&self.0)
    }
}
