//! The views of types and rows.

use super::{
    AstNode, FieldDef, GenericList, HandlerType, MacroType, Mode, Path, RetType, RowAsync,
    RowEffect, SpliceType, child, children, mode, token,
};
use crate::SyntaxKind::{self, *};
use crate::{SyntaxNode, SyntaxToken};

nodes! {
    /// A type named by a path, perhaps with type arguments.
    NamedType = NAMED_TYPE,
    /// Type arguments.
    TypeArgList = TYPE_ARG_LIST,
    /// A literal value argument, as the `7` of `Mod<7>` (generics.value-arguments).
    ValueArg = VALUE_ARG,
    /// A tuple type.
    TupleType = TUPLE_TYPE,
    /// A type in parentheses.
    ParenType = PAREN_TYPE,
    /// An anonymous record type, or an open one (records.anonymous-types and
    /// records.open-parameter-types).
    RecordType = RECORD_TYPE,
    /// A spread of a pack, `..T` (variadics.type-spreads).
    SpreadType = SPREAD_TYPE,
    /// A function type.
    FnType = FN_TYPE,
    /// The parameter types of a function type.
    ParamTypeList = PARAM_TYPE_LIST,
    /// A parameter type of a function type.
    ParamType = PARAM_TYPE,
    /// A row of effects.
    Row = ROW,
    /// The `io` of a row.
    RowIo = ROW_IO,
    /// The `raise<E>` of a row.
    RowRaise = ROW_RAISE,
    /// A row variable in a row.
    RowVar = ROW_VAR,
}

enums! {
    /// A type.
    Type {
        NamedType, TupleType, ParenType, RecordType, SpreadType, FnType, HandlerType, ValueArg,
        MacroType, SpliceType,
    }
    /// An element of a row.
    RowElem { RowIo, RowRaise, RowVar, RowEffect, RowAsync, }
}

impl NamedType {
    /// The type's path.
    #[must_use]
    pub fn path(&self) -> Option<Path> {
        child(&self.0)
    }

    /// The type arguments, in order.
    pub fn args(&self) -> impl Iterator<Item = Type> + use<> {
        child::<TypeArgList>(&self.0)
            .into_iter()
            .flat_map(|list| children(&list.0))
    }
}

impl ValueArg {
    /// The literal's token: an integer, `true` or `false`.
    #[must_use]
    pub fn literal(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            .find(|t| matches!(t.kind(), INT | TRUE_KW | FALSE_KW))
    }

    /// Whether a `-` is written before the integer.
    #[must_use]
    pub fn is_negative(&self) -> bool {
        token(&self.0, MINUS).is_some()
    }
}

impl TupleType {
    /// The elements, in order.
    pub fn types(&self) -> impl Iterator<Item = Type> + use<> {
        children(&self.0)
    }
}

impl RecordType {
    /// The fields, in order.
    pub fn fields(&self) -> impl Iterator<Item = FieldDef> + use<> {
        children(&self.0)
    }

    /// Whether it ends with `..`, which makes it open (records.open-parameter-types).
    #[must_use]
    pub fn is_open(&self) -> bool {
        token(&self.0, DOT2).is_some()
    }
}

impl SpreadType {
    /// The type after `..`.
    #[must_use]
    pub fn ty(&self) -> Option<Type> {
        child(&self.0)
    }
}

impl ParenType {
    /// The type in the parentheses.
    #[must_use]
    pub fn ty(&self) -> Option<Type> {
        child(&self.0)
    }
}

impl FnType {
    /// The type parameters of a polymorphic function type (polymorphism.function-types).
    #[must_use]
    pub fn generic_list(&self) -> Option<GenericList> {
        child(&self.0)
    }

    /// The parameters' types, in order.
    pub fn params(&self) -> impl Iterator<Item = ParamType> + use<> {
        child::<ParamTypeList>(&self.0)
            .into_iter()
            .flat_map(|list| children(&list.0))
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

impl ParamType {
    /// Whether it is written `inout`.
    #[must_use]
    pub fn mode(&self) -> Mode {
        mode(&self.0)
    }

    /// The parameter's type.
    #[must_use]
    pub fn ty(&self) -> Option<Type> {
        child(&self.0)
    }
}

impl Row {
    /// The elements, in order.
    pub fn elements(&self) -> impl Iterator<Item = RowElem> + use<> {
        children(&self.0)
    }
}

impl RowRaise {
    /// The type of the error it raises.
    #[must_use]
    pub fn ty(&self) -> Option<Type> {
        child(&self.0)
    }
}

impl RowVar {
    /// The variable's identifier.
    #[must_use]
    pub fn ident(&self) -> Option<SyntaxToken> {
        token(&self.0, LOWER_IDENT)
    }
}
