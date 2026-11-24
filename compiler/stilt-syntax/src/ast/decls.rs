//! The views of declarations: functions, with their parameters, types, traits, constants and
//! tests. Their generics are in [`super::generics`].

use super::{
    AstNode, Block, Docs, Expr, Generic, GenericList, Limits, Mode, Name, Row, Type, TypeParam,
    WhereClause, child, children, has, mode, token,
};
use crate::SyntaxKind::{self, *};
use crate::{SyntaxNode, SyntaxToken};

nodes! {
    /// A function.
    Fn = FN,
    /// A function's parameters.
    ParamList = PARAM_LIST,
    /// The parameter `self`.
    SelfParam = SELF_PARAM,
    /// A parameter.
    Param = PARAM,
    /// The return type of a function or a function type.
    RetType = RET_TYPE,
    /// A body written `= ?`.
    HoleBody = HOLE_BODY,
    /// A type declaration.
    TypeDecl = TYPE_DECL,
    /// The fields of a record type.
    RecordDef = RECORD_DEF,
    /// A field of a record type.
    FieldDef = FIELD_DEF,
    /// The variants of a variant type.
    VariantList = VARIANT_LIST,
    /// A variant.
    Variant = VARIANT,
    /// The payload of a variant.
    PayloadList = PAYLOAD_LIST,
    /// A field of a variant's payload.
    Payload = PAYLOAD,
    /// A trait.
    Trait = TRAIT,
    /// A constant.
    Const = CONST,
    /// A test.
    Test = TEST,
}

enums! {
    /// A function's body.
    FnBody { Block, HoleBody, }
    /// The definition of a type.
    TypeDef { RecordDef, VariantList, }
}

/// The parts that declarations share: their doc comments and their visibility.
macro_rules! declaration {
    ($($name:ident),*) => {$(
        impl $name {
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
        }
    )*};
}

declaration!(Fn, TypeDecl, Trait, Const, Test);

impl Fn {
    /// The function's name.
    #[must_use]
    pub fn name(&self) -> Option<Name> {
        child(&self.0)
    }

    /// Whether the function is a procedural macro, written with `macro`
    /// (macros.procedural-declarations).
    #[must_use]
    pub fn is_macro(&self) -> bool {
        has(&self.0, MACRO_KW)
    }

    /// Whether the function is written `extern`: exported to C, or given by C.
    #[must_use]
    pub fn is_extern(&self) -> bool {
        has(&self.0, EXTERN_KW)
    }

    /// Whether the function is exported to C, written `pub extern fn` with a body
    /// (c.exported-functions).
    #[must_use]
    pub fn is_exported(&self) -> bool {
        self.is_extern() && self.body().is_some()
    }

    /// Whether the function is foreign, which C gives: written `extern fn` with no body
    /// (c.foreign-functions). A function whose part breaks holds the rest of the part as an error,
    /// and is no foreign one, but a function with an error (errors.declarations-with-errors).
    #[must_use]
    pub fn is_foreign(&self) -> bool {
        self.is_extern() && self.body().is_none() && !self.0.children().any(|n| n.kind() == ERROR)
    }

    /// The keyword that declares it: `fn`, or `macro` for a procedural macro.
    #[must_use]
    pub fn keyword(&self) -> Option<SyntaxToken> {
        token(&self.0, FN_KW).or_else(|| token(&self.0, MACRO_KW))
    }

    /// Its generic parameters, in brackets.
    #[must_use]
    pub fn generic_list(&self) -> Option<GenericList> {
        child(&self.0)
    }

    /// Its parameters, in parentheses.
    #[must_use]
    pub fn param_list(&self) -> Option<ParamList> {
        child(&self.0)
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

    /// The `where` clause, if the function has one (traits.where).
    #[must_use]
    pub fn where_clause(&self) -> Option<WhereClause> {
        child(&self.0)
    }

    /// The `without` clause, if the function has one (declarations.limits).
    #[must_use]
    pub fn limits(&self) -> Option<Limits> {
        child(&self.0)
    }

    /// The body, absent from a trait method that has none.
    #[must_use]
    pub fn body(&self) -> Option<FnBody> {
        child(&self.0)
    }
}

impl ParamList {
    /// The `self` parameter, which comes first.
    #[must_use]
    pub fn self_param(&self) -> Option<SelfParam> {
        child(&self.0)
    }

    /// The parameters other than `self`, in order.
    pub fn params(&self) -> impl Iterator<Item = Param> + use<> {
        children(&self.0)
    }
}

impl SelfParam {
    /// Whether it is written `inout`.
    #[must_use]
    pub fn mode(&self) -> Mode {
        mode(&self.0)
    }

    /// The `self` keyword, after any `inout`.
    #[must_use]
    pub fn self_token(&self) -> Option<SyntaxToken> {
        token(&self.0, SELF_KW)
    }

    /// The receiver's written type, as `self: Self<A>` (traits.receiver-types).
    #[must_use]
    pub fn ty(&self) -> Option<Type> {
        child(&self.0)
    }
}

impl Param {
    /// Whether it is written `inout`.
    #[must_use]
    pub fn mode(&self) -> Mode {
        mode(&self.0)
    }

    /// Whether the parameter is written `escaping` (declarations.parameters).
    #[must_use]
    pub fn is_escaping(&self) -> bool {
        has(&self.0, ESCAPING_KW)
    }

    /// The `escaping` keyword, if the parameter is written with it.
    #[must_use]
    pub fn escaping_token(&self) -> Option<SyntaxToken> {
        token(&self.0, ESCAPING_KW)
    }

    /// The `inout` of a parameter written `inout x: T`.
    #[must_use]
    pub fn inout_token(&self) -> Option<SyntaxToken> {
        token(&self.0, INOUT_KW)
    }

    /// The parameter's name.
    #[must_use]
    pub fn name(&self) -> Option<Name> {
        child(&self.0)
    }

    /// The parameter's type.
    #[must_use]
    pub fn ty(&self) -> Option<Type> {
        child(&self.0)
    }
}

impl RetType {
    /// The result type.
    #[must_use]
    pub fn ty(&self) -> Option<Type> {
        child(&self.0)
    }

    /// Whether the result is written `inout T`, which makes the function a projection
    /// (projections.declaring-projection).
    #[must_use]
    pub fn is_inout(&self) -> bool {
        has(&self.0, INOUT_KW)
    }

    /// The `inout` of a result written `inout T`.
    #[must_use]
    pub fn inout_token(&self) -> Option<SyntaxToken> {
        token(&self.0, INOUT_KW)
    }
}

impl TypeDecl {
    /// The type's name.
    #[must_use]
    pub fn name(&self) -> Option<Name> {
        child(&self.0)
    }

    /// The type parameters, which are plain names, and the value parameters
    /// (generics.value-parameters).
    pub fn params(&self) -> impl Iterator<Item = Generic> + use<> {
        child::<GenericList>(&self.0)
            .into_iter()
            .flat_map(|list| children(&list.0))
    }

    /// What follows `=`: a record's fields, variants, or the type it names.
    #[must_use]
    pub fn def(&self) -> Option<TypeDef> {
        child(&self.0)
    }

    /// The `?` of a native type, `type Name<…> = ?`, which has no written representation
    /// (views.std-view).
    #[must_use]
    pub fn native(&self) -> Option<SyntaxToken> {
        token(&self.0, QUESTION)
    }
}

impl RecordDef {
    /// The fields, in order.
    pub fn fields(&self) -> impl Iterator<Item = FieldDef> + use<> {
        children(&self.0)
    }
}

impl FieldDef {
    /// The field's name.
    #[must_use]
    pub fn name(&self) -> Option<Name> {
        child(&self.0)
    }

    /// The field's type.
    #[must_use]
    pub fn ty(&self) -> Option<Type> {
        child(&self.0)
    }
}

impl VariantList {
    /// The variants, in order.
    pub fn variants(&self) -> impl Iterator<Item = Variant> + use<> {
        children(&self.0)
    }
}

impl Variant {
    /// The variant's name.
    #[must_use]
    pub fn name(&self) -> Option<Name> {
        child(&self.0)
    }

    /// The fields of the payload, none for a variant without one.
    pub fn payloads(&self) -> impl Iterator<Item = Payload> + use<> {
        child::<PayloadList>(&self.0)
            .into_iter()
            .flat_map(|list| children(&list.0))
    }
}

impl Payload {
    /// The field's name, which only documents it (declarations.records).
    #[must_use]
    pub fn name(&self) -> Option<Name> {
        child(&self.0)
    }

    /// The field's type.
    #[must_use]
    pub fn ty(&self) -> Option<Type> {
        child(&self.0)
    }
}

impl Trait {
    /// The trait's name.
    #[must_use]
    pub fn name(&self) -> Option<Name> {
        child(&self.0)
    }

    /// The trait's parameters, which are plain names (traits.trait-parameters).
    pub fn params(&self) -> impl Iterator<Item = TypeParam> + use<> {
        child::<GenericList>(&self.0)
            .into_iter()
            .flat_map(|list| children(&list.0))
    }

    /// The trait's functions, without its constants.
    pub fn methods(&self) -> impl Iterator<Item = Fn> + use<> {
        children(&self.0)
    }

    /// The trait's functions and constants, in order (traits.functions-without-self and
    /// traits.trait-constants).
    pub fn members(&self) -> impl Iterator<Item = super::Item> + use<> {
        children(&self.0).filter(|item| matches!(item, super::Item::Fn(_) | super::Item::Const(_)))
    }
}

impl Const {
    /// The constant's name.
    #[must_use]
    pub fn name(&self) -> Option<Name> {
        child(&self.0)
    }

    /// The constant's type.
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

impl Test {
    /// The test's name, a string literal.
    #[must_use]
    pub fn name(&self) -> Option<SyntaxToken> {
        token(&self.0, STRING)
    }

    /// The test's block.
    #[must_use]
    pub fn body(&self) -> Option<Block> {
        child(&self.0)
    }
}
