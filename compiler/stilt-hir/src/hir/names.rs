//! Names, and the types that signatures and bodies write.

use serde::{Deserialize, Serialize};
use stilt_syntax::TextRange;
use stilt_syntax::ast::Mode;

pub use super::name::Name;

/// A module-level item: its home module, by dotted name, and its own name, which is unique within
/// its namespace there (declarations.unique-names). The built-in types are items of `std.prelude`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Item {
    /// Its module's dotted name.
    pub home: Name,
    /// Its own name.
    pub name: Name,
}

/// A module's item, use or impl block, by its place among the module's items in source order.
/// A module whose name is invalid (program.module-names) is known by its file's path.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeclId {
    /// The module's dotted name, or its file's path.
    pub module: Name,
    /// Its place among the module's items.
    pub index: u32,
}

/// The declaration whose list declares a generic: a function, a type or an impl block, or a
/// member of an impl block or trait.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Owner {
    /// The function, type or impl block.
    pub decl: DeclId,
    /// The member, by its place in its impl block or trait.
    pub member: Option<u32>,
}

/// A type parameter or a row variable: the declaration that declares it, and its place in the list
/// there. A type parameter of a polymorphic function type (polymorphism.function-types) has its
/// declaration's owner and a place from [`GenericId::POLY`] on, unique in the declaration.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GenericId {
    /// The declaration that declares it.
    pub owner: Owner,
    /// Its place in the declaration's list.
    pub index: u32,
}

/// The module that the fresh types of shapes are owned by, which no program can name.
const FRESH: &str = "#fresh";

impl GenericId {
    /// The first place of the type parameters of polymorphic function types.
    pub const POLY: u32 = 1 << 24;

    /// How many of them a declaration has at most. Past them, the places from
    /// [`GenericId::POLY`] on stand for the copies that type checking makes of them, one for
    /// each value it checks against their type ([`GenericId::copy`]).
    pub const POLY_SPAN: u32 = 1 << 12;

    /// Whether it is a type parameter of a polymorphic function type (polymorphism.function-types).
    #[must_use]
    pub fn is_poly(&self) -> bool {
        self.index >= Self::POLY
    }

    /// The type parameter of a polymorphic function type that a declaration writes, of which
    /// this is a copy, or itself.
    #[must_use]
    pub fn declared(&self) -> Self {
        let index = if self.is_poly() {
            Self::POLY + (self.index - Self::POLY) % Self::POLY_SPAN
        } else {
            self.index
        };
        Self {
            owner: self.owner.clone(),
            index,
        }
    }

    /// The fresh type `n` of a body, the type of a field, an element or a payload in an arm or a
    /// loop body that reads a shape, named `letter` in messages as meta.shapes, meta.fields and
    /// meta.variant-cases name it: a rigid type of its own, with no bound, which no code can name
    /// (meta.fresh-types).
    #[must_use]
    pub fn fresh(n: u32, letter: char) -> Self {
        Self {
            owner: Owner {
                decl: DeclId {
                    module: Name::from(FRESH),
                    index: n,
                },
                member: None,
            },
            index: u32::from(letter),
        }
    }

    /// Whether it is a fresh type of a shape (meta.fresh-types).
    #[must_use]
    pub fn is_fresh(&self) -> bool {
        &*self.owner.decl.module == FRESH
    }

    /// The letter that names a fresh type in messages.
    #[must_use]
    pub fn fresh_letter(&self) -> Option<char> {
        self.is_fresh()
            .then(|| char::from_u32(self.index))
            .flatten()
    }

    /// The copy `n` of the type parameter of a polymorphic function type that a declaration
    /// writes, a rigid type of its own (polymorphism.rigid-types).
    #[must_use]
    pub fn copy(&self, n: u32) -> Self {
        let declared = self.declared();
        Self {
            owner: declared.owner,
            index: declared
                .index
                .saturating_add(n.saturating_mul(Self::POLY_SPAN)),
        }
    }
}

/// A trait, as a bound or as the trait of an impl, with its arguments: one for each of its
/// parameters, none for a trait without any (traits.trait-arguments and traits.bound-arguments). A
/// bound written without them gives each a member type of its own, a generic that the function or
/// impl declares.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TraitRef {
    /// A trait, with its arguments.
    Trait(Item, Vec<Ty>),
    /// A trait name with an error, which the type checker treats as satisfied by every type.
    Error,
}

/// A type, as signatures and bodies write it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    /// A named type with its arguments, such as `i64` or `List<Order>`.
    Con(Item, Vec<Ty>),
    /// A type parameter.
    Param(GenericId),
    /// `Self` in a trait: the type that implements it.
    SelfTy,
    /// A constructor applied to its arguments: a constructor parameter, as `F<i64>`, or `Self` in a
    /// constructor trait, as `Self<A>` (traits.constructor-traits and
    /// traits.constructor-parameters). The head is a [`Ty::Param`] or [`Ty::SelfTy`].
    App(Box<Ty>, Vec<Ty>),
    /// `()` is the empty tuple. Its elements may be spreads.
    Tuple(Vec<Ty>),
    /// A function type.
    Fn(Box<FnTy>),
    /// A handler's type (handlers.handler-types).
    Handler(Box<super::HandlerTy>),
    /// A spread of the pack `0`, `..T` where `T`, the second, names it, and stands for each of
    /// its elements: an element of a tuple type or a parameter of a function type, and nothing
    /// else (variadics.type-spreads).
    Spread(GenericId, Box<Ty>),
    /// A value argument given for a value parameter, as the `7` of `Mod<7>`, by its value
    /// (generics.value-arguments and generics.constant-arguments). A value parameter given as an
    /// argument is a [`Ty::Param`].
    Value(Value),
    /// A type with an error.
    Error,
}

/// The value of a value argument: an integer, of any of the integer types, or a `bool`, which
/// compare exactly, so that two types are equal when their arguments are (generics.value-parameters
/// and generics.equal-types).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Value {
    /// An integer.
    Int(i128),
    /// `true` or `false`.
    Bool(bool),
}

impl std::fmt::Display for Value {
    /// The value as a diagnostic shows it, in decimal (generics.constant-arguments).
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Int(n) => write!(f, "{n}"),
            Value::Bool(b) => write!(f, "{b}"),
        }
    }
}

/// A function type. A polymorphic one declares its type parameters, with their bounds, which
/// its parameters' types and its result name (polymorphism.function-types).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FnTy {
    /// Its type parameters, with their bounds, for a polymorphic one.
    pub generics: Vec<(GenericId, Vec<TraitRef>)>,
    /// Each parameter's mode and type.
    pub params: Vec<(Mode, Ty)>,
    /// The written return type, or `None` for `()`.
    pub ret: Option<Ty>,
    /// Its row.
    pub row: Row,
}

/// An effect row (effects.rows). Each kind of element appears at most once, and each effect
/// once (handlers.effects-in-rows).
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Row {
    /// Whether it holds `io`.
    pub io: bool,
    /// The type of the error it raises, from its `raise E`.
    pub raise: Option<Box<Ty>>,
    /// Its row variable.
    pub var: Option<GenericId>,
    /// Its effects, in the order written, `async` among them (handlers.effects-in-rows;
    /// tasks.async).
    pub effects: Vec<super::EffectInst>,
}

/// A type written in a body, where its position is reported.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeRef {
    /// The type.
    pub ty: Ty,
    /// Where it is written.
    pub at: TextRange,
}

/// A name written in a body: a field, a member or a reason.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ident {
    /// The name.
    pub name: Name,
    /// Where it is written.
    pub at: TextRange,
}
