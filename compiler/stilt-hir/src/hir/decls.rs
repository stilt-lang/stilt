//! Declarations, which hold no positions.

use stilt_syntax::ast::Mode;
pub use stilt_syntax::capability::{Capabilities, Capability};

use super::{BodyIndex, GenericId, Item, Name, Row, TraitRef, Ty};

/// A generic of a function, an impl block or a type.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Generic {
    /// Its name.
    pub name: Name,
    /// What it is.
    pub kind: GenericKind,
    /// Whether it is a member type, as `C.Item`, which a bound without its arguments gives a
    /// parameter of its trait (traits.member-types), rather than a generic the program writes. Its
    /// bounds are those of the `where` clause (traits.where).
    pub member: bool,
    /// Whether it is a pack, `..Ts` (variadics.packs).
    pub pack: bool,
}

/// What a generic is.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum GenericKind {
    /// A type parameter, with its bounds.
    Type(Vec<TraitRef>),
    /// A row variable.
    Row,
    /// A value parameter, with its type, an integer type or `bool` (generics.value-parameters), or
    /// the error type for any other.
    Value(Ty),
}

/// A parameter of a function, whose name its body binds.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Param {
    /// The receiver, with its written type, which only a constructor trait's methods and their
    /// impls' write (traits.receiver-types).
    SelfParam(Mode, Option<Ty>),
    /// A parameter's mode and type, and whether it is written `escaping` (declarations.parameters).
    Param(Mode, Ty, bool),
}

impl Param {
    /// Whether the parameter passes its argument's effects through: a `let` parameter of
    /// function type that isn't written `escaping` (effects.non-escaping-parameters).
    #[must_use]
    pub fn passes(&self) -> bool {
        // A parameter of handler type always does (handlers.handler-types).
        matches!(
            self,
            Param::Param(Mode::Let, Ty::Fn(_), false) | Param::Param(Mode::Let, Ty::Handler(_), _)
        )
    }
}

impl Generic {
    /// The type of a value parameter (generics.value-parameters).
    #[must_use]
    pub fn value_type(&self) -> Option<&Ty> {
        match &self.kind {
            GenericKind::Value(t) => Some(t),
            GenericKind::Type(_) | GenericKind::Row => None,
        }
    }

    /// The bounds of a type parameter, none for a row variable or a value parameter.
    #[must_use]
    pub fn bounds(&self) -> &[TraitRef] {
        match &self.kind {
            GenericKind::Type(bounds) => bounds,
            GenericKind::Row | GenericKind::Value(_) => &[],
        }
    }
}

/// What follows a function's signature.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FnBody {
    /// A block, which is the body of the given index.
    Block(BodyIndex),
    /// `= ?`, whose body is the hole, at the `?`. In the standard library it marks a native
    /// function (declarations.native-items).
    Hole(BodyIndex),
}

/// A function's declaration.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FnDecl {
    /// Its name.
    pub name: Name,
    /// Its generics, in order.
    pub generics: Vec<Generic>,
    /// Its parameters, the receiver first.
    pub params: Vec<Param>,
    /// Its written result type, or `None` for `()`.
    pub ret: Option<Ty>,
    /// Whether its result is written `inout T`: a projection, whose body yields a place of type
    /// `T` (projections.declaring-projection).
    pub projection: bool,
    /// Its row.
    pub row: Row,
    /// What the function's `without` limits (declarations.limits).
    pub limits: Limits,
    /// The bounds its `where` clause gives the member types of its impl block's parameters,
    /// which its body assumes and its callers meet (traits.where).
    pub assumed: Vec<(GenericId, Vec<TraitRef>)>,
    /// `None` for a trait method without a default.
    pub body: Option<FnBody>,
    /// Whether it is a procedural macro, a function of its signature whose uses run it
    /// (macros.procedural-declarations and macros.procedural-bodies).
    pub procedural: bool,
    /// Whether it is a foreign function, which C gives, written `extern fn` without a body
    /// (c.foreign-functions).
    pub foreign: bool,
}

/// The implicit effects that a `without` clause rules out: `panic` (effects.without-panic), `alloc`
/// (facts.without-alloc), `div` and `copy` (facts.without-div and facts.without-copy), and the
/// capabilities below `io` (facts.without), and `locks` (shared.locks).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
// Each flag is a limit of its own, which any set of the others may come with.
#[allow(clippy::struct_excessive_bools)]
pub struct Limits {
    /// `panic` (effects.without-panic).
    pub panic: bool,
    /// `overflow` (effects.without-overflow).
    pub overflow: bool,
    /// `alloc` (facts.without-alloc).
    pub alloc: bool,
    /// `div` (facts.without-div).
    pub div: bool,
    /// `copy` (facts.without-copy).
    pub copy: bool,
    /// `locks` (shared.locks).
    pub locks: bool,
    /// The capabilities it names (facts.without).
    pub capabilities: Capabilities,
}

impl Limits {
    /// The limits of either `self` or `other`.
    #[must_use]
    pub fn or(self, other: Limits) -> Limits {
        Limits {
            panic: self.panic || other.panic,
            overflow: self.overflow || other.overflow,
            alloc: self.alloc || other.alloc,
            div: self.div || other.div,
            copy: self.copy || other.copy,
            locks: self.locks || other.locks,
            capabilities: self.capabilities.or(other.capabilities),
        }
    }

    /// The names of the limits set, as the `limit` production orders them
    /// (syntax.declarations).
    #[must_use]
    pub fn names(self) -> Vec<&'static str> {
        let flags = [
            (self.panic, "panic"),
            (self.overflow, "overflow"),
            (self.alloc, "alloc"),
            (self.div, "div"),
            (self.copy, "copy"),
        ];
        let mut names: Vec<&'static str> = flags
            .iter()
            .filter(|(on, _)| *on)
            .map(|(_, n)| *n)
            .collect();
        names.extend(self.capabilities.iter().map(Capability::text));
        if self.locks {
            names.push("locks");
        }
        names
    }

    /// Whether any limit is set.
    #[must_use]
    pub fn any(self) -> bool {
        self.panic
            || self.overflow
            || self.alloc
            || self.div
            || self.copy
            || self.locks
            || !self.capabilities.is_empty()
    }
}

/// What a type is defined as.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TypeDef {
    /// The fields' names and types.
    Record(Vec<(Name, Ty)>),
    /// The variants' names and payloads. Payload names are documentation only
    /// (declarations.variant-types), so they are gone.
    Variants(Vec<(Name, Vec<Ty>)>),
    /// A native type of the standard library, `type Name<…> = ?`, which has no written
    /// representation: each implementation gives it one (views.std-view).
    Native,
}

/// A trait (traits.declaring-trait; traits.trait-parameters, traits.trait-constants and
/// traits.constructor-traits).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TraitDecl {
    /// Its name.
    pub name: Name,
    /// Its parameters, whose generics are those of the declaration's own index.
    pub params: Vec<Name>,
    /// The number of type arguments its `Self` takes: 0 for a trait over types, and the arity
    /// of the constructors a constructor trait is over (traits.constructor-traits).
    pub arity: u32,
    /// Its functions and constants.
    pub members: Vec<Member>,
}

/// A type's declaration.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeDecl {
    /// Its name.
    pub name: Name,
    /// The type parameters, whose generics are those of the declaration's own index.
    pub params: Vec<Name>,
    /// Whether the last is a pack (variadics.packs).
    pub pack: bool,
    /// The value parameters among them, each by its place and with its type
    /// (generics.value-parameters).
    pub values: Vec<(u32, Ty)>,
    /// Its definition.
    pub def: TypeDef,
}

/// A constant's declaration.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ConstDecl {
    /// Its name.
    pub name: Name,
    /// Its type.
    pub ty: Ty,
    /// The body of the constant's value.
    pub value: BodyIndex,
}

/// A function or constant of an impl block or trait.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Member {
    /// Whether it is written `pub`.
    pub is_pub: bool,
    /// What it is.
    pub kind: MemberKind,
    /// Whether a part with a syntax error declares only its name: every use of it has the
    /// error type, and it is no member of its block (errors.broken-parts).
    pub unknown: bool,
    /// The bodies of the member's doc examples and properties.
    pub examples: Vec<BodyIndex>,
}

/// What a member is.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum MemberKind {
    /// A function.
    Fn(FnDecl),
    /// A constant of an impl block.
    Const(ConstDecl),
    /// A constant of a trait, with the body of its default if it has one (traits.trait-constants).
    TraitConst(Name, Ty, Option<BodyIndex>),
}

impl Member {
    /// Its name.
    #[must_use]
    pub fn name(&self) -> &Name {
        match &self.kind {
            MemberKind::Fn(f) => &f.name,
            MemberKind::Const(c) => &c.name,
            MemberKind::TraitConst(name, ..) => name,
        }
    }
}

/// A declaration of a module.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Decl {
    /// Whether it is written `pub`.
    pub is_pub: bool,
    /// What it declares.
    pub kind: DeclKind,
    /// The bodies of the declaration's doc examples and properties.
    pub examples: Vec<BodyIndex>,
}

/// What a declaration declares.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum DeclKind {
    /// A function.
    Fn(FnDecl),
    /// A type.
    Type(TypeDecl),
    /// A trait.
    Trait(TraitDecl),
    /// A constant.
    Const(ConstDecl),
    /// A test's name and body.
    Test(String, BodyIndex),
    /// A macro (macros.syntax-declarations): its name, its patterns, which are part of its module's
    /// API, and its templates, which are its body, each as written, token by token.
    Macro(MacroDecl),
    /// An effect (handlers.declaring-effect).
    Effect(super::EffectDecl),
}

/// A macro's declaration, as the API checks and pins read it (macros.syntax-declarations).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MacroDecl {
    /// Its name.
    pub name: Name,
    /// Its patterns, as written.
    pub patterns: String,
    /// Its templates, as written.
    pub templates: String,
    /// The functions its templates name, as they resolve where it is declared, whose
    /// capabilities are its package's (macros.expansion-effects).
    pub names: Vec<Item>,
}

impl DeclKind {
    /// The declared name, which a test doesn't have in a namespace.
    #[must_use]
    pub fn name(&self) -> Option<&Name> {
        match self {
            Self::Fn(f) => Some(&f.name),
            Self::Type(t) => Some(&t.name),
            Self::Trait(t) => Some(&t.name),
            Self::Const(c) => Some(&c.name),
            Self::Macro(m) => Some(&m.name),
            Self::Effect(e) => Some(&e.name),
            Self::Test(..) => None,
        }
    }
}

/// An impl block, of a trait or inherent.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Impl {
    /// The type parameters, every one a [`GenericKind::Type`].
    pub generics: Vec<Generic>,
    /// `Some` for `impl Trait for T`.
    pub trait_ref: Option<TraitRef>,
    /// The type it is for.
    pub self_ty: Ty,
    /// Its members, in source order.
    pub members: Vec<Member>,
    /// The bounds of its `where` clause on member types that a bound's argument fixes, each a
    /// trait with its arguments, which the fixed type must meet (traits.where), each reported
    /// at an anchor of its own.
    pub fixed: Vec<(Ty, Item, Vec<Ty>)>,
}

/// An item of a module, in source order.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ItemHir {
    /// A `use` declaration, whose effect is in the module's scope.
    Use,
    /// A declaration.
    Decl(Decl),
    /// An impl block.
    Impl(Impl),
}

/// A module's declarations, without bodies or positions.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ModuleHir {
    /// The module's dotted name, or its file's path when the name is invalid
    /// (program.module-names).
    pub name: Name,
    /// Whether the module is part of the standard library.
    pub std: bool,
    /// What the header's `without` limits (program.header-limits).
    pub limits: Limits,
    /// The modules that `use` declarations import, whose traits are visible to method calls
    /// (traits.traits-in-scope), sorted.
    pub imports: Vec<Name>,
    /// The items in source order. Of two declarations with the same name, the first is the one
    /// that names refer to (errors.several-places).
    pub items: Vec<ItemHir>,
    /// The names of the type parameters of the polymorphic function types that its items
    /// write (polymorphism.function-types).
    pub poly_names: Vec<(GenericId, Name)>,
}
