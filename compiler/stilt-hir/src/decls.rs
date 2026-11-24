//! Declarations: what every item and impl block of a program and of the standard library
//! declares, as the type checker reads it, and the errors that arise only outside bodies, in impl
//! blocks (traits.impl-blocks and traits.implementing-trait), records
//! (declarations.recursive-types) and `main` (program.main and program.missing-main).
//!
//! Of two items with the same name, the first is the one names refer to, and resolution
//! reports the other (errors.several-places).

mod build;
mod checks;
mod implements;
mod impls;
mod lookup;
mod once;
mod records;
mod signatures;
mod wheres;

use std::collections::HashMap;
use stilt_diag::Code;

use stilt_db::{Db, Program, SourceFile};

use crate::Anchor;
use crate::hir::{DeclId, GenericId, Item, Mode, Name, Owner, Row, Ty};
use crate::lower::module_hir;
use crate::scope::PRELUDE;
use build::{Builder, Unit};
pub use lookup::{Lookup, Queried};
pub use once::QueriedOnce;
pub use records::record_owner;
pub use signatures::{bound_args_of, bounds_of, signature, substituted};

/// The type parameters of a signature, each with the traits that bound it.
pub type Bounds = Vec<(GenericId, Vec<Item>)>;

/// The arguments that a bound gives a trait with parameters, one for each parameter
/// (traits.bound-arguments): a type, or the member type that a bound written without them declares.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BoundArgs {
    /// The type parameter the bound is on.
    pub param: GenericId,
    /// The trait.
    pub trait_item: Item,
    /// The arguments, one for each of the trait's parameters.
    pub args: Vec<Ty>,
}

/// A function's signature, as callers see it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnSig {
    /// The declaration that declares it, whose non-escaping parameters' implicit row variables
    /// are its own (effects.non-escaping-parameters).
    pub owner: Owner,
    /// An impl member's are those of its block, then its own.
    pub type_params: Bounds,
    /// The value parameters among them, with their types (generics.value-parameters).
    pub values: Vec<(GenericId, Ty)>,
    /// The arguments its bounds give the traits with parameters, in the same order
    /// (traits.bound-arguments).
    pub bound_args: Vec<BoundArgs>,
    /// Its row variables.
    pub row_params: Vec<GenericId>,
    /// Each parameter's mode and type, the receiver's first.
    pub params: Vec<(Mode, Ty)>,
    /// Whether each parameter passes its argument's effects through, as a non-escaping
    /// parameter does (effects.non-escaping-parameters). A receiver never does.
    pub passing: Vec<bool>,
    /// Its result type.
    pub ret: Ty,
    /// Whether it is a projection, whose call is a place of type `ret`
    /// (projections.declaring-projection and projections.call-is-place).
    pub projection: bool,
    /// Its row.
    pub row: Row,
    /// Whether it is a foreign function, which C gives (c.foreign-functions).
    pub foreign: bool,
    /// What a foreign function's `without` clause says its C code doesn't do, which a call of it
    /// then doesn't add (c.effects); none for any other function.
    pub trusted: crate::hir::Limits,
}

/// What a member of an impl block or a trait is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemberKindInfo {
    /// A method, with its receiver's mode.
    Method(Mode),
    /// A function without `self`.
    Function,
    /// A constant.
    Constant,
}

/// A member of an impl block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemberInfo {
    /// Its name.
    pub name: Name,
    /// Whether other modules may name it: a trait impl's members, and the `pub` members of a
    /// `pub` type's inherent impls (program.visibility).
    pub is_pub: bool,
    /// What it is.
    pub kind: MemberKindInfo,
    /// A constant's has no parameters, and returns the constant's type.
    pub signature: FnSig,
    /// The type constructor the block is for.
    pub owner: Item,
    /// The type parameters of its block, with their bounds.
    pub impl_generics: Bounds,
    /// The type its block is for.
    pub self_ty: Ty,
}

/// An impl block of a trait.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImplInfo {
    /// The module that declares it.
    pub module: Name,
    /// Its type parameters, with their bounds.
    pub generics: Bounds,
    /// The value parameters among them, with their types (generics.value-parameters).
    pub values: Vec<(GenericId, Ty)>,
    /// The arguments the bounds of its generics give traits with parameters
    /// (traits.bound-arguments).
    pub bound_args: Vec<BoundArgs>,
    /// The arguments it gives the trait's parameters, which may name its generics
    /// (traits.trait-arguments).
    pub trait_args: Vec<Ty>,
    /// The type it is for.
    pub self_ty: Ty,
    /// Its declaration.
    pub decl: DeclId,
    /// Its members, in source order.
    pub members: Vec<MemberInfo>,
}

/// What a type is defined as.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeDefInfo {
    /// A record's fields' names and types.
    Record(Vec<(Name, Ty)>),
    /// The variants' names and payloads.
    Variants(Vec<(Name, Vec<Ty>)>),
    /// A built-in type, which has no declaration.
    Builtin,
}

/// A type: its parameters and its definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeInfo {
    /// Its type parameters.
    pub params: Vec<GenericId>,
    /// The value parameters among them, each by its place and with its type
    /// (generics.value-parameters).
    pub values: Vec<(u32, Ty)>,
    /// Its definition.
    pub def: TypeDefInfo,
    /// Whether other modules may name it.
    pub is_pub: bool,
    /// Whether its last parameter is a pack (variadics.packs).
    pub pack: bool,
}

/// A member of a trait, whose signature names the implementing type `Self` and the trait's
/// parameters: a method, a function without `self`, or a constant, whose signature takes
/// nothing and returns its type (traits.functions-without-self and traits.trait-constants).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraitMethod {
    /// Its name.
    pub name: Name,
    /// What it is.
    pub kind: MemberKindInfo,
    /// Its signature.
    pub signature: FnSig,
    /// Whether the trait gives it a default.
    pub has_default: bool,
}

impl TraitMethod {
    /// Whether it is a method, which takes `self`.
    #[must_use]
    pub fn is_method(&self) -> bool {
        matches!(self.kind, MemberKindInfo::Method(_))
    }
}

/// A trait (traits.declaring-trait).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraitInfo {
    /// Its parameters, whose arguments each impl gives (traits.trait-parameters).
    pub params: Vec<GenericId>,
    /// The number of type arguments its `Self` takes: 0 for a trait over types, and the arity
    /// of a constructor trait's constructors (traits.constructor-traits).
    pub arity: u32,
    /// Its functions and constants, in order: the entries of its dictionaries.
    pub methods: Vec<TraitMethod>,
    /// The methods that a syntax error leaves without a signature: every use of them has the
    /// error type, and an impl may hold them or not (errors.declarations-with-errors).
    pub unknown_methods: Vec<Name>,
}

/// An effect (handlers.declaring-effect): its type parameters, and its operations in order, each
/// with its parameters, its result and its own row, which name the type parameters.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EffectInfo {
    /// Its type parameters.
    pub params: Vec<GenericId>,
    /// Its operations, in order.
    pub ops: Vec<OperationSig>,
}

/// An operation of an effect, as a performance and a handler see it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OperationSig {
    /// Its name.
    pub name: Name,
    /// Each parameter's mode and type.
    pub params: Vec<(Mode, Ty)>,
    /// Its result type.
    pub ret: Ty,
    /// Its own row.
    pub row: Row,
}

impl EffectInfo {
    /// The operation `name`, with its place among the effect's operations.
    #[must_use]
    pub fn op(&self, name: &str) -> Option<(usize, &OperationSig)> {
        self.ops.iter().enumerate().find(|(_, o)| &*o.name == name)
    }
}

/// A variant: its type, its place among the type's variants, and its payload.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VariantInfo {
    /// Its type.
    pub ty: Item,
    /// Its place among the type's variants.
    pub index: u32,
    /// The types of its payload.
    pub payload: Vec<Ty>,
}

/// An error found among the declarations, at a part of an item of a module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DeclProblem {
    pub(crate) file: SourceFile,
    pub(crate) at: Anchor,
    pub(crate) code: Code,
    pub(crate) message: String,
}

/// What every item and impl block declares.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Declarations {
    /// The types, the built-in ones among them.
    pub types: HashMap<Item, TypeInfo>,
    /// The variants.
    pub variants: HashMap<Item, VariantInfo>,
    /// The functions' signatures.
    pub functions: HashMap<Item, FnSig>,
    /// The constants' types.
    pub constants: HashMap<Item, Ty>,
    /// The traits.
    pub traits: HashMap<Item, TraitInfo>,
    /// The effects (handlers.declaring-effect).
    pub effects: HashMap<Item, EffectInfo>,
    /// The members of each type's inherent impl blocks, in source order.
    pub inherent: HashMap<Item, Vec<MemberInfo>>,
    /// The impl of each trait, first, for each type constructor, second.
    pub trait_impls: HashMap<(Item, Item), ImplInfo>,
    /// The traits each module declares, in source order.
    pub module_traits: HashMap<Name, Vec<Item>>,
    /// The members of impl blocks with errors, whose uses have the error type (errors.error-type),
    /// by type constructor where it is known.
    pub broken: Vec<(Option<Item>, Name)>,
    pub(crate) problems: Vec<DeclProblem>,
}

impl Declarations {
    /// The impl of the trait `trait_item` for the type constructor `owner`.
    #[must_use]
    pub fn trait_impl(&self, trait_item: &Item, owner: &Item) -> Option<&ImplInfo> {
        self.trait_impls.get(&(trait_item.clone(), owner.clone()))
    }

    /// The members of `owner`'s inherent impl blocks, in source order.
    #[must_use]
    pub fn inherent_members(&self, owner: &Item) -> &[MemberInfo] {
        self.inherent.get(owner).map_or(&[], Vec::as_slice)
    }

    fn methods_of(&self, trait_item: &Item) -> &[TraitMethod] {
        self.traits
            .get(trait_item)
            .map_or(&[], |info| info.methods.as_slice())
    }
}

/// The item of the prelude of this name.
#[must_use]
pub fn prelude_item(name: &str) -> Item {
    Item {
        home: Name::from(PRELUDE),
        name: Name::from(name),
    }
}

/// The declarations of a program and of the standard library.
#[salsa::tracked(returns(ref))]
pub fn declarations(db: &dyn Db, program: Program) -> Declarations {
    let files: Vec<SourceFile> = program
        .std(db)
        .iter()
        .chain(program.files(db))
        .copied()
        .collect();
    let units: Vec<Unit<'_>> = files
        .iter()
        .map(|&file| Unit {
            file,
            path: file.path(db),
            hir: module_hir(db, program, file),
        })
        .collect();
    let mut builder = Builder {
        decls: Declarations::default(),
    };
    builder.declare_items(&units);
    builder.add_impls(&units);
    builder.check_record_cycles(&units);
    builder.check_main(&units);
    builder.check_impl_wheres(&units);
    let mut decls = builder.decls;
    let std: Vec<_> = program.std(db).clone();
    debug_assert!(
        decls.problems.iter().all(|p| !std.contains(&p.file)),
        "the standard library has errors: {:?}",
        decls.problems
    );
    decls.problems.retain(|p| !std.contains(&p.file));
    decls
}
