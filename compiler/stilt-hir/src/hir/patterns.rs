//! Patterns, whose parts hold their positions for their diagnostics.

use stilt_diag::Code;
use stilt_syntax::TextRange;

use super::{Ident, Item, LocalId, Name, TypeRef};

/// A pattern.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pat {
    /// What it is.
    pub kind: PatKind,
    /// Its span.
    pub at: TextRange,
}

/// What a pattern is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PatKind {
    /// `_`.
    Wild,
    /// A name, which binds this local.
    Bind(LocalId),
    /// An integer, with its `-` if it has one.
    Int(String),
    /// A string, its escapes resolved.
    Str(String),
    /// `true` or `false`.
    Bool(bool),
    /// A tuple's elements.
    Tuple(Vec<Pat>),
    /// A constant, written `C` or `m.C`.
    Const(Item),
    /// A constant of a type, `Type.NAME`.
    AssocConst(Box<TypeRef>, Ident),
    /// A variant with its payload patterns, which are none for `None`.
    Variant(Item, Vec<Pat>),
    /// A name without a module, `V` or `V(p₁, …)`, with its payload patterns. It names the
    /// variant `V` of the type the pattern is matched against, when that type has one, and
    /// otherwise its fallback (patterns.variants-by-type).
    Bare(Ident, Vec<Pat>, Box<Fallback>),
    /// The record type, the fields, and whether `..` ends the list.
    Record(Box<TypeRef>, Vec<FieldPat>, bool),
    /// A pattern that names no type, `{ f, .. }`, of an anonymous record or of any record known to
    /// have its fields (records.anonymous-patterns): the fields, and whether `..` ends the list.
    AnonRecord(Vec<FieldPat>, bool),
    /// A list's elements, and what follows them.
    List(Vec<Pat>, ListRest),
    /// Two or more alternatives, which bind the same variables.
    Or(Vec<Pat>),
    /// A pattern with an error.
    Error,
}

/// What a name without a module means in a pattern where the type matched has no variant of
/// that name: what it means in the module's scope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Fallback {
    /// The variant of that name in scope.
    Variant(Item),
    /// The constant of that name in scope.
    Const(Item),
    /// A name whose uses have the error type.
    Error,
    /// A name that means no variant or constant there, and its error.
    Failed(Failure),
}

/// The error of a name that means no variant or constant where a pattern writes it: E0211 when
/// it means nothing, with the names there close to it, and E0212 when it means something else.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Failure {
    /// E0211 or E0212.
    pub code: Code,
    /// Its message.
    pub message: String,
    /// For E0211, the names in scope close to the one written.
    pub close: Vec<Name>,
}

/// A field of a record pattern.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldPat {
    /// The field's name.
    pub field: Ident,
    /// The pattern its value matches.
    pub pattern: Pat,
}

/// What follows the elements of a list pattern.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ListRest {
    /// Nothing: the list has exactly the elements written.
    Exact,
    /// `..`, which binds nothing.
    Rest,
    /// A rest with a name, which binds the remaining elements to this local.
    Bind(LocalId),
}
