//! What a debugger needs of a function (goal debuggable-builds): where in the source its code comes
//! from, which `Stmt::At` marks, and how to show each named local's word: the whole value of a
//! type held in one word, and of one held in several, its words under names that say which part
//! of it each is, such as `p.x` or `o.0`. An array held in memory is one local, which a debugger
//! shows element by element, each element's words under the names of their parts.

use std::sync::Arc;

use serde::{Deserialize, Serialize};

/// How a debugger shows the word of a named local.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Shown {
    /// The local's type as the source writes it, such as `i64` or `List<str>`.
    pub name: Arc<str>,
    /// What its word holds.
    pub kind: ShownKind,
    /// Whether the local holds a pointer to the value rather than the value, as an `inout`
    /// parameter does.
    pub by_ref: bool,
    /// For the tag of a variant type held inline, the names of its variants, by their index.
    pub variants: Arc<[Arc<str>]>,
    /// For an array held in memory, its elements.
    pub elements: Option<ShownElements>,
}

/// The elements of an array held in memory (generics.large-arrays): their type, as the source
/// writes it, how many there are, and the words of each, in order, each under the name of the part
/// of the element that it holds, such as `.x` or `.0`, which is empty for an element of one word.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ShownElements {
    /// Their type.
    pub name: Arc<str>,
    /// How many there are.
    pub len: u32,
    /// The words of each, in order, each under its part's name.
    pub words: Arc<[(Arc<str>, Shown)]>,
}

/// What a word of a type holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ShownKind {
    /// An integer of this many bits, sign-extended to the word.
    Signed(u8),
    /// An integer of this many bits, zero-extended to the word.
    Unsigned(u8),
    /// A float of this many bits, in the low bits of the word.
    Float(u8),
    /// A `bool`.
    Bool,
    /// `()`, `Never`, or a value of a type parameter, whose word has no one meaning.
    Opaque,
    /// A string object.
    Str,
    /// A heap word: a pointer to any other object, or an immediate.
    Heap,
    /// The tag of a variant type held inline: the immediate of a variant's index.
    Tag,
    /// An array held in memory, whose elements [`Shown::elements`] gives.
    Array,
}
