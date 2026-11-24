//! The types whose descriptors a debug build makes, as the functions that the
//! compiler makes for them name them: a type with the type parameters it holds numbered in the
//! order they first appear, so that one function describes every type of that form, given the
//! witness and the descriptor of each.

use std::fmt;

use serde::{Deserialize, Serialize};
use stilt_hir::hir::{DeclId, GenericId, Item, Name, Owner, Value};
use stilt_types::ty::Ty;

/// A type to describe, its type parameters numbered.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Described {
    /// A type constructor with its arguments.
    Con(Item, Box<[Described]>),
    /// A tuple type, by its elements.
    Tuple(Box<[Described]>),
    /// A value argument, as an array's size (generics.constant-arguments).
    Value(Value),
    /// The type parameter of this number, whose witness and descriptor the code is given.
    Param(u32),
    /// A type without a shape that meta.shapes gives no case and no impl of any trait: a function
    /// type or a handler type, by its name, whose pieces are text and the names of the type
    /// parameters of these numbers, and by the witness of its one word.
    Other(Box<[Piece]>, u64),
}

/// A piece of a type's name.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Piece {
    /// Text, as written.
    Text(Box<str>),
    /// The name of the type parameter of this number.
    Param(u32),
}

/// What a closure of a descriptor does with a value of its type, which it takes and gives in
/// the one word that holds it where a type parameter stands.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Access {
    /// The field of this place of a record or a tuple.
    Field(u32),
    /// The value that a closure of `fn<F>(Field<T, F>) -> F` gives each field.
    Build,
    /// `Some` of the payload of the variant of this place, as a tuple, or `None`.
    CaseGet(u32),
    /// The value of the variant of this place, from its payload as a tuple.
    CaseMake(u32),
    /// An option of the one word that holds its element, and back.
    OptionGet,
    /// The option back from the one word.
    OptionMake,
    /// An array's elements as a list, and back from a list of as many.
    ArrayGet,
    /// The array back from the list.
    ArrayMake,
}

/// What the code of a shape dictionary walks (traits.structural-impls): the fields of a
/// tuple or a record, the variants of a variant type, each with the tuple of its payload, or
/// the elements of an array, each through the accessors and the descriptors of its parts.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Walk {
    /// The fields of a tuple or a record.
    Fields,
    /// The variants of a variant type.
    Variants,
    /// The elements of an array.
    Array,
}

/// The module of the type parameters that a described type's numbers stand for.
const NUMBERED: &str = "#described";

/// The type parameter that number `i` stands for in the code of a descriptor.
#[must_use]
pub fn numbered(i: u32) -> GenericId {
    GenericId {
        owner: Owner {
            decl: DeclId {
                module: Name::from(NUMBERED),
                index: 0,
            },
            member: None,
        },
        index: i,
    }
}

/// The number that a type parameter of a descriptor's code stands for.
#[must_use]
pub fn number_of(g: &GenericId) -> Option<u32> {
    (&*g.owner.decl.module == NUMBERED).then_some(g.index)
}

impl Described {
    /// The type that the code of a descriptor holds, each number its type parameter
    /// ([`numbered`]); none for [`Described::Other`], which the code reads no type of.
    #[must_use]
    pub fn ty(&self) -> Option<Ty> {
        Some(match self {
            Self::Con(item, args) => Ty::Con(item.clone(), list(args)?),
            Self::Tuple(ts) => Ty::Tuple(list(ts)?),
            Self::Value(v) => Ty::Value(*v),
            Self::Param(i) => Ty::Param(numbered(*i)),
            Self::Other(..) => return None,
        })
    }
}

fn list(ds: &[Described]) -> Option<Vec<Ty>> {
    ds.iter().map(Described::ty).collect()
}

impl fmt::Display for Described {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let list = |ds: &[Described]| {
            ds.iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(",")
        };
        match self {
            Self::Con(i, ds) => write!(f, "{}.{}[{}]", i.home, i.name, list(ds)),
            Self::Tuple(ds) => write!(f, "({})", list(ds)),
            Self::Value(v) => write!(f, "{v}"),
            Self::Param(i) => write!(f, "'{i}"),
            Self::Other(pieces, _) => pieces.iter().try_for_each(|p| match p {
                Piece::Text(t) => write!(f, "{t}"),
                Piece::Param(i) => write!(f, "'{i}"),
            }),
        }
    }
}

impl fmt::Display for Walk {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Fields => write!(f, "fields"),
            Self::Variants => write!(f, "variants"),
            Self::Array => write!(f, "array"),
        }
    }
}

impl fmt::Display for Access {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Field(i) => write!(f, "field{i}"),
            Self::Build => write!(f, "build"),
            Self::CaseGet(i) => write!(f, "case{i}-get"),
            Self::CaseMake(i) => write!(f, "case{i}-make"),
            Self::OptionGet => write!(f, "option-get"),
            Self::OptionMake => write!(f, "option-make"),
            Self::ArrayGet => write!(f, "array-get"),
            Self::ArrayMake => write!(f, "array-make"),
        }
    }
}
