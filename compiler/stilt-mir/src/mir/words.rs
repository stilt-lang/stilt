//! What a local holds, and a field of a data object: a scalar, a heap word, a value of a type
//! parameter, whose witness tells at run time, or the words of an array held in memory
//! (generics.large-arrays), which take as many words as its elements do.

use serde::{Deserialize, Serialize};

use super::{Element, Elements, Local, Table};

/// What a local holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Repr {
    /// A scalar: an integer, a float's bits, a `bool` or `()`.
    Scalar,
    /// A heap word: a pointer to an object, or an immediate.
    Heap,
    /// A value of a type parameter, which is a heap word if the lowest bit of the witness in
    /// this local, its argument's shape (`crate::shape`), is set.
    Generic(Local),
    /// The words of an array held in memory, which a local of this representation holds in a
    /// slot of the frame and an operand that names it stands for: an assignment copies them,
    /// a copy or a release counts each word of its elements that may need it, and memory,
    /// objects and lists hold them one after the other, as they hold a value's words.
    Array(Elements<Repr>),
}

impl Repr {
    /// Whether values of this representation may need their references counted.
    #[must_use]
    pub fn counted(self) -> bool {
        match self {
            Repr::Scalar => false,
            Repr::Heap | Repr::Generic(_) => true,
            Repr::Array(e) => e.counted(),
        }
    }

    /// The number of words that a value of this representation takes in memory.
    #[must_use]
    pub fn words(self) -> usize {
        match self {
            Repr::Array(e) => e.words(),
            Repr::Scalar | Repr::Heap | Repr::Generic(_) => 1,
        }
    }

    /// The representation with each word of a type parameter's as `f` gives it, from its
    /// witness, or `None` if `f` gives none for one.
    pub fn map_witnesses(self, f: &impl Fn(Local) -> Option<Repr>) -> Option<Repr> {
        match self {
            Repr::Generic(w) => f(w),
            Repr::Array(e) => e.map(|r| r.map_witnesses(f)).map(Repr::Array),
            Repr::Scalar | Repr::Heap => Some(self),
        }
    }

    /// The locals whose witnesses tell the heapness of its words.
    #[must_use]
    pub fn witnesses(self) -> Vec<Local> {
        match self {
            Repr::Generic(w) => vec![w],
            Repr::Array(e) => e.each().iter().flat_map(|r| r.witnesses()).collect(),
            Repr::Scalar | Repr::Heap => Vec::new(),
        }
    }
}

static REPR_ARRAYS: Table<Repr> = Table::new();

impl Element for Repr {
    fn words(self) -> usize {
        Repr::words(self)
    }

    fn counted(self) -> bool {
        Repr::counted(self)
    }

    fn table() -> &'static Table<Self> {
        &REPR_ARRAYS
    }
}

/// The word offset of each of the values of these representations, one after the other in
/// memory, and the words they take in all.
#[must_use]
pub fn offsets(reprs: impl IntoIterator<Item = Repr>) -> (Vec<usize>, usize) {
    let mut at = 0;
    let offsets = reprs
        .into_iter()
        .map(|r| {
            let here = at;
            at += r.words();
            here
        })
        .collect();
    (offsets, at)
}

/// Whether a field of a data object being built holds a heap word.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Heapness {
    /// A heap word, or not, whatever the type arguments.
    Static(bool),
    /// As the lowest bit of the witness in this local says.
    Witness(Local),
    /// The words of an array held in memory, which a local of this representation holds, each
    /// a heap word as its representation says.
    Array(Elements<Repr>),
}

impl Heapness {
    /// The heapness of a field of the representation `repr`.
    #[must_use]
    pub fn of(repr: Repr) -> Self {
        match repr {
            Repr::Scalar => Heapness::Static(false),
            Repr::Heap => Heapness::Static(true),
            Repr::Generic(w) => Heapness::Witness(w),
            Repr::Array(e) => Heapness::Array(e),
        }
    }

    /// The locals whose witnesses tell the heapness of its words.
    #[must_use]
    pub fn witnesses(self) -> Vec<Local> {
        match self {
            Heapness::Witness(w) => vec![w],
            Heapness::Array(e) => Repr::Array(e).witnesses(),
            Heapness::Static(_) => Vec::new(),
        }
    }

    /// The words of the field.
    #[must_use]
    pub fn words(self) -> usize {
        match self {
            Heapness::Array(e) => e.words(),
            Heapness::Static(_) | Heapness::Witness(_) => 1,
        }
    }
}
