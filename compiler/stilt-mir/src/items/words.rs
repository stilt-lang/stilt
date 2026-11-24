//! The words of an instance's key: what each word of a type argument's layout holds.

use std::fmt;

use serde::{Deserialize, Serialize};

use crate::mir::{Element, Elements, Table};

/// What a word of a type argument's layout holds, in the key of an instance: a scalar, a heap
/// word, a word whose heapness the witness of a type parameter of the caller tells, or the
/// words of an array held in memory (`crate::mir::Elements`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Word {
    /// A scalar.
    Scalar,
    /// A heap word.
    Heap,
    /// A word whose heapness the witness of a type parameter of the caller tells.
    Dynamic,
    /// The words of an array held in memory.
    Array(Elements<Word>),
}

static WORD_ARRAYS: Table<Word> = Table::new();

impl Element for Word {
    fn words(self) -> usize {
        match self {
            Word::Array(e) => e.words(),
            Word::Scalar | Word::Heap | Word::Dynamic => 1,
        }
    }

    fn counted(self) -> bool {
        match self {
            Word::Scalar => false,
            Word::Heap | Word::Dynamic => true,
            Word::Array(e) => e.counted(),
        }
    }

    fn table() -> &'static Table<Self> {
        &WORD_ARRAYS
    }
}

/// Writes the words of a key, as an instance's name holds them.
pub(super) fn write_words(f: &mut fmt::Formatter<'_>, words: &[Word]) -> fmt::Result {
    words.iter().try_for_each(|w| match w {
        Word::Scalar => write!(f, "s"),
        Word::Heap => write!(f, "h"),
        Word::Dynamic => write!(f, "d"),
        Word::Array(e) => {
            write!(f, "[")?;
            write_words(f, e.each())?;
            write!(f, ";{}]", e.len())
        }
    })
}
