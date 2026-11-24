//! Arrays held in memory (generics.large-arrays and generics.array-effects): the words of an array
//! past [`MEMORY_WORDS`] are one local of the MIR, which lives in a slot of the frame, rather than
//! a local per word, so that making, copying, passing, returning and counting one compiles to a
//! copy or a loop over its memory, whatever its size. Its layout is `len` elements, each in the
//! words of `each`, one after the other, as an array held in words has them, so memory, objects and
//! lists hold its words as they would any other value's.
//!
//! A layout is interned for the life of the process, so that it is copied for free, as a name
//! is; two are equal, hash and order as their contents do.

use std::collections::HashSet;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::{Mutex, OnceLock, PoisonError};

use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// The most words an array holds in words, a local each; one of more is held in memory. Past
/// 16 words, as many as x86-64's general registers and half of aarch64's, code that works on a
/// value spills most of its words to the frame anyway, so holding it in memory costs its reads
/// little, while each copy, call and count of it becomes one copy or loop instead of code per
/// word. An array of 16 words, as a 4×4 matrix of `f64`, stays in words.
pub const MEMORY_WORDS: usize = 16;

// An array in memory takes more than one word, so that it is never the one word that generic
// code and the runtime take a value of a type parameter in, unboxed.
const _: () = assert!(MEMORY_WORDS >= 1);

/// What an array's element is made of: a word of the MIR's, or of an instance's key.
pub trait Element: Copy + Eq + Hash + fmt::Debug + Send + Sync + 'static {
    /// The words it takes.
    fn words(self) -> usize;
    /// Whether one of its words may need its references counted.
    fn counted(self) -> bool;
    #[doc(hidden)]
    fn table() -> &'static Table<Self>;
}

/// The layouts of one kind that the process has made.
pub struct Table<T: 'static>(OnceLock<Mutex<HashSet<&'static Layout<T>>>>);

impl<T> Table<T> {
    /// A table that holds nothing yet.
    #[must_use]
    pub const fn new() -> Self {
        Self(OnceLock::new())
    }
}

impl<T> fmt::Debug for Table<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Table")
    }
}

impl<T> Default for Table<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// The layout of an array held in memory.
#[derive(Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Layout<T> {
    len: u32,
    each: Box<[T]>,
}

/// An array held in memory: `len` elements of the words `each`, interned.
pub struct Elements<T: 'static>(&'static Layout<T>);

impl<T: Element> Elements<T> {
    /// The layout of `len` elements of the words `each`.
    ///
    /// # Panics
    ///
    /// Never: the table's lock is only poisoned by a panic while it is held, and the table is
    /// still whole then.
    #[must_use]
    pub fn new(len: u32, each: Vec<T>) -> Self {
        let layout = Layout {
            len,
            each: each.into_boxed_slice(),
        };
        let mut table = T::table()
            .0
            .get_or_init(Mutex::default)
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        if let Some(&known) = table.get(&layout) {
            return Self(known);
        }
        let leaked: &'static Layout<T> = Box::leak(Box::new(layout));
        table.insert(leaked);
        Self(leaked)
    }

    /// The number of elements.
    #[must_use]
    pub fn len(self) -> u32 {
        self.0.len
    }

    /// Whether it has no elements.
    #[must_use]
    pub fn is_empty(self) -> bool {
        self.0.len == 0
    }

    /// The words of one element.
    #[must_use]
    pub fn each(self) -> &'static [T] {
        &self.0.each
    }

    /// The number of words of one element.
    #[must_use]
    pub fn element_words(self) -> usize {
        self.0.each.iter().map(|w| w.words()).sum()
    }

    /// The number of words of the whole array.
    #[must_use]
    pub fn words(self) -> usize {
        self.0.len as usize * self.element_words()
    }

    /// Whether some word of it may need its references counted.
    #[must_use]
    pub fn counted(self) -> bool {
        self.0.len > 0 && self.0.each.iter().any(|w| w.counted())
    }

    /// The same number of elements, each word of an element as `f` gives it, or `None` if `f`
    /// gives none for one.
    pub fn map<U: Element>(self, mut f: impl FnMut(T) -> Option<U>) -> Option<Elements<U>> {
        let each = self
            .0
            .each
            .iter()
            .map(|&w| f(w))
            .collect::<Option<Vec<U>>>()?;
        Some(Elements::new(self.0.len, each))
    }
}

impl<T> Clone for Elements<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Elements<T> {}

impl<T: PartialEq> PartialEq for Elements<T> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0) || self.0 == other.0
    }
}

impl<T: Eq> Eq for Elements<T> {}

impl<T: Hash> Hash for Elements<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<T: Ord> PartialOrd for Elements<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Ord> Ord for Elements<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(other.0)
    }
}

impl<T: fmt::Debug> fmt::Debug for Elements<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{:?}; {}]", self.0.each, self.0.len)
    }
}

impl<T: Element + Serialize> Serialize for Elements<T> {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        (self.0.len, &*self.0.each).serialize(s)
    }
}

impl<'de, T: Element + Deserialize<'de>> Deserialize<'de> for Elements<T> {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let (len, each) = <(u32, Vec<T>)>::deserialize(d)?;
        Ok(Self::new(len, each))
    }
}
