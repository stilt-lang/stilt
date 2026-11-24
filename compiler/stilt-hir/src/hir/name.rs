//! Names, interned: a name is four bytes, copied for free, and its text is held once for the
//! life of the process (goal bounded-cache). Two names are equal when their texts are, and
//! they hash and order as their texts do, so that every map, set and sort behaves as it would
//! over the texts.

use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt;
use std::hash::{BuildHasher, Hash, Hasher};
use std::ops::Deref;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Mutex, OnceLock, PoisonError};

use rustc_hash::FxBuildHasher;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// A name, by its place in the process's table of names.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Name(u32);

/// The texts of the names, in chunks made as they fill, so that a name's text is read without
/// a lock.
const CHUNK_BITS: u32 = 12;
const CHUNK: usize = 1 << CHUNK_BITS;
const CHUNKS: usize = 1 << 12;

type Chunk = Box<[OnceLock<&'static str>]>;

static TEXTS: [OnceLock<Chunk>; CHUNKS] = [const { OnceLock::new() }; CHUNKS];

/// The names by their texts, in shards, so that the threads that resolve modules at once
/// rarely wait for one another.
const SHARDS: usize = 64;

type Shard = Mutex<HashMap<&'static str, u32, FxBuildHasher>>;

static IDS: [OnceLock<Shard>; SHARDS] = [const { OnceLock::new() }; SHARDS];

static NEXT: AtomicU32 = AtomicU32::new(0);

impl Name {
    /// The name whose text is `text`.
    ///
    /// # Panics
    ///
    /// When the process has made 16 million names, far more than any program has.
    #[must_use]
    pub fn new(text: &str) -> Self {
        let shard = FxBuildHasher.hash_one(text) % SHARDS as u64;
        let shard = &IDS[usize::try_from(shard).unwrap_or_default()];
        let mut ids = shard
            .get_or_init(Mutex::default)
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        if let Some(&id) = ids.get(text) {
            return Self(id);
        }
        let id = NEXT.fetch_add(1, Ordering::Relaxed);
        let text: &'static str = Box::leak(text.into());
        let chunk = TEXTS
            .get((id >> CHUNK_BITS) as usize)
            .expect("a program has fewer than 16 million names")
            .get_or_init(|| (0..CHUNK).map(|_| OnceLock::new()).collect());
        let _ = chunk[id as usize % CHUNK].set(text);
        ids.insert(text, id);
        Self(id)
    }

    /// The name's text.
    ///
    /// # Panics
    ///
    /// Never: a name is made only once its text is in the table.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        TEXTS[(self.0 >> CHUNK_BITS) as usize]
            .get()
            .and_then(|chunk| chunk[self.0 as usize % CHUNK].get())
            .expect("a name's text is set before the name is made")
    }
}

impl Default for Name {
    fn default() -> Self {
        Self::new("")
    }
}

impl Deref for Name {
    type Target = str;

    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<str> for Name {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl Borrow<str> for Name {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl Hash for Name {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl PartialOrd for Name {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Name {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.0 == other.0 {
            std::cmp::Ordering::Equal
        } else {
            self.as_str().cmp(other.as_str())
        }
    }
}

impl PartialEq<str> for Name {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<&str> for Name {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

impl fmt::Debug for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), f)
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

impl From<&str> for Name {
    fn from(text: &str) -> Self {
        Self::new(text)
    }
}

impl From<&String> for Name {
    fn from(text: &String) -> Self {
        Self::new(text)
    }
}

impl From<String> for Name {
    fn from(text: String) -> Self {
        Self::new(&text)
    }
}

impl From<Name> for std::sync::Arc<str> {
    fn from(name: Name) -> Self {
        Self::from(name.as_str())
    }
}

impl From<Name> for String {
    fn from(name: Name) -> Self {
        name.as_str().to_owned()
    }
}

impl Serialize for Name {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.as_str())
    }
}

impl<'de> Deserialize<'de> for Name {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let text = <std::borrow::Cow<'de, str>>::deserialize(deserializer)?;
        Ok(Self::new(&text))
    }
}

#[cfg(test)]
mod tests {
    use super::Name;

    #[test]
    fn a_name_is_its_text() {
        let a = Name::from("main.totals");
        let b = Name::from(String::from("main.totals"));
        assert_eq!(a, b);
        assert_eq!(&*a, "main.totals");
        assert_ne!(a, Name::from("main.total"));
        assert!(Name::from("b") > Name::from("a"));
        assert_eq!(format!("{a} {a:?}"), "main.totals \"main.totals\"");
    }

    #[test]
    fn names_hash_as_their_texts() {
        use std::collections::HashSet;
        let set: HashSet<Name> = ["x", "y"].map(Name::from).into_iter().collect();
        assert!(set.contains("x"));
        assert!(!set.contains("z"));
    }
}
