//! The editions of the language (editions.edition): each named for a year, with the methods of
//! `std`'s types that it renames. A package's manifest names its edition, and every edition is read
//! with its own meaning.

use std::sync::RwLock;

/// A method of a type of `std` that an edition renames (editions.renames).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Rename {
    /// The type, by its name in `std`, as `List`.
    pub owner: &'static str,
    /// The name of the method in the earlier edition.
    pub from: &'static str,
    /// The name of the method in the edition that renames it.
    pub to: &'static str,
}

/// An edition: its name, a year, and the renames it makes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Edition {
    /// The name of the edition.
    pub name: &'static str,
    /// The renames the edition makes.
    pub renames: &'static [Rename],
}

/// The editions, oldest first (editions.edition).
pub const EDITIONS: &[Edition] = &[Edition {
    name: "2027",
    renames: &[],
}];

/// The editions in force, which a toolchain's own tests may extend with editions to come, to
/// test `stilt migrate` before anyone needs it (editions.migrate).
static IN_FORCE: RwLock<&'static [Edition]> = RwLock::new(EDITIONS);

/// The editions this process reads, oldest first.
#[must_use]
pub fn editions() -> &'static [Edition] {
    *IN_FORCE
        .read()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// Makes this process read `editions`, which hold [`EDITIONS`] first, unchanged.
///
/// # Panics
///
/// When `editions` doesn't start with [`EDITIONS`], since an edition never changes once made.
pub fn extend(editions: &'static [Edition]) {
    assert!(editions.starts_with(EDITIONS), "an edition never changes");
    *IN_FORCE
        .write()
        .unwrap_or_else(std::sync::PoisonError::into_inner) = editions;
}

/// The first edition, which a package without an `edition` is of (editions.edition).
#[must_use]
pub fn first() -> &'static Edition {
    &editions()[0]
}

/// The newest edition.
#[must_use]
pub fn newest() -> &'static Edition {
    editions().last().unwrap_or(&EDITIONS[0])
}

/// The edition named `name`.
#[must_use]
pub fn named(name: &str) -> Option<&'static Edition> {
    editions().iter().find(|e| e.name == name)
}

/// The editions after `edition`, in order, which `stilt migrate` moves a package through.
#[must_use]
pub fn after(edition: &str) -> &'static [Edition] {
    let all = editions();
    let at = all
        .iter()
        .position(|e| e.name == edition)
        .map_or(all.len(), |i| i + 1);
    &all[at..]
}

/// The renames in force in a package of `edition`: those of every edition up to it, in order.
#[must_use]
pub fn renames(edition: &str) -> Vec<(Rename, &'static str)> {
    let all = editions();
    let upto = all
        .iter()
        .position(|e| e.name == edition)
        .map_or(0, |i| i + 1);
    all[..upto]
        .iter()
        .flat_map(|e| e.renames.iter().map(move |r| (*r, e.name)))
        .collect()
}

/// The editions as messages list them: `2027`, or `2027 and 2028`.
#[must_use]
pub fn listed() -> String {
    let names: Vec<&str> = editions().iter().map(|e| e.name).collect();
    match names.as_slice() {
        [] => String::new(),
        [one] => (*one).to_owned(),
        [init @ .., last] => format!("{} and {last}", init.join(", ")),
    }
}

/// What a method's name written in a package means, after the renames in force there: `std`
/// declares each method by its name in the first edition, which it is written in
/// (editions.renames).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Named<'a> {
    /// The method that `std` declares by this name.
    Declared(&'a str),
    /// A name that an edition took away: the method `std` declares by `declared`, which the
    /// package writes `newest`, since `edition` renamed it.
    Renamed {
        /// The name that `std` declares the method by.
        declared: &'static str,
        /// The name the package writes it by.
        newest: &'static str,
        /// The edition that renamed it.
        edition: &'static str,
    },
}

/// What `written`, a method of the `std` type `owner`, names under `renames`, those in force in
/// a package, in the order of their editions.
#[must_use]
pub fn resolve<'a>(renames: &[(Rename, &'static str)], owner: &str, written: &'a str) -> Named<'a> {
    // Each method that a rename reaches: its declared name, its names in order, and the edition
    // that took each but the last away.
    let mut tracks: Vec<(&'static str, Vec<&'static str>, Vec<&'static str>)> = Vec::new();
    for (r, edition) in renames.iter().filter(|(r, _)| r.owner == owner) {
        match tracks.iter_mut().find(|t| t.1.last() == Some(&r.from)) {
            Some(t) => {
                t.1.push(r.to);
                t.2.push(edition);
            }
            None => tracks.push((r.from, vec![r.from, r.to], vec![edition])),
        }
    }
    for (declared, names, editions) in &tracks {
        let newest = names[names.len() - 1];
        if written == newest {
            return Named::Declared(declared);
        }
        if let Some(i) = names.iter().position(|n| *n == written) {
            return Named::Renamed {
                declared,
                newest,
                edition: editions[i],
            };
        }
    }
    Named::Declared(written)
}
