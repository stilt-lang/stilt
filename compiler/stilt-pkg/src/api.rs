//! A package's API, and the change a version needs (versions.api and versions.change-needed).
//!
//! The API is what another package can use: each module, with its tier; each `pub` item, member,
//! trait method and visible trait impl, by its address, with its signature written so that it
//! doesn't depend on the names of generics and parameters, and its limitable facts, those of
//! its inferred facts that a `without` can name; the effects that the package's own code
//! performs; and whether its own code holds an `unsafe` block (c.unsafe-in-api). The compiler
//! fills it in.

use std::collections::BTreeMap;
use std::path::Path;

use crate::version::Change;

/// What gives the APIs of packages: the compiler, which checks each as the root of a program.
pub trait Apis {
    /// The API of the package in `dir`, or the code and the place of its first error, as
    /// `E0311 at csv/src/read.lt:14:22`, when it has errors.
    ///
    /// # Errors
    ///
    /// The first error of the package, checked as a program of its own
    /// (packages.dependencies-with-errors).
    fn api(&mut self, dir: &Path) -> Result<Api, String>;
}

/// The APIs of a reader that checks no version against another, as a reader of a program's
/// files alone needs.
#[derive(Debug)]
pub struct Unchecked;

impl Apis for Unchecked {
    fn api(&mut self, _: &Path) -> Result<Api, String> {
        Ok(Api::default())
    }
}

/// What an entry of an API is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// A module.
    Module,
    /// An item of a module: a function, type, trait or constant.
    Item,
    /// A function or constant of an inherent impl.
    Member,
    /// A method that a trait declares, which every impl of the trait must give.
    TraitMethod,
    /// An impl of a trait for a type.
    Impl,
}

/// An entry of an API: what another package can use at one address.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    /// What the entry is.
    pub kind: Kind,
    /// What can break: a signature, a type's fields or variants, a trait method's signature, an
    /// impl's bounds, or a module's tier.
    pub shape: String,
    /// Its limitable facts, as `without` names them, such as `panic`, `div` and `clock`, in the
    /// order that `stilt show` prints them.
    pub facts: Vec<String>,
    /// For a trait method, whether it has a default body.
    pub default: bool,
}

/// A package's API.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Api {
    /// The entries of the API, by address.
    pub entries: BTreeMap<String, Entry>,
    /// Whether the package's own code performs `io` (packages.own-effects).
    pub io: bool,
    /// Whether the package's own code holds an `unsafe` block, counted as  counts calls
    /// (c.unsafe-in-api).
    pub unsafe_code: bool,
}

/// One change between two APIs, by the address it is at, and what it does.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    /// The change of version that the change needs.
    pub needs: Change,
    /// The address the change is at.
    pub address: String,
    /// What the change does.
    pub what: String,
}

impl Step {
    /// What the change does, for messages, as in removes `json.decode.parse_int`.
    #[must_use]
    pub fn described(&self) -> String {
        if self.address.is_empty() {
            self.what.clone()
        } else {
            format!("{} `{}`", self.what, self.address)
        }
    }
}

/// The changes from `old` to `new`, in the order of their addresses (versions.change-needed).
#[must_use]
pub fn changes(old: &Api, new: &Api) -> Vec<Step> {
    let mut steps = Vec::new();
    let step = |needs, address: &str, what: &str| Step {
        needs,
        address: address.to_owned(),
        what: what.to_owned(),
    };
    for (address, before) in &old.entries {
        let Some(after) = new.entries.get(address) else {
            steps.push(step(Change::Major, address, "removes"));
            continue;
        };
        if before.shape != after.shape {
            let what = if before.kind == Kind::Module {
                tier_change(&before.shape, &after.shape)
            } else {
                (Change::Major, "changes")
            };
            steps.push(step(what.0, address, what.1));
        }
        effects(&mut steps, address, before, after);
        if before.default != after.default {
            let (needs, what) = if after.default {
                (Change::Minor, "gives a default body to")
            } else {
                (Change::Major, "takes the default body from")
            };
            steps.push(step(needs, address, what));
        }
    }
    for (address, entry) in &new.entries {
        if !old.entries.contains_key(address) {
            let needs = if entry.kind == Kind::TraitMethod {
                Change::Major
            } else {
                Change::Minor
            };
            steps.push(step(needs, address, "adds"));
        }
    }
    steps.extend(own_code(old, new));
    steps.sort_by(|a, b| a.address.cmp(&b.address));
    steps
}

/// The steps of what the package's own code does: starting to perform `io`, or to
/// hold an `unsafe` block (c.unsafe-in-api), breaks the manifests that don't grant it, and
/// stopping breaks none.
fn own_code(old: &Api, new: &Api) -> Vec<Step> {
    let facts = [
        (old.io, new.io, "perform `io`", "stop performing `io`"),
        (
            old.unsafe_code,
            new.unsafe_code,
            "hold an `unsafe` block",
            "stop holding `unsafe` blocks",
        ),
    ];
    facts
        .into_iter()
        .filter(|(before, after, ..)| before != after)
        .map(|(_, after, starts, stops)| {
            let (needs, what) = if after {
                (Change::Major, starts)
            } else {
                (Change::Minor, stops)
            };
            Step {
                needs,
                address: String::new(),
                what: format!("makes the package's own code {what}"),
            }
        })
        .collect()
}

/// The steps of the limitable facts that an entry gains or loses: a gained fact breaks the
/// callers that a limit bars it from, and a lost one breaks none.
fn effects(steps: &mut Vec<Step>, address: &str, before: &Entry, after: &Entry) {
    let gained = (after.facts.iter()).filter(|f| !before.facts.contains(f));
    let lost = (before.facts.iter()).filter(|f| !after.facts.contains(f));
    let changed = (gained.map(|f| (Change::Major, "gains", f)))
        .chain(lost.map(|f| (Change::Minor, "loses", f)));
    for (needs, verb, fact) in changed {
        steps.push(Step {
            needs,
            address: address.to_owned(),
            what: format!("{verb} `{fact}` in"),
        });
    }
}

/// What a change of a module's tier needs: a rise breaks the packages that use it.
fn tier_change(before: &str, after: &str) -> (Change, &'static str) {
    const TIERS: [&str; 4] = ["core", "advanced", "meta", "systems"];
    let rank = |t: &str| TIERS.iter().position(|x| *x == t).unwrap_or(0);
    if rank(after) > rank(before) {
        (Change::Major, "raises the tier of")
    } else {
        (Change::Minor, "lowers the tier of")
    }
}

/// The change from `old` to `new` that the version must make at least.
#[must_use]
pub fn needed(steps: &[Step]) -> Change {
    steps.iter().map(|s| s.needs).max().unwrap_or(Change::Patch)
}

#[cfg(test)]
mod tests;
