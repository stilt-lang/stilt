//! The inferred fact `reflects T` (meta.reflects), the types whose descriptors a debug build
//! passes, and E0350 where a type without a shape is given to a function that
//! reflects (meta.types-without-shape).
//!
//! A function reflects on a type parameter when its body names its shape, or gives it to a type
//! parameter of a function that reflects on it, and on its parts when it gives a fresh type of
//! its shape to one. The facts are a fixed point over the uses of every function of the program and
//! the standard library, as implicit effects are (facts.interfaces and facts.visibility), read from
//! one summary of each body, so an edit of a body reads no other body's types.

mod bounds;
mod check;
pub(crate) mod queries;
mod shapes;
mod summary;

use std::collections::BTreeMap;

use stilt_hir::hir::{DeclId, GenericId, Item, Name, Owner};

pub use crate::analyses::implicit::Key;
pub(crate) use check::{Names, errors};
pub use queries::{Carried, carried, reflected, reflects as facts_of, tested_traits};
use summary::params_of;
pub(crate) use summary::{Summary, summary};

use crate::ty::Ty;

/// How a function reflects on one of its type parameters.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Reflects {
    /// Whether it reflects on the types its fields, elements and payloads hold.
    pub parts: bool,
    /// The traits whose impl a type may have in place of a shape (meta.types-without-shape).
    pub guards: Vec<Item>,
    /// The functions that reflect, from this one to the one that names `T.shape()`.
    pub chain: Vec<Key>,
}

/// What a function reads of one of its type parameters at run time: its descriptor, which a
/// debug build passes, and whether it reflects on it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Fact {
    /// The type parameter.
    pub param: GenericId,
    /// How it reflects on the parameter, if it does.
    pub reflects: Option<Reflects>,
}

/// The facts of each function that reads a type parameter's descriptor, by its key.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Reflections {
    facts: BTreeMap<Key, Vec<Fact>>,
}

impl Reflections {
    /// The facts of the functions `facts` gives, for a body's checks.
    #[must_use]
    pub(crate) fn of_functions(facts: Vec<(Key, Vec<Fact>)>) -> Self {
        Self {
            facts: facts.into_iter().filter(|(_, f)| !f.is_empty()).collect(),
        }
    }

    /// The facts of a function, none when it reads no descriptor.
    #[must_use]
    pub fn of(&self, key: &Key) -> &[Fact] {
        self.facts.get(key).map_or(&[], Vec::as_slice)
    }

    /// Every function's facts.
    pub(crate) fn all(&self) -> impl Iterator<Item = (&Key, &Vec<Fact>)> {
        self.facts.iter()
    }

    /// The fact of one of a function's type parameters.
    #[must_use]
    pub fn param(&self, key: &Key, param: &GenericId) -> Option<&Fact> {
        self.of(key).iter().find(|f| f.param == *param)
    }

    /// Records that `key` reads `param`'s descriptor, and reflects on it as `with` says, if it
    /// does; tells whether that is new.
    fn add(&mut self, key: &Key, param: &GenericId, with: Option<Reflects>) -> bool {
        let facts = self.facts.entry(key.clone()).or_default();
        let Some(fact) = facts.iter_mut().find(|f| f.param == *param) else {
            facts.push(Fact {
                param: param.clone(),
                reflects: with,
            });
            return true;
        };
        let Some(new) = with else {
            return false;
        };
        match &mut fact.reflects {
            None => {
                fact.reflects = Some(new);
                true
            }
            Some(r) => {
                let mut changed = new.parts && !r.parts;
                r.parts |= new.parts;
                for g in new.guards {
                    if !r.guards.contains(&g) {
                        r.guards.push(g);
                        changed = true;
                    }
                }
                changed
            }
        }
    }
}

/// `Self` in a trait's default method, as the facts of reflection name it: a type that each
/// impl gives, as it gives the trait's parameters, whose descriptor the dictionary holds.
#[must_use]
pub fn self_param() -> GenericId {
    GenericId {
        owner: Owner {
            decl: DeclId {
                module: Name::from("#Self"),
                index: 0,
            },
            member: None,
        },
        index: 0,
    }
}

/// The key under which the facts of reflection gather what a trait's default methods read of
/// `Self` and of the trait's parameters, which every default then takes: one that names no
/// method.
#[must_use]
pub fn of_defaults(t: &Item) -> Key {
    Key::DefaultMethod(t.clone(), Name::from(""))
}

/// Whether a type parameter is one a body declares or is given, rather than a fresh type of a
/// shape or a rigid type of a polymorphic function type.
fn own(g: &GenericId) -> bool {
    !g.is_fresh() && !g.is_poly()
}

/// The guards of the type `t` in a body: the traits its bound tests on `t` name.
fn guards_of(s: &Summary, t: &Ty) -> Vec<Item> {
    let mut found: Vec<Item> = Vec::new();
    for (u, tr) in &s.guards {
        if u == t && !found.contains(tr) {
            found.push(tr.clone());
        }
    }
    found
}

/// The type parameter of the body whose shape a fresh type is a part of, through the fresh
/// types whose shapes hold it, if it is one.
fn root_param(s: &Summary, fresh: &GenericId) -> Option<GenericId> {
    let mut at = fresh.clone();
    for _ in 0..=s.fresh_of.len() {
        let (_, of) = s.fresh_of.iter().find(|(f, _)| *f == at)?;
        match of {
            Ty::Param(g) if own(g) => return Some(g.clone()),
            Ty::Param(g) => at = g.clone(),
            _ => return None,
        }
    }
    None
}

/// The facts of the program's functions, from every body's summary.
#[must_use]
pub(crate) fn solve(summaries: &[Summary]) -> Reflections {
    let mut r = Reflections::default();
    for s in summaries {
        for (t, _) in &s.shapes {
            if let Ty::Param(g) = t
                && own(g)
            {
                let with = Reflects {
                    parts: false,
                    guards: guards_of(s, t),
                    chain: vec![s.key.clone()],
                };
                r.add(&s.key, g, Some(with));
            }
        }
        for t in &s.described {
            let mut found = Vec::new();
            params_of(t, &mut found);
            for g in found.iter().filter(|g| own(g)) {
                r.add(&s.key, g, None);
            }
        }
    }
    while summaries
        .iter()
        .any(|s| through_uses(&mut r, s) | to_trait(&mut r, s))
    {}
    r
}

/// Adds to the trait's method what an impl's method reads of its own type parameters, so that
/// every call through the trait, which can't see the impl, passes their descriptors, and to
/// the trait what a default method reads of `Self` and of the trait's parameters
/// ([`of_defaults`]), telling whether that added anything.
fn to_trait(r: &mut Reflections, s: &Summary) -> bool {
    let read: Vec<GenericId> = r.of(&s.key).iter().map(|f| f.param.clone()).collect();
    let mut changed = false;
    match &s.key {
        Key::ImplMethod(t, _, name) => {
            let key = Key::DefaultMethod(t.clone(), *name);
            for (own, of_trait) in &s.to_trait {
                if read.contains(own) {
                    changed |= r.add(&key, of_trait, None);
                }
            }
        }
        Key::DefaultMethod(t, _) => {
            let key = of_defaults(t);
            for g in read.iter().filter(|g| g.owner.member.is_none()) {
                changed |= r.add(&key, g, None);
            }
        }
        _ => {}
    }
    changed
}

/// Adds what a body's uses make it read, telling whether that added anything.
fn through_uses(r: &mut Reflections, s: &Summary) -> bool {
    let mut changed = false;
    for u in &s.uses {
        let callee: Vec<Fact> = r.of(&u.callee).to_vec();
        for (cg, x) in &u.targs {
            let Some(fact) = callee.iter().find(|f| f.param == *cg) else {
                continue;
            };
            let mut named = Vec::new();
            params_of(x, &mut named);
            for g in named.iter().filter(|g| own(g)) {
                changed |= r.add(&s.key, g, None);
            }
            let Some(with) = &fact.reflects else {
                continue;
            };
            let mut chain = vec![s.key.clone()];
            chain.extend(with.chain.iter().cloned());
            let mut reflect = |g: &GenericId, parts: bool| {
                let new = Reflects {
                    parts,
                    guards: with.guards.clone(),
                    chain: chain.clone(),
                };
                r.add(&s.key, g, Some(new))
            };
            for g in &named {
                if own(g) {
                    let whole = *x == Ty::Param(g.clone());
                    if whole || with.parts {
                        changed |= reflect(g, !whole || with.parts);
                    }
                } else if let Some(root) = root_param(s, g) {
                    changed |= reflect(&root, true);
                }
            }
        }
    }
    changed
}
