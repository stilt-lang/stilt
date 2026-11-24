//! What each function does about the check of `without alloc` in debug builds
//! (facts.without-alloc): a function that the limit covers raises a count of limited frames, one
//! that allocates sets it to 0 while it runs, since a limited function reaches it only through a
//! function value whose facts it doesn't inherit (facts.calls-through-function-values), and the
//! runtime ends the program at an allocation while the count isn't 0. A program that no
//! `without alloc` limits has no guards, so its code is as it would be without the check.

use std::collections::HashMap;
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use stilt_db::{Database, Program};
use stilt_types::promises::{AllocGuards, Key, alloc_guards};

use crate::FnRef;
use crate::mir::Function;

/// What a function does about the check.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Guard {
    /// A `without alloc` limits it.
    Limited,
    /// It allocates, so the limits around it don't cover what it does.
    Allocating,
}

/// The guard of each function that has one.
pub type Guards = HashMap<FnRef, Guard>;

/// The guards of `functions`, those of a program's code.
#[must_use]
pub fn guards(db: &Database, program: Program, functions: &[Arc<Function>]) -> Guards {
    let known = alloc_guards(db, program);
    if known.limited.is_empty() {
        return Guards::new();
    }
    let guarded = functions
        .iter()
        .filter_map(|f| Some((f.name.clone(), guard(known, &f.name)?)));
    guarded.collect()
}

/// The guard of the code `f`. A closure's body is code of the function that writes it: one that
/// a limited function writes is covered by the limit, and any other may allocate. A function's
/// code used as a value, a dictionary's entry and the code that natives call only pass a call on
/// to code that guards itself. A constant's value and a variant's constructor allocate where
/// they are first read or called, which no limit covers, and so does a structural `show`.
fn guard(known: &AllocGuards, f: &FnRef) -> Option<Guard> {
    match f.generic() {
        FnRef::Closure(parent, _) => {
            let mut writer = &**parent;
            while let FnRef::Closure(outer, _) = writer {
                writer = outer;
            }
            let covered = key_of(writer).is_some_and(|k| known.limited.contains(&k));
            (!covered).then_some(Guard::Allocating)
        }
        FnRef::Const(_) | FnRef::MemberConst(..) | FnRef::Constructor(_) => Some(Guard::Allocating),
        FnRef::Structural(_, name, _) => name.starts_with("show").then_some(Guard::Allocating),
        f => {
            let key = key_of(f)?;
            if known.limited.contains(&key) {
                Some(Guard::Limited)
            } else {
                known.allocating.contains(&key).then_some(Guard::Allocating)
            }
        }
    }
}

/// The item whose facts the code of a function with a body has, if it is a function's.
#[must_use]
pub fn key_of(f: &FnRef) -> Option<Key> {
    match f.generic() {
        FnRef::Function(item) => Some(Key::Function(item.clone())),
        FnRef::Member(owner, name) => Some(Key::Member(owner.clone(), *name)),
        FnRef::ImplMethod(t, owner, name) => Some(Key::ImplMethod(t.clone(), owner.clone(), *name)),
        FnRef::DefaultMethod(t, name) => Some(Key::DefaultMethod(t.clone(), *name)),
        _ => None,
    }
}
