//! The fixed points of `copy` (facts.copy), and of the copies at calls that modes.shared-writes
//! makes shared, which allocate (facts.copy-at-call), as facts.inference solves implicit effects:
//! over the items that each body names, from the program's functions, each read once.

#![expect(
    clippy::drop_non_drop,
    reason = "salsa's macro drops each query's key, which interned names may leave with nothing \
              to free"
)]

use std::collections::{BTreeMap, HashSet};

use stilt_db::{Db, Program, SourceFile};
use stilt_mir::{Code, FnRef, code_of};
use stilt_types::promises::{self, Body, Effect, Key, Site};

use crate::modes::{SharedWrite, shared_writes};

/// How an item has an effect: its own code, through the operation this names, or through an
/// item it names that has it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Via {
    Own(String),
    Through(Key),
}

/// The items that have an effect.
pub(crate) type Reached = BTreeMap<Key, Via>;

/// The code of an item.
pub(crate) fn fn_ref(key: &Key) -> Option<FnRef> {
    match key {
        Key::Function(item) => Some(FnRef::Function(item.clone())),
        Key::Member(owner, name) => Some(FnRef::Member(owner.clone(), *name)),
        Key::ImplMethod(t, owner, name) => Some(FnRef::ImplMethod(t.clone(), owner.clone(), *name)),
        Key::DefaultMethod(t, name) => Some(FnRef::DefaultMethod(t.clone(), *name)),
        Key::BuiltIn(..) => None,
    }
}

/// The body of an item, if it has one.
pub(crate) fn body_of(db: &dyn Db, program: Program, key: &Key) -> Option<(SourceFile, u32)> {
    match code_of(db, program, fn_ref(key)?)? {
        Code::Body(file, index) => Some((file, index)),
        Code::Native => None,
    }
}

/// The shared modifications of an item's body (modes.shared-writes), relative to its start.
// Salsa takes a query's key by value.
#[allow(clippy::needless_pass_by_value)]
#[salsa::tracked(returns(ref))]
pub(crate) fn shared(db: &dyn Db, program: Program, key: Key) -> Vec<SharedWrite> {
    fn_ref(&key).map_or_else(Vec::new, |f| shared_writes(db, program, &f))
}

/// The shared modification that a site of `body` waits on, if modes.shared-writes makes it shared.
pub(crate) fn shared_at<'s>(
    shared: &'s [SharedWrite],
    pending: &promises::Pending,
) -> Option<&'s SharedWrite> {
    shared
        .iter()
        .find(|w| w.binding == pending.binding && w.at == pending.modified)
}

/// What a fixed point needs of one body: whether its own code has the effect, through the
/// operation named, the items it names, and whether a `without` limits it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Summary {
    own: Option<String>,
    names: Vec<Key>,
    limited: bool,
}

/// A body's summary for `copy`: its first copy at a call (facts.copy-at-call), or its first shared
/// modification (facts.copy).
#[allow(clippy::needless_pass_by_value)]
#[salsa::tracked(returns(ref))]
pub(crate) fn copy_summary(db: &dyn Db, program: Program, key: Key) -> Option<Summary> {
    let (file, index) = body_of(db, program, &key)?;
    let body = promises::body(db, program, file, index)?;
    let own = body
        .sites
        .iter()
        .find_map(|s| s.copy().map(|f| f.a.clone()))
        .or_else(|| {
            shared(db, program, key.clone())
                .first()
                .map(|w| super::write(w, false))
        });
    Some(summarized(&body, own, body.limits.copy))
}

/// A body's summary for the copies at calls that a shared modification makes allocate: its first
/// `inout` argument of an in-place parameter that modes.shared-writes makes shared
/// (facts.copy-at-call). Its shared modifications are read only when it has such an argument.
#[allow(clippy::needless_pass_by_value)]
#[salsa::tracked(returns(ref))]
pub(crate) fn alloc_summary(db: &dyn Db, program: Program, key: Key) -> Option<Summary> {
    let (file, index) = body_of(db, program, &key)?;
    let body = promises::body(db, program, file, index)?;
    let mut waiting = body
        .sites
        .iter()
        .filter_map(|s| s.pending().filter(|p| p.callee.is_some()))
        .peekable();
    let own = if waiting.peek().is_some() {
        let shared = shared(db, program, key.clone());
        waiting.find_map(|p| shared_at(shared, p).map(|w| super::passing(p, w, &body, false)))
    } else {
        None
    };
    Some(summarized(&body, own, body.limits.alloc))
}

fn summarized(body: &Body, own: Option<String>, limited: bool) -> Summary {
    Summary {
        own,
        names: body.sites.iter().flat_map(Site::names).cloned().collect(),
        limited,
    }
}

/// The items of the program, and those they name, that have the effect that `summary` gives
/// their bodies, as a least fixed point. A limited item counts as one without it, since its own
/// operations are errors where they are written (facts.without-copy).
fn reach(db: &dyn Db, program: Program, summary: &dyn Fn(Key) -> Option<Summary>) -> Reached {
    let mut all: Vec<(Key, Summary)> = Vec::new();
    let mut seen: HashSet<Key> = HashSet::new();
    let mut next: Vec<Key> = roots(db, program);
    while let Some(key) = next.pop() {
        if !seen.insert(key.clone()) {
            continue;
        }
        if let Some(s) = summary(key.clone()) {
            next.extend(s.names.iter().filter(|k| !seen.contains(*k)).cloned());
            all.push((key, s));
        }
    }
    let mut reached = Reached::new();
    loop {
        let found: Vec<(Key, Via)> = all
            .iter()
            .filter(|(k, s)| !s.limited && !reached.contains_key(k))
            .filter_map(|(k, s)| {
                if let Some(own) = &s.own {
                    return Some((k.clone(), Via::Own(own.clone())));
                }
                let through = s.names.iter().find(|n| reached.contains_key(*n))?;
                Some((k.clone(), Via::Through(through.clone())))
            })
            .collect();
        if found.is_empty() {
            return reached;
        }
        reached.extend(found);
    }
}

/// The functions of the program's own files, where the fixed points start.
fn roots(db: &dyn Db, program: Program) -> Vec<Key> {
    let files: HashSet<SourceFile> = program.files(db).iter().copied().collect();
    let mut keys: Vec<Key> = stilt_mir::bodies(db, program)
        .code
        .iter()
        .filter(|(_, code)| matches!(code, Code::Body(file, _) if files.contains(file)))
        .filter_map(|(f, _)| key_of(f))
        .collect();
    keys.sort();
    keys
}

/// The item of a function's code.
fn key_of(f: &FnRef) -> Option<Key> {
    match f {
        FnRef::Function(item) => Some(Key::Function(item.clone())),
        FnRef::Member(owner, name) => Some(Key::Member(owner.clone(), *name)),
        FnRef::ImplMethod(t, owner, name) => Some(Key::ImplMethod(t.clone(), owner.clone(), *name)),
        FnRef::DefaultMethod(t, name) => Some(Key::DefaultMethod(t.clone(), *name)),
        _ => None,
    }
}

/// The items that copy shared data (facts.copy).
#[salsa::tracked(returns(ref))]
pub(crate) fn copies(db: &dyn Db, program: Program) -> Reached {
    reach(db, program, &|k| copy_summary(db, program, k).clone())
}

/// The items that allocate through a copy at a call that a shared modification makes, which
/// `stilt-types` can't see (facts.copy-at-call).
#[salsa::tracked(returns(ref))]
pub(crate) fn shared_allocs(db: &dyn Db, program: Program) -> Reached {
    reach(db, program, &|k| alloc_summary(db, program, k).clone())
}

/// The item whose own code gives `key` the effect, following `reached`, and that code's
/// operation.
pub(crate) fn origin<'k>(reached: &'k Reached, mut key: &'k Key) -> (&'k Key, Option<&'k str>) {
    loop {
        match reached.get(key) {
            Some(Via::Through(next)) => key = next,
            Some(Via::Own(op)) => return (key, Some(op)),
            None => return (key, None),
        }
    }
}

/// Whether the effect is `copy` or `alloc`, for the fixed point it reads.
pub(crate) fn reached(db: &dyn Db, program: Program, effect: Effect) -> &Reached {
    match effect {
        Effect::Copy => copies(db, program),
        _ => shared_allocs(db, program),
    }
}
