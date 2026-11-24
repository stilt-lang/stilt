//! Consumption as queries of the database (values.consumed-parameters). Each body's [`Summary`] is
//! cached on its own, and [`consumed`] gives one function's share of the fixed point over them, so
//! that an edit which changes what one function consumes reaches only the code of the functions
//! that call it, while every other edit leaves every convention as it was. Type checking never
//! reads these queries, so editing a body never checks its callers again (facts.interfaces).
//!
//! What a function consumes follows only its own summary and what the functions it passes a
//! parameter to consume, so the fixed point over the functions that some code calls, and those
//! they pass parameters to, and so on, gives each of them what the fixed point over every
//! function of the program and the standard library gives it ([`consumption_of`]). A build or
//! a run thus summarizes only the functions it reaches, which it has lowered already, and never
//! the rest of the standard library.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use stilt_hir::hir::Name;

use stilt_db::{Db, Program, parallel};
use stilt_mir::mir::Function;
use stilt_mir::{Code, FnRef, bodies};

use crate::consume::{self, Conventions, Summary};
use crate::fixpoint::solve;

/// Whether direct calls reach the function, so that its convention follows what it consumes.
/// Closures, the code of functions and variants used as values, and the entries of
/// dictionaries are called through values, all in one convention that borrows every `let`
/// parameter; the ones that call a function directly are its adapters, which give it the
/// arguments it consumes.
pub(crate) fn inferred(f: &FnRef) -> bool {
    matches!(
        f.generic(),
        FnRef::Function(_) | FnRef::Member(..) | FnRef::ImplMethod(..) | FnRef::DefaultMethod(..)
    )
}

/// What the body of `f` does with its parameters, if `f` has a body whose convention is
/// inferred. It reads the MIR that a build keeps of the functions it reaches, since only those
/// are summarized for it, and the functions they pass parameters to, which they reach too, and
/// the typed body for the parameters it takes apart to build in their place.
// Salsa takes a query's key by value.
#[allow(clippy::needless_pass_by_value)]
#[salsa::tracked(returns(ref))]
fn summary_of(db: &dyn Db, program: Program, f: FnRef) -> Option<Summary> {
    let functions = stilt_mir::functions(db, program, f.clone());
    let g = functions.iter().find(|g| g.name == f)?;
    let mut summary = consume::summary(g);
    summary.consumed.extend(apart_positions(db, program, g));
    summary.consumed.sort_unstable();
    summary.consumed.dedup();
    Some(summary)
}

/// The positions of the parameters of `g`'s code that its body takes apart to build in their
/// place (values.consumed-parameters).
fn apart_positions(db: &dyn Db, program: Program, g: &Function) -> Vec<usize> {
    let names = consume::apart::taken_apart(db, program, &g.name);
    if names.is_empty() {
        return Vec::new();
    }
    (g.hidden as usize..g.params.len())
        .filter(|&i| g.locals[g.params[i].local.0 as usize].repr.counted())
        .filter(|&i| source_name(g, i).is_some_and(|n| names.contains(&n)))
        .collect()
}

/// The parameters, by position, that each function consumes.
pub(crate) type Consumption = HashMap<FnRef, Vec<usize>>;

/// What each of `wanted` consumes, with the functions it passes parameters to, and so on: the
/// fixed point over their summaries, which gives each what the fixed point over every function
/// gives it. The summaries are read a wave at a time, each wave first by `summarize`, which
/// reads them across the machine's cores for a caller that can share its database.
fn closure_of(
    db: &dyn Db,
    program: Program,
    wanted: impl IntoIterator<Item = FnRef>,
    summarize: &dyn Fn(&[FnRef]),
) -> Consumption {
    let code = &bodies(db, program).code;
    let summarized = |f: &FnRef| inferred(f) && matches!(code.get(f), Some(Code::Body(..)));
    let mut seen = HashSet::new();
    let mut wave: Vec<FnRef> = wanted
        .into_iter()
        .filter(|f| summarized(f) && seen.insert(f.clone()))
        .collect();
    let mut all = Vec::new();
    while !wave.is_empty() {
        summarize(&wave);
        let mut next = Vec::new();
        for f in &wave {
            let passed = summary_of(db, program, f.clone())
                .iter()
                .flat_map(|s| &s.passed);
            for (_, g, _) in passed {
                if summarized(g) && seen.insert(g.clone()) {
                    next.push(g.clone());
                }
            }
        }
        all.append(&mut wave);
        wave = next;
    }
    let summaries: Vec<(FnRef, &Summary)> = all
        .into_iter()
        .filter_map(|f| {
            let summary = summary_of(db, program, f.clone()).as_ref()?;
            Some((f, summary))
        })
        .collect();
    solve(&summaries)
}

/// What every function of `functions` and each function it calls directly consumes, as
/// [`conventions_by`] reads it for their code, but those that `known` gives already, with the
/// summaries read across the machine's cores (goal clean-debug-build).
pub(crate) fn consumption_of<D: Db + Clone>(
    db: &D,
    program: Program,
    functions: &[Arc<Function>],
    known: &Consumption,
) -> Consumption {
    let wanted = functions
        .iter()
        .flat_map(|f| std::iter::once(&f.name).chain(consume::direct_callees(f)))
        .map(|g| g.generic().clone())
        .filter(|g| !known.contains_key(g));
    let summarize = |wave: &[FnRef]| {
        parallel::for_each(db, wave, |db, f| {
            summary_of(db, program, f.clone());
        });
    };
    closure_of(db, program, wanted, &summarize)
}

/// The parameters of `f`, by position, that it consumes, so that its callers give it their
/// arguments for them rather than lend them. A function called only through values, and a
/// native, consumes none.
// Salsa takes a query's key by value.
#[allow(clippy::needless_pass_by_value)]
#[salsa::tracked(returns(ref))]
pub fn consumed(db: &dyn Db, program: Program, f: FnRef) -> Vec<usize> {
    let consumption = closure_of(db, program, [f.generic().clone()], &|_| {});
    consumed_by(db, program, &consumption, &f)
}

/// The parameters of `f`, by position, that it consumes by `consumption`. An instance of a
/// generic function consumes the words of each of the source's parameters that the function
/// consumes, which its body consumes in every instance alike.
fn consumed_by(db: &dyn Db, program: Program, consumption: &Consumption, f: &FnRef) -> Vec<usize> {
    let of = |g: &FnRef| consumption.get(g).cloned().unwrap_or_default();
    let FnRef::Instance(g, _) = f else {
        return of(f);
    };
    let generic = of(g);
    if generic.is_empty() {
        return Vec::new();
    }
    let names = |h: &FnRef| -> Vec<Option<Name>> {
        stilt_mir::functions(db, program, h.clone())
            .iter()
            .find(|x| x.name == *h)
            .map(|x| (0..x.params.len()).map(|i| source_name(x, i)).collect())
            .unwrap_or_default()
    };
    let of_generic = names(g);
    let consumed: Vec<Name> = generic
        .iter()
        .filter_map(|&i| of_generic.get(i).copied().flatten())
        .collect();
    names(f)
        .iter()
        .enumerate()
        .filter(|(_, n)| n.as_ref().is_some_and(|n| consumed.contains(n)))
        .map(|(i, _)| i)
        .collect()
}

/// Where a function consumes a parameter: the parameter's name, the callee it passes the
/// parameter to when a call consumes it, and the location word of the code that does
/// (values.consumed-parameters).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Consuming {
    /// The parameter that is consumed.
    pub param: Name,
    /// The callee it is passed to, if the consuming is a call.
    pub through: Option<FnRef>,
    /// The location word of the code that consumes it.
    pub at: u64,
}

/// Each use by which `f` consumes a parameter that [`consumed`] says it consumes: a use that
/// consumes the parameter itself, as returning it does, or a direct call that passes it to a
/// parameter its callee consumes. `stilt show` prints them (goal shown-facts).
#[must_use]
pub fn consuming(db: &dyn Db, program: Program, f: &FnRef) -> Vec<Consuming> {
    let owned = consumed(db, program, f.clone());
    if owned.is_empty() {
        return Vec::new();
    }
    let functions = stilt_mir::functions(db, program, f.clone());
    let Some(g) = functions.iter().find(|g| g.name == *f) else {
        return Vec::new();
    };
    let apart = apart_positions(db, program, g)
        .into_iter()
        .filter(|p| owned.contains(p))
        .map(|param| consume::ParamUse {
            param,
            call: None,
            at: consume::first_read(g, param),
        });
    consume::param_uses(g)
        .into_iter()
        .chain(apart)
        .filter(|u| owned.contains(&u.param))
        .filter(|u| {
            u.call
                .as_ref()
                .is_none_or(|(callee, i)| consumed(db, program, callee.clone()).contains(i))
        })
        .filter_map(|u| {
            Some(Consuming {
                param: source_name(g, u.param)?,
                through: u.call.map(|(callee, _)| callee),
                at: u.at,
            })
        })
        .collect()
}

/// The name of the source's parameter that a parameter of `f`'s MIR holds a word of: a value
/// held inline takes a parameter for each word, named after the parameter and the word's
/// field, as `p.x` is. The parameters that the source doesn't write, such as dictionaries,
/// have none.
pub(crate) fn source_name(f: &Function, param: usize) -> Option<Name> {
    let name = f.locals[f.params.get(param)?.local.0 as usize]
        .name
        .as_ref()?;
    Some(match name.split_once('.') {
        Some((head, _)) => Name::from(head),
        None => *name,
    })
}

/// The conventions of a function's code: those of its own parameters, and of each function it
/// calls directly.
#[must_use]
pub fn conventions(db: &dyn Db, program: Program, f: &Function) -> Conventions {
    Conventions {
        owned: consumed(db, program, f.name.clone()).clone(),
        calls: consume::direct_callees(f)
            .map(|g| consumed(db, program, g.clone()).clone())
            .collect(),
        unique: unique_calls(db, program, f),
    }
}

/// The conventions of a function's code by what `consumption` says each function consumes, as
/// [`conventions`] gives them by the query, for what reads every function's at once. It reads
/// no summary, so an update that keeps the last consumption lowers no function again for it.
pub(crate) fn conventions_by(
    db: &dyn Db,
    program: Program,
    consumption: &Consumption,
    f: &Function,
) -> Conventions {
    let of = |g: &FnRef| consumed_by(db, program, consumption, g);
    Conventions {
        owned: of(&f.name),
        calls: consume::direct_callees(f).map(of).collect(),
        unique: unique_calls(db, program, f),
    }
}

/// The callees of a function's direct calls that have in-place `let` parameters, with their
/// positions (facts.in-place-promise).
fn unique_calls(db: &dyn Db, program: Program, f: &Function) -> Vec<(FnRef, Vec<usize>)> {
    let mut found: Vec<(FnRef, Vec<usize>)> = Vec::new();
    for g in consume::direct_callees(f) {
        if found.iter().any(|(h, _)| h == g) {
            continue;
        }
        let words = crate::unique::unique_words(db, program, g);
        if !words.is_empty() {
            found.push((g.clone(), words));
        }
    }
    found
}
