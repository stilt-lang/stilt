//! Inlining small user functions into the functions that call them, in a build only
//! (goal debug-speed). A running program keeps one function per slot, so that an edit patches one
//! function alone (goal edit-to-running-program), and a built program has no edits to patch: the
//! two differ in speed alone, never in meaning.
//!
//! A direct call to a function of the program's own files that is small, not recursive and
//! doesn't name a closure is replaced by the function's body, as [`super::splice`] does for the
//! standard library's, so that the range facts see its arguments and a scalar function such as
//! `a(i, j)` of a hot loop costs no call. It comes before the conventions of consumption are
//! applied and before reference counting, so counting sees the inlined code, while what a
//! function consumes still follows its own body, which is still compiled for the calls that
//! stay.
//!
//! The body keeps its own locations, so a panic in it reports the line it panics at
//! (program.panic-location; numbers.integer-panics), and a debugger's line table maps its code to
//! its own lines (goal debuggable-builds).

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use rustc_hash::FxHashMap;
use stilt_db::{Db, Program, parallel};

use crate::items::FnRef;
use crate::lower::Cx;
use crate::mir::{Arg, BlockId, Callee, Function, Operand, ParamMode, Repr, Terminator};
use crate::opt::inline::splice::{Body, splice};
use crate::opt::inline::{is_user, size, witnesses};

/// How many levels of calls are looked at: a function inlined into a caller may already have
/// inlined its own calls.
const LEVELS: usize = 2;

/// The most statements and blocks a function has to be inlined. Chosen by measuring `just bench`: spectral-norm's `a(i, j)` has 16 to 20, and a limit of 20,
/// 40 or 80 gains the others nothing, so the least round figure above it is kept.
const SIZE: usize = 24;

/// The most statements and blocks inlining adds to one function, which keeps the build's
/// compile time in proportion to the program (goal clean-debug-build).
const GROWTH: usize = 400;

/// What each function of the last build names, as [`crate::walk::referenced`] finds it, by the
/// function it was found in, which it keeps, so that its address names it: a build finds again only
/// what the functions an edit changed name (goal compile-time-code-rebuilds). It holds the
/// functions of the last build alone (goal bounded-cache).
#[derive(Debug, Default)]
pub struct Named {
    by_address: FxHashMap<usize, (Arc<Function>, Arc<[FnRef]>)>,
}

/// The functions of `functions` with each user function's calls of small user functions
/// inlined, and without the functions that nothing reaches any more from the program's entry,
/// whose every call was inlined. The functions are inlined across the machine's cores, and what
/// each names is taken from `named` when the last build found it, which then holds what these
/// functions name.
pub fn inline_calls<D: Db + Clone>(
    db: &D,
    program: Program,
    functions: Vec<Arc<Function>>,
    named: &mut Named,
) -> Vec<Arc<Function>> {
    let mut functions = functions;
    for _ in 0..LEVELS {
        let small = small(db, program, &functions);
        if small.is_empty() {
            break;
        }
        let users: Vec<bool> = functions
            .iter()
            .map(|f| !f.broken && is_user(db, program, f.name.root()))
            .collect();
        let todo: Vec<(Arc<Function>, bool)> = functions.into_iter().zip(users).collect();
        functions = parallel::map(todo, |(f, user)| {
            if user {
                into(&f, &small).map_or(f, Arc::new)
            } else {
                f
            }
        });
    }
    reachable(functions, named)
}

/// The functions that a call may inline, by name: small functions of the program's own files
/// whose parameters are all passed by value and whose type has no type parameters, that don't
/// call themselves and name no closure.
fn small<D: Db + Clone>(
    db: &D,
    program: Program,
    functions: &[Arc<Function>],
) -> HashMap<FnRef, Arc<Function>> {
    let cx = Cx { db, program };
    functions
        .iter()
        .filter(|f| {
            matches!(
                f.name,
                FnRef::Function(_) | FnRef::Member(..) | FnRef::ImplMethod(..)
            ) && !f.broken
                && size(f) <= SIZE
                && f.params.iter().all(|p| p.mode != ParamMode::Ref)
                && f.locals.iter().all(|d| !matches!(d.repr, Repr::Generic(_)))
                && is_user(db, program, &f.name)
                && witnesses(&cx, &f.name).is_some_and(|w| w.is_empty())
                && leaf(f)
        })
        .map(|f| (f.name.clone(), Arc::clone(f)))
        .collect()
}

/// Whether `f` doesn't call itself, and makes and names no closure.
fn leaf(f: &Function) -> bool {
    crate::walk::referenced(f)
        .iter()
        .all(|g| *g != f.name && !matches!(g, FnRef::Closure(..)))
}

/// `f` with the calls of the functions in `small` inlined, or `None` if it inlines none. A
/// function that calls none of them isn't copied, since a build looks at every function it
/// reaches again (goal compile-time-code-rebuilds).
fn into(f: &Function, small: &HashMap<FnRef, Arc<Function>>) -> Option<Function> {
    let calls_small = f.blocks.iter().any(|b| match &b.term {
        Terminator::Call {
            callee: Callee::Direct(g),
            ..
        } => small.get(g).is_some_and(|c| c.name != f.name),
        _ => false,
    });
    if !calls_small {
        return None;
    }
    let mut f = f.clone();
    let mut room = GROWTH;
    let mut any = false;
    for b in 0..f.blocks.len() {
        let at = BlockId(u32::try_from(b).expect("under 4G blocks"));
        let Terminator::Call {
            callee: Callee::Direct(g),
            args,
            ..
        } = &f.blocks[b].term
        else {
            continue;
        };
        let Some(callee) = small.get(g).filter(|c| c.name != f.name) else {
            continue;
        };
        let grows = size(callee);
        if grows > room || args.len() != callee.params.len() {
            continue;
        }
        // A value lent in a box goes only to a native or a dictionary's method, neither inlined.
        let Some(args) = args
            .iter()
            .map(|a| match a {
                Arg::Borrow(o) | Arg::Own(o) | Arg::Ref(o) => Some(o.clone()),
                Arg::Lend(_) => None,
            })
            .collect::<Option<Vec<Operand>>>()
        else {
            continue;
        };
        let body = Body {
            function: callee,
            args,
            std: false,
        };
        if splice(&mut f, at, &body) {
            room -= grows;
            any = true;
        }
    }
    any.then(|| {
        crate::prune::keep_reachable(&mut f);
        crate::opt::boxes::unbox(&mut f);
        crate::opt::copies::propagate(&mut f);
        f
    })
}

/// The functions that the program's entry reaches, in their order. What each function names
/// that `kept` doesn't hold is found across the machine's cores, and `kept` then holds what
/// each of `functions` names.
fn reachable(functions: Vec<Arc<Function>>, kept: &mut Named) -> Vec<Arc<Function>> {
    let by_name: HashMap<&FnRef, usize> = functions
        .iter()
        .enumerate()
        .map(|(i, f)| (&f.name, i))
        .collect();
    let named = names(&functions, kept);
    let mut seen: HashSet<usize> = HashSet::new();
    let mut todo: Vec<usize> = by_name.get(&FnRef::Main).copied().into_iter().collect();
    while let Some(i) = todo.pop() {
        if seen.insert(i) {
            todo.extend(named[i].iter().filter_map(|g| by_name.get(g).copied()));
        }
    }
    if seen.is_empty() {
        return functions;
    }
    functions
        .iter()
        .enumerate()
        .filter(|(i, _)| seen.contains(i))
        .map(|(_, f)| Arc::clone(f))
        .collect()
}

/// What each of `functions` names, from `kept` where the last build found it in the same
/// function, and otherwise found across the machine's cores; `kept` then holds these.
fn names(functions: &[Arc<Function>], kept: &mut Named) -> Vec<Arc<[FnRef]>> {
    let address = |f: &Arc<Function>| Arc::as_ptr(f) as usize;
    let mut last = std::mem::take(&mut kept.by_address);
    let mut named: Vec<Option<Arc<[FnRef]>>> = (functions.iter())
        .map(|f| last.remove(&address(f)).map(|(_, names)| names))
        .collect();
    let missing: Vec<usize> = (0..functions.len())
        .filter(|&i| named[i].is_none())
        .collect();
    let found = parallel::map(missing.clone(), |i| {
        Arc::<[FnRef]>::from(crate::walk::referenced(&functions[i]))
    });
    for (i, names) in missing.into_iter().zip(found) {
        named[i] = Some(names);
    }
    let named: Vec<Arc<[FnRef]>> = named.into_iter().flatten().collect();
    kept.by_address = (functions.iter().zip(&named))
        .map(|(f, n)| (address(f), (Arc::clone(f), Arc::clone(n))))
        .collect();
    named
}
