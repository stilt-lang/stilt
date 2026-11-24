//! Reference counting kept from one version of a program to the next, so that an edit counts only
//! the functions whose MIR, or whose calling conventions, it changed.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use stilt_db::{Db, Program, parallel};
use stilt_mir::FnRef;
use stilt_mir::mir::Function;

use crate::consume::Conventions;
use crate::counted;
use crate::queries::{Consumption, consumption_of, conventions_by};

/// A function's MIR as lowering gave it, the conventions it was counted with, and its MIR with
/// those conventions and its reference counting.
#[derive(Debug)]
struct Entry {
    before: Arc<Function>,
    conventions: Conventions,
    after: Arc<Function>,
}

/// Each function's MIR, before and after its conventions and reference counting were inserted,
/// and for a build, what each function it counted names.
#[derive(Debug, Default)]
pub struct Counted {
    functions: HashMap<FnRef, Entry>,
    named: stilt_mir::Named,
}

impl Counted {
    /// The functions of `program`, each of the program's own inlining what it calls of the
    /// standard library and of its closures (`stilt_mir::inlined`), with the conventions that
    /// consumption calls for and their reference counting, inserted again only in those whose
    /// MIR differs from the last that was counted, or whose conventions do: an edit that
    /// changes what a function consumes changes the code of every function that calls it
    /// directly. A function that didn't change is the same `Arc` as before, which tells it
    /// apart at no cost. The functions to count are counted across the machine's cores, each on
    /// its own.
    pub fn insert<D: Db + Clone>(
        &mut self,
        db: &D,
        program: Program,
        functions: Vec<Arc<Function>>,
    ) -> Vec<Arc<Function>> {
        let functions = stilt_mir::inline_reached(db, program, functions);
        self.insert_consumed(db, program, functions)
    }

    /// As [`Counted::insert`], for a build: the functions also inline the small functions of the
    /// program's own files that they call (`stilt_mir::inline_calls`), which a running program
    /// doesn't, since it keeps one function per slot (goal edit-to-running-program). A build keeps
    /// the counting of the functions it gives alone, so that the counting kept for the next build
    /// is that of the functions the last one reached (goal bounded-cache).
    pub fn insert_built<D: Db + Clone>(
        &mut self,
        db: &D,
        program: Program,
        functions: Vec<Arc<Function>>,
    ) -> Vec<Arc<Function>> {
        let functions = stilt_mir::inline_reached(db, program, functions);
        let functions = stilt_mir::inline_calls(db, program, functions, &mut self.named);
        let built = self.insert_consumed(db, program, functions);
        let reached: HashSet<&FnRef> = built.iter().map(|f| &f.name).collect();
        self.functions.retain(|f, _| reached.contains(f));
        built
    }

    /// The functions with the conventions that what they and their direct callees consume
    /// calls for, summarized across the machine's cores, and their reference counting.
    fn insert_consumed<D: Db + Clone>(
        &mut self,
        db: &D,
        program: Program,
        functions: Vec<Arc<Function>>,
    ) -> Vec<Arc<Function>> {
        let consumption = consumption_of(db, program, &functions, &Consumption::new());
        self.insert_by(functions, |f| conventions_by(db, program, &consumption, f))
    }

    /// The functions with the conventions that `conventions` gives each and their reference
    /// counting, as [`Counted::insert`] gives them.
    pub(crate) fn insert_by(
        &mut self,
        functions: Vec<Arc<Function>>,
        conventions: impl Fn(&Function) -> Conventions,
    ) -> Vec<Arc<Function>> {
        let mut out = Vec::with_capacity(functions.len());
        let mut todo = Vec::new();
        for f in functions {
            let conventions = conventions(&f);
            match self.functions.get_mut(&f.name) {
                Some(e)
                    if (Arc::ptr_eq(&e.before, &f) || *e.before == *f)
                        && e.conventions == conventions =>
                {
                    // The query's own, so that an equal one lowered before is freed.
                    e.before = f;
                    out.push(Arc::clone(&e.after));
                }
                _ => {
                    // In its place until it is counted.
                    out.push(Arc::clone(&f));
                    todo.push((out.len() - 1, f, conventions));
                }
            }
        }
        // The largest first, so that the last to finish is a small one.
        todo.sort_by_key(|(_, f, _)| {
            std::cmp::Reverse(f.blocks.iter().map(|b| b.stmts.len() + 1).sum::<usize>())
        });
        let done = parallel::map_costly(todo, |(at, before, conventions)| {
            let (mut after, _) = counted(&before, &conventions);
            stilt_mir::opt::optimize_counted(&mut after);
            (at, before, conventions, Arc::new(after.fitted()))
        });
        for (at, before, conventions, after) in done {
            out[at] = Arc::clone(&after);
            let entry = Entry {
                before,
                conventions,
                after,
            };
            self.functions.insert(entry.before.name.clone(), entry);
        }
        out
    }
}
