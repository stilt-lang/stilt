//! What a program's roots reach, through calls, the code of closures and dictionaries, and the
//! values of constants: the roots, then the functions they name that no step before reached, and so
//! on, a step at a time.
//!
//! A [`Walk`] keeps what it reached, so that walking the program again after an edit does only what
//! the edit calls for (goal edit-to-running-program). Each function it reached is proved unchanged
//! by the query that lowered it, across the machine's cores, and the steps are taken again only
//! when the roots, or the functions that a changed function names, differ, since only then can what
//! is reached differ; the walk then gives only the functions whose lowering ran again, and those it
//! reached for the first time. A function's closures are lowered with it and named only by its
//! code, so a walk never visits them on their own.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use stilt_db::{Db, Program, parallel};

use crate::check_errors::CheckErrors;
use crate::functions;
use crate::items::{Code, FnRef, bodies};
use crate::mir::{Arg, Callee, Const, Function, Operand, Rvalue, Stmt, Terminator};

/// The functions of a program that its entry reaches, the entry first, and the natives they
/// call.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Reached {
    /// Shared with the query that lowered them, so that a function an edit doesn't change is
    /// the same `Arc` after it.
    pub functions: Vec<Arc<Function>>,
    /// The natives reached.
    pub natives: BTreeSet<FnRef>,
    /// The constants reached, whose values are computed where first used.
    pub constants: BTreeSet<FnRef>,
}

/// Every function and native that the program's entry reaches. In a program with errors, `errors`
/// are its code with an error, which panics in place of running (program.programs-with-errors).
#[must_use]
pub fn reached<D: Db + Clone>(db: &D, program: Program, errors: &CheckErrors) -> Reached {
    reached_from(db, program, &[FnRef::Main], errors)
}

/// Every function and native that `roots` reach, as [`reached`] finds them. Each step's functions
/// are lowered across the machine's cores first, so that a build lowers what it reaches in parallel
/// (goals edit-to-running-program and clean-debug-build).
#[must_use]
pub fn reached_from<D: Db + Clone>(
    db: &D,
    program: Program,
    roots: &[FnRef],
    errors: &CheckErrors,
) -> Reached {
    let found = find(db, program, roots, errors, &HashMap::new());
    Reached {
        functions: found.nodes.into_iter().flat_map(|n| n.functions).collect(),
        natives: found.natives,
        constants: found.constants,
    }
}

/// A function that a walk reached: the functions that make it up, as the query that lowered
/// them gave them, and the functions they name.
#[derive(Clone, Debug)]
struct Node {
    f: FnRef,
    functions: Vec<Arc<Function>>,
    named: Arc<[FnRef]>,
}

/// What a walk reached, its functions in the order it reached them.
#[derive(Clone, Debug, Default)]
struct Found {
    nodes: Vec<Node>,
    natives: BTreeSet<FnRef>,
    constants: BTreeSet<FnRef>,
}

/// What a program's roots reached when it was last walked, kept so that the next walk does only
/// what an edit calls for.
#[derive(Debug, Default)]
pub struct Walk {
    /// The roots of the last walk, or `None` before the first and after a walk of a program
    /// with errors, whose code with an error panics in place of what lowering gives, so that the
    /// next walk starts afresh.
    roots: Option<Vec<FnRef>>,
    found: Found,
}

/// A walk made but not yet kept: what the roots reach now, and the functions that may differ
/// from those the walk reached before. The walk is kept by [`Walk::keep`], once what reads the
/// database after it is done too, so that an edit that cancels a reader never leaves a walk
/// kept whose functions were never given.
#[derive(Debug)]
pub struct Walked {
    roots: Option<Vec<FnRef>>,
    now: Now,
    renewed: Vec<Arc<Function>>,
}

/// A function reached again whose lowering ran again: the functions that make it up at the
/// last walk, and now.
#[derive(Debug)]
pub struct Renewed<'a> {
    /// The function.
    pub f: &'a FnRef,
    /// The functions that made it up at the last walk.
    pub before: &'a [Arc<Function>],
    /// The functions that make it up after this one.
    pub now: &'a [Arc<Function>],
}

/// What the roots reach now.
#[derive(Debug)]
enum Now {
    /// The same functions as before, of which those at these places have functions lowered
    /// again, and name what they named.
    Same(Vec<(usize, Vec<Arc<Function>>)>),
    /// Other functions.
    Moved(Found),
}

/// A function reached before whose lowering ran again: its functions now, and when they differ
/// from those of the last walk, what they name.
struct Renewal {
    functions: Vec<Arc<Function>>,
    named: Option<Arc<[FnRef]>>,
}

impl Walk {
    /// Walks the program from `roots`, as [`reached_from`] does, and tells the functions that
    /// may differ from those of the last walk: every function reached on the first walk, after
    /// a walk of a program with errors, and with errors; and otherwise the functions whose
    /// lowering ran again since the last walk, the ones whose code changed among them, and
    /// those reached for the first time, in the order reached. A function reached before that
    /// is reached again with the same code isn't among them, so that what reads the result
    /// does as much as the edit changed.
    #[must_use]
    pub fn walk<D: Db + Clone>(
        &self,
        db: &D,
        program: Program,
        roots: Vec<FnRef>,
        errors: &CheckErrors,
    ) -> Walked {
        let last = self.roots.as_ref().filter(|_| errors.is_empty());
        let Some(last) = last else {
            let found = find(db, program, &roots, errors, &HashMap::new());
            let renewed = found
                .nodes
                .iter()
                .flat_map(|n| n.functions.clone())
                .collect();
            let roots = errors.is_empty().then_some(roots);
            let now = Now::Moved(found);
            return Walked {
                roots,
                now,
                renewed,
            };
        };
        let renewals = renewals(db, program, &self.found.nodes);
        let moved = *last != roots
            || renewals.iter().zip(&self.found.nodes).any(|(r, node)| {
                r.as_ref()
                    .and_then(|r| r.named.as_ref())
                    .is_some_and(|named| !same_names(named, &node.named))
            });
        if moved {
            return self.moved(db, program, roots, renewals);
        }
        let mut renewed = Vec::new();
        let mut edits = Vec::new();
        for (at, renewal) in renewals.into_iter().enumerate() {
            if let Some(r) = renewal {
                renewed.extend(r.functions.iter().cloned());
                edits.push((at, r.functions));
            }
        }
        Walked {
            roots: Some(roots),
            now: Now::Same(edits),
            renewed,
        }
    }

    /// The walk from `roots` once what is reached may have moved: the steps taken again, each
    /// function reached before taken as `renewals` found it.
    fn moved<D: Db + Clone>(
        &self,
        db: &D,
        program: Program,
        roots: Vec<FnRef>,
        renewals: Vec<Option<Renewal>>,
    ) -> Walked {
        let mut renewed_at = HashSet::new();
        let nodes: Vec<Node> = self
            .found
            .nodes
            .iter()
            .zip(renewals)
            .map(|(node, renewal)| match renewal {
                None => node.clone(),
                Some(r) => {
                    renewed_at.insert(node.f.clone());
                    let named = r.named.unwrap_or_else(|| Arc::clone(&node.named));
                    let (f, functions) = (node.f.clone(), r.functions);
                    Node {
                        f,
                        functions,
                        named,
                    }
                }
            })
            .collect();
        let known: HashMap<&FnRef, &Node> = nodes.iter().map(|n| (&n.f, n)).collect();
        let found = find(db, program, &roots, &CheckErrors::default(), &known);
        let renewed = found
            .nodes
            .iter()
            .filter(|n| !known.contains_key(&n.f) || renewed_at.contains(&n.f))
            .flat_map(|n| n.functions.iter().cloned())
            .collect();
        Walked {
            roots: Some(roots),
            now: Now::Moved(found),
            renewed,
        }
    }

    /// Keeps `walked` as the last walk.
    pub fn keep(&mut self, walked: Walked) {
        match walked.now {
            Now::Same(edits) => {
                for (at, functions) in edits {
                    self.found.nodes[at].functions = functions;
                }
            }
            Now::Moved(found) => self.found = found,
        }
        self.roots = walked.roots;
    }
}

impl Walked {
    /// The functions whose lowering ran again since the last walk, the ones whose code
    /// changed among them, and those reached for the first time, in the order reached: every
    /// function reached, when the walk started afresh.
    #[must_use]
    pub fn renewed(&self) -> &[Arc<Function>] {
        &self.renewed
    }

    /// When the walk reached the same functions as `last`, the walk it followed, each function
    /// whose lowering ran again, with its functions then and now; and otherwise `None`.
    #[must_use]
    pub fn renewals<'a>(&'a self, last: &'a Walk) -> Option<Vec<Renewed<'a>>> {
        let Now::Same(edits) = &self.now else {
            return None;
        };
        let renewed = edits.iter().map(|(at, now)| {
            let node = &last.found.nodes[*at];
            Renewed {
                f: &node.f,
                before: &node.functions,
                now,
            }
        });
        Some(renewed.collect())
    }

    /// Every function reached, in the order reached, `last` being the walk this one followed.
    #[must_use]
    pub fn functions(&self, last: &Walk) -> Vec<Arc<Function>> {
        match &self.now {
            Now::Moved(found) => found
                .nodes
                .iter()
                .flat_map(|n| n.functions.iter().cloned())
                .collect(),
            Now::Same(edits) => {
                let edited: HashMap<usize, &Vec<Arc<Function>>> =
                    edits.iter().map(|(at, f)| (*at, f)).collect();
                let nodes = last.found.nodes.iter().enumerate();
                nodes
                    .flat_map(|(at, n)| edited.get(&at).copied().unwrap_or(&n.functions))
                    .cloned()
                    .collect()
            }
        }
    }
}

/// For each node, `None` when the query that lowers it gives the same functions, and otherwise
/// what it gives, read across the machine's cores.
fn renewals<D: Db + Clone>(db: &D, program: Program, nodes: &[Node]) -> Vec<Option<Renewal>> {
    parallel::map_with(db, nodes, |db, node| {
        let now = functions(db, program, node.f.clone());
        let same = |eq: fn(&Arc<Function>, &Arc<Function>) -> bool| {
            now.len() == node.functions.len()
                && now.iter().zip(&node.functions).all(|(a, b)| eq(a, b))
        };
        if same(Arc::ptr_eq) {
            return None;
        }
        let named = (!same(|a, b| **a == **b)).then(|| references(db, program, node.f.clone()));
        Some(Renewal {
            functions: now.clone(),
            named,
        })
    })
}

/// Whether two lists of names are the same, which they are at no cost when they are the same
/// `Arc`, as they are when the query that finds them didn't run again.
fn same_names(a: &Arc<[FnRef]>, b: &Arc<[FnRef]>) -> bool {
    Arc::ptr_eq(a, b) || **a == **b
}

/// What `roots` reach, a step at a time. Each function in `known` is taken as it is there, and
/// every other is lowered, the step's unknown functions across the machine's cores first.
fn find<D: Db + Clone>(
    db: &D,
    program: Program,
    roots: &[FnRef],
    errors: &CheckErrors,
    known: &HashMap<&FnRef, &Node>,
) -> Found {
    let code = &bodies(db, program).code;
    let mut found = Found::default();
    let mut seen = HashSet::new();
    let mut step: Vec<FnRef> = roots
        .iter()
        .filter(|f| seen.insert((*f).clone()))
        .cloned()
        .collect();
    while !step.is_empty() {
        step.retain(|f| {
            let native = matches!(code.get(f), Some(Code::Native));
            if native {
                found.natives.insert(f.clone());
            }
            // A foreign function's code is C's (c.calls).
            !native && !matches!(f, FnRef::Closure(..) | FnRef::Foreign(..))
        });
        if errors.is_empty() {
            let unknown: Vec<&FnRef> = step.iter().filter(|f| !known.contains_key(f)).collect();
            parallel::for_each(db, &unknown, |db, f| {
                references(db, program, (*f).clone());
            });
        }
        let mut next = Vec::new();
        for f in step {
            let node = match known.get(&f) {
                Some(node) => (*node).clone(),
                None => visit(db, program, f, errors),
            };
            if matches!(node.f, FnRef::Const(_) | FnRef::MemberConst(..)) {
                found.constants.insert(node.f.clone());
            }
            for g in node.named.iter() {
                if seen.insert(g.clone()) {
                    next.push(g.clone());
                }
            }
            found.nodes.push(node);
        }
        step = next;
    }
    found
}

/// The node of `f`: its functions, or with errors, those that panic in place of its code with
/// an error, and what they name.
fn visit(db: &dyn Db, program: Program, f: FnRef, errors: &CheckErrors) -> Node {
    if errors.is_empty() {
        let functions = functions(db, program, f.clone()).clone();
        let named = references(db, program, f.clone());
        return Node {
            f,
            functions,
            named,
        };
    }
    let functions = errors.functions(db, program, &f);
    let named = named_by(&functions);
    Node {
        f,
        functions,
        named,
    }
}

/// The functions that the functions of `f` name, each once, in the order they are first named, kept
/// so that walking a program after an edit reads again only the functions the edit changed (goal
/// edit-to-running-program).
// Salsa takes a query's key by value.
#[allow(clippy::needless_pass_by_value)]
#[salsa::tracked(returns(clone))]
fn references(db: &dyn Db, program: Program, f: FnRef) -> Arc<[FnRef]> {
    named_by(functions(db, program, f))
}

/// The functions that `functions` name, each once, in the order they are first named, but
/// their closures, which come with them.
fn named_by(functions: &[Arc<Function>]) -> Arc<[FnRef]> {
    let mut seen = HashSet::new();
    functions
        .iter()
        .flat_map(|g| referenced(g))
        .filter(|g| !matches!(g, FnRef::Closure(..)) && seen.insert(g.clone()))
        .collect()
}

/// The functions a function names: those it calls, and the code it puts in data.
pub fn referenced(f: &Function) -> Vec<FnRef> {
    let mut out = Vec::new();
    let mut operands: Vec<&Operand> = Vec::new();
    for block in &f.blocks {
        for stmt in &block.stmts {
            match stmt {
                Stmt::Assign(_, rvalue) => {
                    if let Rvalue::Constant(g, ..) = rvalue {
                        out.push(g.clone());
                    }
                    operands.extend(rvalue.operands());
                }
                Stmt::Store { value, .. } => operands.push(value),
                Stmt::Effect(_, args) => operands.extend(args),
                Stmt::ReleaseConstants
                | Stmt::Dup(_)
                | Stmt::Drop(_)
                | Stmt::At(_)
                | Stmt::Count(..) => {}
            }
        }
        match &block.term {
            Terminator::Call { callee, args, .. } => {
                match callee {
                    Callee::Direct(g) => out.push(g.clone()),
                    Callee::Value(o) | Callee::Method(o, _) => operands.push(o),
                }
                operands.extend(args.iter().flat_map(Arg::operands));
            }
            Terminator::Return(os) | Terminator::Raise(os) => operands.extend(os),
            _ => {}
        }
    }
    for o in operands {
        if let Operand::Const(c) = o {
            constant(c, &mut out);
        }
    }
    out
}

fn constant(c: &Const, out: &mut Vec<FnRef>) {
    match c {
        Const::Code(f) => out.push(f.clone()),
        Const::Data(_, fields) => {
            for (c, _) in fields {
                constant(c, out);
            }
        }
        Const::Word(_) | Const::Str(_) => {}
    }
}

#[cfg(test)]
mod tests;
