//! Inlining the standard library into user functions ([Values and costs](../../../../docs/design/values-and-costs.md),
//! "A cheap optimizer before Cranelift"; goal debug-speed). A call from a function of the
//! program's own files to a small function of the standard library written in Stilt, given a
//! closure that the function itself makes, is replaced by the function's body, and so is the
//! body's call of the closure, so that the optimizer's passes see through them: the element a
//! `map` or a `fold` reads and lends to the closure needs no box ([`crate::opt::boxes`]), nor
//! does the closure, the range facts prove the reads of its loop in bounds, and its list is
//! made unique once. A call given no closure that can be inlined stays a call: its body would
//! cost the build its code and gain the program little, as the benchmark suite measures.
//!
//! Nothing crosses a user function's boundary: the standard library never changes while a
//! program runs, and a function's closures are lowered with it, so each function can still be
//! patched alone (goal edit-to-running-program). A generic function is inlined only where the call
//! gives each witness a constant, as concrete code does ([`instance`]).
//!
//! The code keeps its meaning and its reports: the standard library's code panics at the location
//! its call passes it (program.panic-location), which the inlined body reads in place of its
//! location parameter, every check that can fail stays, and the body's code is marked with the
//! call's location for a debugger's line table (goal debuggable-builds).

pub(crate) mod instance;
pub(crate) mod rename;
pub(crate) mod splice;
pub(crate) mod user;

use std::sync::Arc;

use stilt_db::{Db, Program, parallel};

use crate::items::{Code, FnRef, code_of};
use crate::lower::Cx;
use crate::lower::functions::signature;
use crate::mir::{Arg, BlockId, Callee, Const, Function, Local, Operand, Rvalue, Terminator};
use crate::opt::defs::defined_once;
use crate::opt::inline::splice::{Body, splice};

/// How many times a function's calls are looked at: the calls of the standard library, then
/// the closures that their bodies call and the calls of the standard library in those, and so on.
const ROUNDS: usize = 4;

/// The most statements and blocks a function of the standard library has to be inlined.
const STD_SIZE: usize = 72;

/// The most statements and blocks a closure has to be inlined.
const CLOSURE_SIZE: usize = 48;

/// The most statements and blocks inlining adds to one function, which keeps the debug build's
/// compile time in proportion to the program (goal clean-debug-build).
const GROWTH: usize = 640;

/// The functions that make up `f`, as [`crate::functions`] gives them, with each function of the
/// program's own code inlining what it calls of the standard library and of its own closures,
/// and `None` for each closure that nothing names any more, every call of it inlined, which
/// needs no code. A function without such a call is the same `Arc`.
// Salsa takes a query's key by value.
#[allow(clippy::needless_pass_by_value)]
#[salsa::tracked(returns(ref))]
pub fn inlined(db: &dyn Db, program: Program, f: FnRef) -> Vec<Option<Arc<Function>>> {
    let own = crate::functions(db, program, f.clone());
    let inliner = Inliner { db, program, own };
    let functions: Vec<Arc<Function>> = own
        .iter()
        .map(|g| {
            inliner
                .inline(g)
                .map_or_else(|| Arc::clone(g), |g| Arc::new(g.fitted()))
        })
        .collect();
    let named = named(&functions);
    functions
        .into_iter()
        .zip(named)
        .map(|(g, named)| named.then_some(g))
        .collect()
}

/// Which of the functions that make up a user function something names: the user function
/// itself, and each closure that one of them it names names, since only they name its closures.
fn named(functions: &[Arc<Function>]) -> Vec<bool> {
    let mut named = vec![false; functions.len()];
    if functions.is_empty() {
        return named;
    }
    let mut todo = vec![0];
    named[0] = true;
    while let Some(i) = todo.pop() {
        for g in crate::walk::referenced(&functions[i]) {
            if let Some(j) = functions.iter().position(|f| f.name == g)
                && !named[j]
            {
                named[j] = true;
                todo.push(j);
            }
        }
    }
    named
}

/// The functions of `functions` to compile: each as [`inlined`] gives it if it is one of the
/// program's own as [`crate::functions`] gives it, rather than code that panics in place of a
/// body with an error, and without the closures that nothing names any more. The user
/// functions are inlined across the machine's cores first.
pub fn inline_reached<D: Db + Clone>(
    db: &D,
    program: Program,
    functions: Vec<Arc<Function>>,
) -> Vec<Arc<Function>> {
    let mut roots: Vec<FnRef> = functions
        .iter()
        .map(|g| g.name.root().clone())
        .filter(|r| is_user(db, program, r))
        .collect();
    roots.dedup();
    parallel::for_each(db, &roots, |db, r| {
        inlined(db, program, r.clone());
    });
    functions
        .into_iter()
        .filter_map(|g| {
            let root = g.name.root();
            if !is_user(db, program, root) {
                return Some(g);
            }
            let own = crate::functions(db, program, root.clone());
            match own.iter().position(|o| Arc::ptr_eq(o, &g)) {
                Some(i) => inlined(db, program, root.clone())[i].clone(),
                None => Some(g),
            }
        })
        .collect()
}

/// Whether the code of `f` is in one of the program's own files.
pub(crate) fn is_user(db: &dyn Db, program: Program, f: &FnRef) -> bool {
    in_std(db, program, f) == Some(false)
}

/// Whether the code of `f` is in a file of the standard library, if it is in a file.
fn in_std(db: &dyn Db, program: Program, f: &FnRef) -> Option<bool> {
    match code_of(db, program, f.clone())? {
        Code::Body(file, _) => Some(stilt_hir::module_hir(db, program, file).std),
        Code::Native => None,
    }
}

/// The statements and blocks of a function, which measure the code it compiles to.
pub(crate) fn size(f: &Function) -> usize {
    let counted = |s: &&crate::mir::Stmt| !matches!(s, crate::mir::Stmt::Count(..));
    f.blocks
        .iter()
        .map(|b| b.stmts.iter().filter(counted).count() + 1)
        .sum()
}

/// What inlining into the functions of one user function reads.
struct Inliner<'a> {
    db: &'a dyn Db,
    program: Program,
    /// The functions that make up the user function, its closures among them.
    own: &'a [Arc<Function>],
}

/// A call to inline: the function and its parameters' operands.
struct Target {
    function: Arc<Function>,
    args: Vec<Operand>,
    std: bool,
}

impl Inliner<'_> {
    /// `g` with its calls inlined, or `None` if it inlines none.
    fn inline(&self, g: &Function) -> Option<Function> {
        if g.broken || !is_user(self.db, self.program, g.name.root()) {
            return None;
        }
        let mut f = g.clone();
        let mut room = GROWTH;
        let mut any = false;
        for _ in 0..ROUNDS {
            let mut changed = false;
            let known = closures(&f);
            for b in 0..f.blocks.len() {
                let at = BlockId(u32::try_from(b).expect("under 4G blocks"));
                let Some(target) = self.target(&f, at, &known) else {
                    continue;
                };
                let grows = size(&target.function);
                if grows > room {
                    continue;
                }
                let body = Body {
                    function: &target.function,
                    args: target.args,
                    std: target.std,
                };
                if splice(&mut f, at, &body) {
                    room -= grows;
                    changed = true;
                }
            }
            any |= changed;
            if !changed {
                break;
            }
        }
        any.then(|| {
            crate::prune::keep_reachable(&mut f);
            crate::opt::boxes::unbox(&mut f);
            crate::opt::copies::propagate(&mut f);
            f
        })
    }

    /// The function that the call ending block `at` of `f` calls, if it is to be inlined.
    fn target(&self, f: &Function, at: BlockId, known: &[Option<FnRef>]) -> Option<Target> {
        let Terminator::Call { callee, args, .. } = &f.blocks[at.0 as usize].term else {
            return None;
        };
        // A value lent in a box goes only to a native or a dictionary's method, neither inlined.
        let operands: Vec<Operand> = args
            .iter()
            .map(|a| match a {
                Arg::Borrow(o) | Arg::Own(o) | Arg::Ref(o) => Some(o.clone()),
                Arg::Lend(_) => None,
            })
            .collect::<Option<_>>()?;
        match callee {
            // A call of the standard library pays for its code where its closure's call is
            // inlined too, and what the closure reads and returns needs no object.
            Callee::Direct(g) if operands.iter().any(|o| self.lends_closure(f, o, known)) => {
                self.std_target(g, operands)
            }
            Callee::Value(closure) => {
                let c = match closure {
                    Operand::Local(l) => known.get(l.0 as usize)?.clone()?,
                    Operand::Const(c) => code_of_closure(c)?,
                };
                let function = self.closure(&c, &f.name)?;
                let (loc, rest) = operands.split_first()?;
                let mut args = vec![loc.clone(), closure.clone()];
                args.extend_from_slice(rest);
                let std = self.own.iter().all(|o| o.name != c);
                Some(Target {
                    function,
                    args,
                    std,
                })
            }
            Callee::Direct(_) | Callee::Method(..) => None,
        }
    }

    /// The function of the standard library that a direct call calls, instantiated for the
    /// call's constant witnesses, if it is small, not recursive, and every witness is constant.
    fn std_target(&self, g: &FnRef, args: Vec<Operand>) -> Option<Target> {
        if in_std(self.db, self.program, g) != Some(true) {
            return None;
        }
        let lowered = crate::functions(self.db, self.program, g.clone());
        let callee = lowered.iter().find(|h| h.name == *g)?;
        let recursive = callee.blocks.iter().any(
            |b| matches!(&b.term, Terminator::Call { callee: Callee::Direct(h), .. } if h == g),
        );
        if callee.broken || recursive || size(callee) > STD_SIZE {
            return None;
        }
        let cx = Cx {
            db: self.db,
            program: self.program,
        };
        let shapes: Vec<(Local, u64)> = witnesses(&cx, g)?
            .into_iter()
            .map(|i| match args.get(i)? {
                Operand::Const(Const::Word(s)) => Some((callee.params.get(i)?.local, *s)),
                _ => None,
            })
            .collect::<Option<_>>()?;
        let mut function = (**callee).clone();
        instance::instantiate(&mut function, &shapes);
        Some(Target {
            function: Arc::new(function),
            args,
            std: true,
        })
    }

    /// Whether `o` is a closure of `f` that can be inlined.
    fn lends_closure(&self, f: &Function, o: &Operand, known: &[Option<FnRef>]) -> bool {
        let c = match o {
            Operand::Local(l) => known.get(l.0 as usize).cloned().flatten(),
            Operand::Const(c) => code_of_closure(c),
        };
        c.is_some_and(|c| self.closure(&c, &f.name).is_some())
    }

    /// The function of the closure `c`, if it is small and the user function's own or the
    /// standard library's, and not `caller` itself.
    fn closure(&self, c: &FnRef, caller: &FnRef) -> Option<Arc<Function>> {
        let root = c.root();
        let functions = if self.own.first().is_some_and(|o| o.name == *root) {
            self.own
        } else if in_std(self.db, self.program, root) == Some(true) {
            crate::functions(self.db, self.program, root.clone()).as_slice()
        } else {
            return None;
        };
        let function = functions.iter().find(|g| g.name == *c)?;
        (c != caller && !function.broken && size(function) <= CLOSURE_SIZE)
            .then(|| Arc::clone(function))
    }
}

/// The parameters, by position, of the witnesses of `g`'s type parameters, as lowering lays
/// them out after the location: those of `Self` in a trait's default method, then each type
/// parameter's, each followed by its bounds' dictionaries.
pub(crate) fn witnesses(cx: &Cx<'_>, g: &FnRef) -> Option<Vec<usize>> {
    let sig = signature(&cx.decls(), g)?;
    let mut at = 1;
    let mut out = Vec::new();
    if let FnRef::DefaultMethod(..) = g {
        out.push(at);
        at += 2;
    }
    for (_, bounds) in &sig.type_params {
        out.push(at);
        at += 1 + bounds.len();
    }
    Some(out)
}

/// The closure that each local of `f` holds, if `f` makes it: a local defined once by the
/// allocation of a closure object, whose first field is its code, or by a copy of one.
fn closures(f: &Function) -> Vec<Option<FnRef>> {
    let defs = defined_once(f);
    let mut known: Vec<Option<FnRef>> = defs
        .iter()
        .map(|r| match r {
            Some(Rvalue::Alloc(_, fields)) => match fields.first() {
                Some((Operand::Const(Const::Code(c @ FnRef::Closure(..))), _)) => Some(c.clone()),
                _ => None,
            },
            _ => None,
        })
        .collect();
    let mut changed = true;
    while changed {
        changed = false;
        for (l, r) in defs.iter().enumerate() {
            if let Some(Rvalue::Use(Operand::Local(s))) = r
                && known[l].is_none()
                && let Some(c) = known[s.0 as usize].clone()
            {
                known[l] = Some(c);
                changed = true;
            }
        }
    }
    known
}

/// The closure that a constant closure object holds, which captures nothing.
fn code_of_closure(c: &Const) -> Option<FnRef> {
    match c {
        Const::Data(_, fields) => match fields.first() {
            Some((Const::Code(c @ FnRef::Closure(..)), _)) => Some(c.clone()),
            _ => None,
        },
        _ => None,
    }
}
