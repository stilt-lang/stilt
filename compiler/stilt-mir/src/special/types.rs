//! The instantiations of each function that a build's roots reach, as lists of type and value
//! arguments (builds.specialization), which the release build's performance report names
//! (builds.performance-report): from the roots, each call of a function with a body at type
//! arguments that the caller's own arguments make concrete, each trait method called on a concrete
//! type, its impl's, or for a structural impl, as a list's `==` is, the impls of the types it
//! holds, and each operator and interpolation, which call `Eq`, `Ord`, `Hash` and `Show`. A
//! function of a group that keeps its dictionaries ([`super::groups`]) is reached at the arguments
//! it is called with from outside, and its own calls at types built from its parameters reach
//! nothing, as its code calls them through dictionaries.

use std::collections::{HashMap, HashSet, VecDeque};

use stilt_db::{Db, Program};
use stilt_hir::decls::{Lookup, TypeDefInfo, prelude_item};
use stilt_hir::hir::{BinaryOp, Item, Name};
use stilt_types::tast::{Callee, Code, Definition, Expr, ExprKind, Segment, walk};
use stilt_types::ty::{Subst, Table, Ty, instantiate};

use crate::FnRef;
use crate::items::{Code as Where, code_of};
use crate::lower::Cx;
use crate::lower::functions::{calls_own, signature};

/// The most instantiations the walk makes, and the most parts of a type argument it follows,
/// past which a type that grows through a structure is reached no further.
const MOST: usize = 50_000;
const LARGEST: usize = 64;

/// Each function with a body that `roots` reach, a build's roots, an executable's entry running
/// `main`, with each list of type arguments it is reached at, in the order reached. `kept` says
/// which functions keep their dictionaries.
#[must_use]
pub fn instantiations(
    db: &dyn Db,
    program: Program,
    roots: &[FnRef],
    kept: &dyn Fn(&FnRef) -> bool,
) -> HashMap<FnRef, Vec<Vec<Ty>>> {
    let cx = Cx { db, program };
    let mut w = Walk {
        cx: &cx,
        kept,
        seen: HashSet::new(),
        structural: HashSet::new(),
        queue: VecDeque::new(),
        of: HashMap::new(),
    };
    for root in roots {
        let root = match root {
            FnRef::Main => FnRef::Function(Item {
                home: Name::from("main"),
                name: Name::from("main"),
            }),
            f => f.clone(),
        };
        w.reach(root, Vec::new());
    }
    while let Some((f, args)) = w.queue.pop_front() {
        w.body(&f, &args);
    }
    w.of
}

/// The names of the parameters whose arguments each list of [`instantiations`] gives for `f`,
/// in order: `Self` for a trait's default method, then its impl's type parameters, then its
/// own, its value parameters among them.
#[must_use]
pub fn parameters(db: &dyn Db, program: Program, f: &FnRef) -> Vec<Name> {
    let cx = Cx { db, program };
    let decls = cx.decls();
    let own = matches!(f, FnRef::DefaultMethod(..)).then(|| Name::from("Self"));
    let params = signature(&decls, f)
        .map(|sig| sig.type_params)
        .unwrap_or_default();
    own.into_iter()
        .chain((params.iter()).map(|(g, _)| *stilt_types::generic_name(db, program, g.clone())))
        .collect()
}

struct Walk<'a> {
    cx: &'a Cx<'a>,
    kept: &'a dyn Fn(&FnRef) -> bool,
    seen: HashSet<(FnRef, Vec<Ty>)>,
    /// The trait uses on types without a written impl already followed into their parts.
    structural: HashSet<(Item, Ty)>,
    queue: VecDeque<(FnRef, Vec<Ty>)>,
    of: HashMap<FnRef, Vec<Vec<Ty>>>,
}

impl Walk<'_> {
    fn reach(&mut self, f: FnRef, args: Vec<Ty>) {
        let concrete = args
            .iter()
            .all(|t| !mentions_params(t) && parts(t) <= LARGEST);
        if !concrete || self.seen.len() >= MOST || self.seen.contains(&(f.clone(), args.clone())) {
            return;
        }
        self.seen.insert((f.clone(), args.clone()));
        self.of.entry(f.clone()).or_default().push(args.clone());
        self.queue.push_back((f, args));
    }

    /// Walks the body of `f` at the arguments `args`.
    fn body(&mut self, f: &FnRef, args: &[Ty]) {
        let Some(Where::Body(file, index)) = code_of(self.cx.db, self.cx.program, f.clone()) else {
            return;
        };
        let typed = &stilt_types::infer_body(self.cx.db, self.cx.program, file, index).body;
        let Definition::Code(code) = &typed.code else {
            return;
        };
        let subst = self.subst(f, args);
        let mut found: Vec<&Expr> = Vec::new();
        let mut visit = |e| found.push(e);
        match code {
            Code::Block(b) => walk::exprs_of_block(b, &mut visit),
            Code::Expr(e) => walk::iter(e, &mut |_| {}, &mut visit),
        }
        for e in found {
            self.expr(e, &subst);
        }
    }

    /// The substitution of the arguments `args` for the type parameters of `f`, but for a
    /// function that keeps its dictionaries, whose code is the same for every argument.
    fn subst(&self, f: &FnRef, args: &[Ty]) -> Subst {
        if (self.kept)(f) {
            return Subst::default();
        }
        let decls = self.cx.decls();
        let mut s = Subst::default();
        let mut args = args.iter().cloned();
        if let FnRef::DefaultMethod(..) = f {
            s.self_ty = args.next();
        }
        if let Some(sig) = signature(&decls, f) {
            s.types = sig
                .type_params
                .iter()
                .map(|(g, _)| g.clone())
                .zip(args)
                .collect();
        }
        s
    }

    fn expr(&mut self, e: &Expr, s: &Subst) {
        let t = Table::default();
        let ty = |x: &Ty| t.subst(s, x);
        match &e.kind {
            ExprKind::Call(c, targs, ..)
            | ExprKind::Project(c, targs, ..)
            | ExprKind::Callee(c, targs) => {
                let targs: Vec<Ty> = targs.iter().map(ty).collect();
                match c {
                    Callee::Function(item) => self.reach(FnRef::Function(item.clone()), targs),
                    Callee::Member(owner, name) => {
                        self.reach(FnRef::Member(owner.clone(), *name), targs);
                    }
                    Callee::TraitMethod(tr, name, self_ty) => {
                        self.method(tr, *name, &ty(self_ty), targs);
                    }
                    Callee::Operation(..) => {}
                }
            }
            ExprKind::Binary(op, a, _) => {
                let (tr, name) = match op {
                    BinaryOp::Eq | BinaryOp::Ne => ("Eq", "eq"),
                    BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => ("Ord", "compare"),
                    _ => return,
                };
                self.method(&prelude_item(tr), Name::from(name), &ty(&a.ty), Vec::new());
            }
            ExprKind::Interpolated(segments) => {
                for seg in segments {
                    if let Segment::Splice(x, _) = seg {
                        let show = (prelude_item("Show"), Name::from("show"));
                        self.method(&show.0, show.1, &ty(&x.ty), Vec::new());
                    }
                }
            }
            ExprKind::Index(base, key) if base.ty.is_prelude("Map") => {
                for (tr, name) in [("Hash", "hash"), ("Eq", "eq")] {
                    self.method(
                        &prelude_item(tr),
                        Name::from(name),
                        &ty(&key.ty),
                        Vec::new(),
                    );
                }
            }
            ExprKind::Constant(item) => self.reach(FnRef::Const(item.clone()), Vec::new()),
            _ => {}
        }
    }

    /// A trait's method called on a value of type `self_ty`: the impl of its constructor, or
    /// where the trait's impl for it is structural, the impls of the types it holds.
    fn method(&mut self, tr: &Item, name: Name, self_ty: &Ty, own: Vec<Ty>) {
        if mentions_params(self_ty) || parts(self_ty) > LARGEST {
            return;
        }
        let decls = self.cx.decls();
        let con = match self_ty {
            Ty::Con(item, _) => Some(item.clone()),
            _ => None,
        };
        if let Some(con) = &con
            && let Some(info) = decls.trait_impl(tr, con).cloned()
        {
            let holds = info.members.iter().any(|m| m.name == name);
            if holds || calls_own(&decls, tr, con, name) {
                let args = impl_targs(&decls, &info, self_ty)
                    .into_iter()
                    .chain(own)
                    .collect();
                self.reach(FnRef::ImplMethod(tr.clone(), con.clone(), name), args);
            } else {
                let args = std::iter::once(self_ty.clone()).chain(own).collect();
                self.reach(FnRef::DefaultMethod(tr.clone(), name), args);
            }
            return;
        }
        if !self.structural.insert((tr.clone(), self_ty.clone())) {
            return;
        }
        for part in components(&decls, self_ty) {
            self.method(tr, name, &part, own.clone());
        }
    }
}

/// The arguments of an impl's type parameters for the type `ty` it is used at.
fn impl_targs(decls: &dyn Lookup, info: &stilt_hir::decls::ImplInfo, ty: &Ty) -> Vec<Ty> {
    let table = Table::default();
    stilt_types::params::Args {
        decls,
        scope: &[],
        table: &table,
    }
    .impl_targs(info, ty)
}

/// The types a value of type `ty` holds, which a structural impl reaches the impls of.
fn components(decls: &dyn Lookup, ty: &Ty) -> Vec<Ty> {
    match ty {
        Ty::Tuple(ts) => ts.clone(),
        Ty::Con(item, args) => match decls.type_info(item) {
            Some(info) => {
                let field = |t: &stilt_hir::hir::Ty| instantiate(t, &info.params, args);
                match &info.def {
                    TypeDefInfo::Record(fields) => fields.iter().map(|(_, t)| field(t)).collect(),
                    TypeDefInfo::Variants(vs) => {
                        vs.iter().flat_map(|(_, ts)| ts.iter().map(field)).collect()
                    }
                    TypeDefInfo::Builtin => args.clone(),
                }
            }
            None => args.clone(),
        },
        _ => Vec::new(),
    }
}

/// The number of parts of a type, itself among them.
fn parts(ty: &Ty) -> usize {
    match ty {
        Ty::Con(_, args) | Ty::Tuple(args) => 1 + args.iter().map(parts).sum::<usize>(),
        _ => 1,
    }
}

/// Whether a type names a type parameter or `Self`, or is yet to be inferred.
fn mentions_params(ty: &Ty) -> bool {
    match ty {
        Ty::Param(_) | Ty::SelfTy | Ty::Var(_) | Ty::Spread(_) | Ty::App(..) => true,
        Ty::Con(_, args) | Ty::Tuple(args) => args.iter().any(mentions_params),
        Ty::Fn(f) => f.params.iter().any(|(_, p)| mentions_params(p)) || mentions_params(&f.ret),
        Ty::Handler(_) | Ty::Value(_) | Ty::Error => false,
    }
}
