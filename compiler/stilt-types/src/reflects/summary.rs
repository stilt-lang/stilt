//! What the fixed point of `reflects` and the checks of E0350 read of one function's typed body
//! (meta.reflects and meta.types-without-shape): the type parameters whose shape, name or bound
//! test it names, the functions it instantiates with the types it gives them, and the type whose
//! shape each fresh type is a part of.

use stilt_hir::decls::Lookup;
use stilt_hir::hir::{GenericId, Item};
use stilt_syntax::TextRange;

use crate::analyses::implicit::Key;
use crate::tast::walk::{Part, parts};
use crate::tast::{
    Arm, Block, Callee, Expr, ExprKind, Iterable, Pat, PatKind, Reflection, StmtKind,
};
use crate::ty::{Ty, is_shape_case};

/// A use of a function: a call, or its name as a value.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Use {
    pub(crate) callee: Key,
    /// The callee's type parameters, with the types the use gives them.
    pub targs: Vec<(GenericId, Ty)>,
    /// The call or the name.
    pub at: TextRange,
    /// The arguments of a call, each with its type.
    pub args: Vec<(TextRange, Ty)>,
    /// Whether the function is named as a value given for a polymorphic function type, whose
    /// instantiations can't be seen (meta.unseen-instantiations).
    pub poly: bool,
}

/// What a function's body reads of types.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Summary {
    pub key: Key,
    /// The types whose shape the body names, each where it names it first.
    pub shapes: Vec<(Ty, TextRange)>,
    /// The types whose name or a bound test the body names, which the debug build passes a
    /// descriptor of.
    pub described: Vec<Ty>,
    /// The traits that the bound tests on each type name (meta.reflects).
    pub guards: Vec<(Ty, Item)>,
    pub uses: Vec<Use>,
    /// Each fresh type, and each rigid type of a closure given for `fields.build`, with the
    /// type whose shape it is a part of (meta.fresh-types and meta.building).
    pub fresh_of: Vec<(GenericId, Ty)>,
    /// In an impl's method, each of its own type parameters with the trait method's that it
    /// stands for, whose callers reach it through the trait.
    pub to_trait: Vec<(GenericId, GenericId)>,
}

/// The summary of a function's typed body.
pub(crate) fn summary(decls: &dyn Lookup, key: Key, block: &Block) -> Summary {
    let to_trait = super::bounds::own_of_trait(decls, &key);
    let mut s = Summary {
        key,
        shapes: Vec::new(),
        described: Vec::new(),
        guards: Vec::new(),
        uses: Vec::new(),
        fresh_of: Vec::new(),
        to_trait,
    };
    for stmt in block {
        stmt_parts(decls, &mut s, &stmt.kind);
    }
    s
}

fn stmt_parts(decls: &dyn Lookup, s: &mut Summary, kind: &StmtKind) {
    match kind {
        StmtKind::Let(b) | StmtKind::Var(b) => {
            expr(decls, s, &b.value);
            if let Some(e) = &b.otherwise {
                expr(decls, s, e);
            }
        }
        StmtKind::Assign(_, p, v) => {
            expr(decls, s, p);
            expr(decls, s, v);
        }
        StmtKind::Assert(e) | StmtKind::Yield(e) | StmtKind::Expr(e) => expr(decls, s, e),
    }
}

/// The parts of a pattern's type that are parts of `of`'s shape: the fresh types it holds.
fn fresh_in(s: &mut Summary, p: &Pat, of: &Ty) {
    let mut found = Vec::new();
    params_of(&p.ty, &mut found);
    for g in found.into_iter().filter(|g| g.is_fresh() || g.is_poly()) {
        if !s.fresh_of.iter().any(|(f, _)| *f == g) {
            s.fresh_of.push((g, of.clone()));
        }
    }
}

/// The type parameters a type names, in order and each once.
pub(super) fn params_of(t: &Ty, out: &mut Vec<GenericId>) {
    match t {
        Ty::Param(g) if !out.contains(g) => out.push(g.clone()),
        Ty::Con(_, ts) | Ty::Tuple(ts) => ts.iter().for_each(|t| params_of(t, out)),
        Ty::App(head, ts) => {
            params_of(head, out);
            for t in ts {
                params_of(t, out);
            }
        }
        Ty::Fn(f) => {
            f.params.iter().for_each(|(_, t)| params_of(t, out));
            params_of(&f.ret, out);
        }
        Ty::Spread(sp) => params_of(&sp.elem, out),
        _ => {}
    }
}

fn arms(s: &mut Summary, scrutinee: &Expr, arms: &[Arm]) {
    let shape = scrutinee.ty.meta_of("Shape").cloned();
    for a in arms {
        if let (Some(of), PatKind::Variant(case, ps)) = (&shape, &a.pattern.kind)
            && is_shape_case(case)
        {
            for p in ps {
                fresh_in(s, p, of);
            }
        }
    }
}

fn expr(decls: &dyn Lookup, s: &mut Summary, e: &Expr) {
    match &e.kind {
        ExprKind::Reflect(Reflection::Shape, t) => {
            let t = of_self(s, t);
            if !s.shapes.iter().any(|(u, _)| *u == t) {
                s.shapes.push((t, e.at));
            }
        }
        ExprKind::Reflect(Reflection::Name, t) => described(s, t),
        // A bound test reads the descriptors of `T` and of the bound's arguments
        // (meta.bound-tests).
        ExprKind::Bound(t, traits) => {
            described(s, t);
            for (tr, args) in traits {
                s.guards.push((t.clone(), tr.clone()));
                for a in args {
                    described(s, a);
                }
            }
        }
        ExprKind::Call(callee, targs, args, _) | ExprKind::Project(callee, targs, args, _) => {
            let args = args
                .iter()
                .map(|a| (a.value.at, a.value.ty.clone()))
                .collect();
            used(decls, s, (callee, targs), (e.at, args, false));
        }
        ExprKind::Callee(callee, targs) => {
            let poly = matches!(&e.ty, Ty::Fn(f) if f.is_poly());
            used(decls, s, (callee, targs), (e.at, Vec::new(), poly));
        }
        _ => opened(s, e),
    }
    for part in parts(e) {
        match part {
            Part::Expr(x) => expr(decls, s, x),
            Part::Block(b) => {
                for stmt in b {
                    stmt_parts(decls, s, &stmt.kind);
                }
            }
        }
    }
}

/// The fresh types that an expression opens, of a shape's case matched by `match` or `if let`,
/// or of a field or a variant that `for` binds, and the rigid type of a closure given for
/// `fields.build`, which is the field's type (meta.fresh-types, meta.fields and
/// meta.variant-cases).
fn opened(s: &mut Summary, e: &Expr) {
    match &e.kind {
        ExprKind::Match(scrutinee, a) => arms(s, scrutinee, a),
        ExprKind::IfLet(p, scrutinee, ..) => {
            if let (Some(of), PatKind::Variant(case, ps)) = (scrutinee.ty.meta_of("Shape"), &p.kind)
                && is_shape_case(case)
            {
                let of = of.clone();
                for q in ps {
                    fresh_in(s, q, &of);
                }
            }
        }
        ExprKind::For(p, iterable, _) => {
            if let Iterable::Iter(source) = &**iterable
                && let Some(of) = source
                    .ty
                    .meta_of("Fields")
                    .or_else(|| source.ty.meta_of("Cases"))
            {
                let of = of.clone();
                fresh_in(s, p, &of);
            }
        }
        ExprKind::Closure(ps, _) => {
            for p in ps {
                if let Some(of) = p.ty.meta_of("Field") {
                    let of = of.clone();
                    fresh_in(s, p, &of);
                }
            }
        }
        _ => {}
    }
}

fn described(s: &mut Summary, t: &Ty) {
    let t = of_self(s, t);
    if !s.described.contains(&t) {
        s.described.push(t);
    }
}

/// A type as the facts name it: in a trait's default method, `Self` is a parameter that each
/// impl gives ([`super::self_param`]).
pub(super) fn of_self(s: &Summary, t: &Ty) -> Ty {
    if !matches!(s.key, Key::DefaultMethod(..)) {
        return t.clone();
    }
    match t {
        Ty::SelfTy => Ty::Param(super::self_param()),
        Ty::Con(item, ts) => Ty::Con(item.clone(), ts.iter().map(|t| of_self(s, t)).collect()),
        Ty::Tuple(ts) => Ty::Tuple(ts.iter().map(|t| of_self(s, t)).collect()),
        Ty::App(head, ts) => Ty::App(
            Box::new(of_self(s, head)),
            ts.iter().map(|t| of_self(s, t)).collect(),
        ),
        other => other.clone(),
    }
}

/// A use of `callee` at `targs`, whose instantiation the fixed point and E0350 read: of a
/// function of a module or of an inherent impl. A trait's method is reached through its impl,
/// whose own type parameters are checked where a bound is met (meta.unseen-instantiations).
fn used(
    decls: &dyn Lookup,
    s: &mut Summary,
    (callee, targs): (&Callee, &[Ty]),
    (at, args, poly): (TextRange, Vec<(TextRange, Ty)>, bool),
) {
    let (key, params) = match callee {
        Callee::Function(item) => {
            let Some(sig) = decls.function(item) else {
                return;
            };
            (Key::Function(item.clone()), &sig.type_params)
        }
        Callee::Member(owner, name) => {
            let Some(m) = decls
                .inherent_members(owner)
                .iter()
                .find(|m| m.name == *name)
            else {
                return;
            };
            (Key::Member(owner.clone(), *name), &m.signature.type_params)
        }
        // A trait's method called on a type, whose impl it reaches, meets the trait's bound,
        // and gives the trait's method its own type arguments and `Self`.
        Callee::TraitMethod(t, name, ty) => {
            super::bounds::met(decls, s, (t, ty), (at, &args));
            super::bounds::method_used(decls, s, (t, *name, ty), (targs, (at, &args)));
            return;
        }
        Callee::Operation(..) => return,
    };
    for ((_, bounds), x) in params.iter().zip(targs) {
        for b in bounds {
            super::bounds::met(decls, s, (b, x), (at, &args));
        }
    }
    if params.is_empty() {
        return;
    }
    let targs = params
        .iter()
        .map(|(g, _)| g.clone())
        .zip(targs.iter().map(|t| of_self(s, t)))
        .collect();
    s.uses.push(Use {
        callee: key,
        targs,
        at,
        args,
        poly,
    });
}
