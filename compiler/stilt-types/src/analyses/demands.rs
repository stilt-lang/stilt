//! The demands on the thread axes of modes (modes.fixed-values, modes.contended-values,
//! modes.demands and modes.diagnostic-shape): a value put in a `Shared<T>`, and a task's function,
//! must be `portable` (shared.tasks-and-modes and shared.std-sync), E0432, and a closure that
//! `std.par` runs must be `calm` and `portable` (par.what-runs-in-parallel), E0431. A value is
//! fixed when its type holds a view, or it is a closure that captures one, and contended when its
//! type holds a `Shared<T>`; a closure literal is either when a binding it captures is. A type
//! holds its fields' and its variants' types as its elements and arguments
//! ([`crate::holding`]).

use std::collections::{HashMap, HashSet};

use stilt_diag::{Diagnostic, codes};
use stilt_hir::decls::{Lookup, TypeDefInfo};
use stilt_hir::hir::{LocalId, Name};
use stilt_syntax::TextRange;

use super::views::Sources;
use crate::holding::holds;
use crate::tast::walk;
use crate::tast::{Block, Callee, Expr, ExprKind, PatKind, StmtKind};
use crate::ty::{Ty, instantiate, is_shared};

/// What an argument must be.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Demand {
    /// E0432 (shared.tasks-and-modes).
    Portable,
    /// E0431 (par.what-runs-in-parallel).
    CalmPortable,
}

/// The arguments that a call's callee makes demands of, by their places, a receiver first.
fn demands(callee: &Callee) -> &'static [(usize, Demand)] {
    match callee {
        Callee::Member(owner, name) if is_shared(owner) && &**name == "new" => {
            &[(0, Demand::Portable)]
        }
        Callee::Member(owner, name) if is_scope(owner) && &**name == "spawn" => {
            &[(1, Demand::Portable)]
        }
        Callee::Function(item) => match (&*item.home, &*item.name) {
            ("std.task", "spawn") => &[(0, Demand::Portable)],
            ("std.par", "map" | "each") => &[(1, Demand::CalmPortable)],
            ("std.par", "both") => &[(0, Demand::CalmPortable), (1, Demand::CalmPortable)],
            ("std.par", "fold") => &[(2, Demand::CalmPortable)],
            _ => &[],
        },
        _ => &[],
    }
}

/// Whether a type constructor is `std.task`'s `Scope` (tasks.scopes).
pub(crate) fn is_scope(item: &stilt_hir::hir::Item) -> bool {
    (&*item.home, &*item.name) == ("std.task", "Scope")
}

/// Whether the argument at `index` of a call of `callee` is demanded to be `portable`, so that
/// the errors of views leave it to this analysis.
pub(crate) fn demanded(callee: &Callee, index: usize) -> bool {
    demands(callee).iter().any(|(i, _)| *i == index)
}

/// modes.fixed-values, and views.fixed: a type that holds a view.
fn fixed_type(decls: &dyn Lookup, ty: &Ty) -> bool {
    holds(decls, ty, &Ty::is_view)
}

/// modes.contended-values: whether a type is a `Shared<T>`, which a contended type holds.
fn is_shared_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::Con(item, _) if is_shared(item))
}

/// How a captured binding's type holds what `p` accepts, `what`, for a message and for its note:
/// it is one, which `why` explains, a field or a variant of its declared type holds one, or it
/// holds one otherwise, as an element or a type argument does (modes.mode-crossing). The two
/// last leave `why` out, so that the message stays short (modes.diagnostic-shape).
fn held_how(
    decls: &dyn Lookup,
    ty: &Ty,
    p: &dyn Fn(&Ty) -> bool,
    what: &str,
    why: &str,
) -> (String, String) {
    if p(ty) {
        return (format!("{what}, {why}"), format!("is {what}"));
    }
    let held = format!("holds {what}");
    let part = match ty {
        Ty::Con(item, args) => decls.type_info(item).and_then(|info| {
            let at = |t| instantiate(t, &info.params, args);
            match &info.def {
                TypeDefInfo::Record(fields) => fields
                    .iter()
                    .find(|(_, t)| holds(decls, &at(t), p))
                    .map(|(f, _)| format!("whose field `{f}`")),
                TypeDefInfo::Variants(vs) => vs
                    .iter()
                    .find(|(_, ts)| ts.iter().any(|t| holds(decls, &at(t), p)))
                    .map(|(v, _)| format!("whose variant `{v}`")),
                TypeDefInfo::Builtin => None,
            }
        }),
        _ => None,
    };
    let part = part.unwrap_or_else(|| "which".to_owned());
    (format!("{part} {held}"), held)
}

struct Demands<'a> {
    decls: &'a dyn Lookup,
    locals: &'a [Name],
    /// Where each parameter is declared.
    params: &'a [(LocalId, TextRange)],
    sources: &'a Sources,
    /// The closure literals that a `let` binds to a name.
    closures: HashMap<LocalId, &'a Expr>,
    errors: Vec<Diagnostic>,
}

/// The errors of the demands of every call in a body.
pub(crate) fn errors(
    decls: &dyn Lookup,
    locals: &[Name],
    params: &[(LocalId, TextRange)],
    sources: &Sources,
    block: &Block,
) -> Vec<Diagnostic> {
    let mut d = Demands {
        decls,
        locals,
        params,
        sources,
        closures: HashMap::new(),
        errors: Vec::new(),
    };
    walk::iter_block(
        block,
        &mut |s| {
            if let StmtKind::Let(b) = &s.kind
                && let PatKind::Bind(v) = b.pattern.kind
                && matches!(b.value.kind, ExprKind::Closure(..))
            {
                d.closures.insert(v, &b.value);
            }
        },
        &mut |_| {},
    );
    walk::exprs_of_block(block, &mut |e| {
        if let ExprKind::Call(callee, _, args, _) = &e.kind {
            for &(i, demand) in demands(callee) {
                if let Some(a) = args.get(i) {
                    d.check(callee, demand, &a.value);
                }
            }
        }
    });
    d.errors
}

impl<'a> Demands<'a> {
    /// The closure literal that an argument is, or that the binding it names holds.
    fn literal(&self, a: &'a Expr) -> Option<&'a Expr> {
        match &a.kind {
            ExprKind::Closure(..) => Some(a),
            ExprKind::Local(v) => self.closures.get(v).copied(),
            _ => None,
        }
    }

    /// Whether a captured binding's use is fixed: of a type that holds a view, or a closure
    /// that captures one.
    fn fixed(&self, use_: &Expr) -> bool {
        fixed_type(self.decls, &use_.ty) || !self.sources.sources(use_).is_empty()
    }

    fn check(&mut self, callee: &Callee, demand: Demand, a: &'a Expr) {
        match (demand, self.literal(a)) {
            (Demand::Portable, Some(closure)) => {
                let Some((v, use_)) = captures(closure).into_iter().find(|(_, u)| self.fixed(u))
                else {
                    return;
                };
                let name = self.locals[v.0 as usize];
                let message = format!(
                    "this task's function captures `{name}`, a view, which can't reach another \
                     task"
                );
                let d = Diagnostic::new(codes::E0432, use_.at, message);
                let d = self.noted(d, v, "is a view");
                self.errors.push(d);
            }
            (Demand::Portable, None) if self.fixed(a) => {
                let message = if matches!(callee, Callee::Member(owner, _) if is_shared(owner)) {
                    "this value holds a view, which can't be put in a `Shared<T>`"
                } else {
                    "this function holds a view, which can't reach another task"
                };
                self.errors
                    .push(Diagnostic::new(codes::E0432, a.at, message));
            }
            (Demand::CalmPortable, Some(closure)) => self.calm_portable(a, closure),
            _ => {}
        }
    }

    /// E0431 at a closure given to `std.par` that reaches a `Shared<T>` or a view.
    fn calm_portable(&mut self, a: &Expr, closure: &Expr) {
        let decls = self.decls;
        let thread = "which can't leave its source's thread";
        let reached = captures(closure).into_iter().find_map(|(v, use_)| {
            let ty = &use_.ty;
            if holds(decls, ty, &is_shared_ty) {
                let why = "which only a `when` reads";
                let (how, note) = held_how(decls, ty, &is_shared_ty, "a `Shared<T>`", why);
                Some((v, how, note))
            } else if fixed_type(decls, ty) {
                let (how, note) = held_how(decls, ty, &Ty::is_view, "a view", thread);
                Some((v, how, note))
            } else if self.fixed(use_) {
                Some((v, format!("a view, {thread}"), "is a view".to_owned()))
            } else {
                None
            }
        });
        if let Some((v, why, note)) = reached {
            let name = self.locals[v.0 as usize];
            let message = format!("this closure can't run in parallel: it reaches `{name}`, {why}");
            let d = Diagnostic::new(codes::E0431, a.at, message);
            let d = self.noted(d, v, &note);
            self.errors.push(d);
        }
    }

    /// modes.diagnostic-shape: one note at the binding that gave `v` its mode, when it is a
    /// parameter or a binding of a view, which says what `note` says of it.
    fn noted(&self, d: Diagnostic, v: LocalId, note: &str) -> Diagnostic {
        let at = self
            .params
            .iter()
            .find(|(p, _)| *p == v)
            .map(|(_, at)| *at)
            .or_else(|| self.sources.binding_at(v));
        match at {
            Some(at) => {
                let name = self.locals[v.0 as usize];
                d.with_note(at, format!("`{name}` {note} from here"))
            }
            None => d,
        }
    }
}

/// The uses, in a closure literal's body, of the bindings it captures: those that no pattern
/// inside it binds, in the order they are written.
pub(crate) fn captures(closure: &Expr) -> Vec<(LocalId, &Expr)> {
    let ExprKind::Closure(_, body) = &closure.kind else {
        return Vec::new();
    };
    let bound: HashSet<LocalId> = super::views::sources::declared_in(closure);
    let mut found = Vec::new();
    walk::iter(body, &mut |_| {}, &mut |x| {
        if let ExprKind::Local(v) = x.kind
            && !bound.contains(&v)
        {
            found.push((v, x));
        }
    });
    found
}
