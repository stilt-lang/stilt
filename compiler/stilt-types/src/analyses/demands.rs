//! The demands on the thread axes of modes (modes.fixed-values, modes.contended-values,
//! modes.demands and modes.diagnostic-shape): a value put in a `Shared<T>`, and a task's function,
//! must be `portable` (shared.tasks-and-modes and shared.std-sync), E0432, and a closure that
//! `std.par` runs must be `calm` and `portable` (par.what-runs-in-parallel), E0431. A value is
//! fixed when its type holds a view, or it is a closure that captures one, and contended when its
//! type holds a `Shared<T>`; a closure literal is either when a binding it captures is.

use std::collections::{HashMap, HashSet};

use stilt_diag::{Diagnostic, codes};
use stilt_hir::hir::{LocalId, Name};
use stilt_syntax::TextRange;

use super::views::Sources;
use crate::tast::walk;
use crate::tast::{Block, Callee, Expr, ExprKind, PatKind, StmtKind};
use crate::ty::{Ty, is_shared};

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

/// Whether a type holds a type that `p` accepts, at any depth.
pub(crate) fn holds(ty: &Ty, p: &dyn Fn(&Ty) -> bool) -> bool {
    p(ty)
        || match ty {
            Ty::Con(_, ts) | Ty::Tuple(ts) => ts.iter().any(|t| holds(t, p)),
            Ty::App(head, ts) => holds(head, p) || ts.iter().any(|t| holds(t, p)),
            Ty::Spread(s) => holds(&s.elem, p),
            Ty::Fn(f) => f.params.iter().any(|(_, t)| holds(t, p)) || holds(&f.ret, p),
            Ty::Param(_) | Ty::SelfTy | Ty::Handler(_) | Ty::Var(_) | Ty::Value(_) | Ty::Error => {
                false
            }
        }
}

/// modes.fixed-values, and views.fixed: a type that holds a view.
fn fixed_type(ty: &Ty) -> bool {
    holds(ty, &Ty::is_view)
}

/// modes.contended-values: a type that holds a `Shared<T>`.
fn contended_type(ty: &Ty) -> bool {
    holds(ty, &|t| matches!(t, Ty::Con(item, _) if is_shared(item)))
}

struct Demands<'a> {
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
    locals: &[Name],
    params: &[(LocalId, TextRange)],
    sources: &Sources,
    block: &Block,
) -> Vec<Diagnostic> {
    let mut d = Demands {
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
        fixed_type(&use_.ty) || !self.sources.sources(use_).is_empty()
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
                let d = self.noted(d, v, "a view");
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
        let reached = captures(closure).into_iter().find_map(|(v, use_)| {
            if contended_type(&use_.ty) {
                Some((
                    v,
                    "a `Shared<T>`, which only a `when` reads",
                    "a `Shared<T>`",
                ))
            } else if self.fixed(use_) {
                Some((v, "a view, which can't leave its source's thread", "a view"))
            } else {
                None
            }
        });
        if let Some((v, why, what)) = reached {
            let name = self.locals[v.0 as usize];
            let message = format!("this closure can't run in parallel: it reaches `{name}`, {why}");
            let d = Diagnostic::new(codes::E0431, a.at, message);
            let d = self.noted(d, v, what);
            self.errors.push(d);
        }
    }

    /// modes.diagnostic-shape: one note at the binding that gave `v` its mode, when it is a
    /// parameter or a binding of a view.
    fn noted(&self, d: Diagnostic, v: LocalId, what: &str) -> Diagnostic {
        let at = self
            .params
            .iter()
            .find(|(p, _)| *p == v)
            .map(|(_, at)| *at)
            .or_else(|| self.sources.binding_at(v));
        match at {
            Some(at) => {
                let name = self.locals[v.0 as usize];
                d.with_note(at, format!("`{name}` is {what} from here"))
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
