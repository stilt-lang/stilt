//! Parameters that escape (effects.non-escaping-parameters and effects.no-escape): each occurrence
//! of a non-escaping parameter, and each closure literal that contains one at any depth, is the
//! callee of a call or an argument given to a non-escaping parameter of the function or method that
//! a call names, or E0508. A binding of type `Scope<E>` is checked as such a parameter is, but may
//! also be given to a parameter of that type, as the receiver of `s.spawn` is, or E0434
//! (tasks.scope-that-escapes).

use std::collections::BTreeMap;

use stilt_diag::{Diagnostic, codes};
use stilt_hir::hir::{LocalId, Mode, Name};
use stilt_syntax::{TextRange, TextSize};

use super::demands::is_scope;
use super::signature::SigInfo;
use crate::tast::walk;
use crate::tast::{Block, Expr, ExprKind, PatKind, StmtKind, TypedBody};
use crate::ty::Ty;

/// Where an expression is, as far as escaping goes: where a non-escaping parameter may be, or
/// where its value is kept, with the phrase that says where.
#[derive(Clone, Debug)]
enum Place {
    Allowed,
    Kept(String),
}

/// What the walk has found: for each parameter that escapes, by its place among the
/// parameters, the first place where it does, and what keeps it there.
struct Escapes<'a> {
    passing: &'a [(LocalId, usize)],
    names: &'a [Name],
    found: BTreeMap<usize, (TextSize, TextRange, String, bool)>,
}

impl Escapes<'_> {
    /// The non-escaping parameter that `e` is, if it is one, by its place.
    fn param(&self, e: &Expr) -> Option<usize> {
        match &e.kind {
            ExprKind::Local(v) => self
                .passing
                .iter()
                .find(|(w, _)| w == v)
                .map(|&(_, index)| index),
            _ => None,
        }
    }

    /// The non-escaping parameters that occur in `e`, by their places.
    fn occurring(&self, e: &Expr) -> Vec<usize> {
        let mut found = Vec::new();
        walk::iter(e, &mut |_| {}, &mut |x| {
            if let Some(i) = self.param(x)
                && !found.contains(&i)
            {
                found.push(i);
            }
        });
        found
    }

    /// Records that the parameter at `index` escapes at `at`, by itself or in a closure, kept
    /// as `kept` says, unless it escapes earlier.
    fn escape(&mut self, index: usize, at: TextRange, kept: &str, closure: bool) {
        let entry = (at.start(), at, kept.to_owned(), closure);
        self.found
            .entry(index)
            .and_modify(|e| {
                if entry.0 < e.0 {
                    *e = entry.clone();
                }
            })
            .or_insert(entry);
    }

    fn expr(&mut self, e: &Expr, place: &Place) {
        if let Place::Kept(kept) = place {
            if let Some(i) = self.param(e) {
                self.escape(i, e.at, kept, false);
            } else if matches!(e.kind, ExprKind::Closure(..)) {
                for i in self.occurring(e) {
                    self.escape(i, e.at, kept, true);
                }
            }
        }
        match &e.kind {
            ExprKind::Call(_, _, args, _) | ExprKind::Project(_, _, args, _) => {
                for a in args {
                    let scope = matches!(&a.value.ty, Ty::Con(item, _) if is_scope(item));
                    let place = if (a.passes && a.mode == Mode::Let) || scope {
                        Place::Allowed
                    } else {
                        kept_by_param()
                    };
                    self.expr(&a.value, &place);
                }
            }
            ExprKind::CallValue(f, args) => {
                self.expr(f, &Place::Allowed);
                for a in args {
                    self.expr(
                        &a.value,
                        &Place::Kept("passed to a function value here".into()),
                    );
                }
            }
            // handlers.handler-literals: installing a handler is a use it may have, as a call is.
            ExprKind::With(h, _, _, b) => {
                self.expr(h, &Place::Allowed);
                self.block(b, &Place::Kept(stored(e)));
            }
            // An instantiation is the value it instantiates (polymorphism.instantiation).
            ExprKind::Instantiate(value, _) => self.expr(value, place),
            ExprKind::Closure(_, body) => self.expr(body, &Place::Kept("returned here".into())),
            ExprKind::Block(b) => self.block(b, place),
            ExprKind::Return(value) => {
                if let Some(v) = value {
                    self.expr(v, &Place::Kept("returned here".into()));
                }
            }
            _ => {
                let inner = Place::Kept(stored(e));
                for part in walk::parts(e) {
                    match part {
                        walk::Part::Expr(x) => self.expr(x, &inner),
                        walk::Part::Block(b) => self.block(b, &inner),
                    }
                }
            }
        }
    }

    /// The statements of a block whose final expression, if it is one, is in `tail`.
    fn block(&mut self, b: &Block, tail: &Place) {
        for (i, s) in b.iter().enumerate() {
            let last = i + 1 == b.len();
            match &s.kind {
                StmtKind::Expr(e) if last => self.expr(e, tail),
                StmtKind::Let(binding) | StmtKind::Var(binding) => {
                    let kept = match &binding.pattern.kind {
                        PatKind::Bind(v) => self.names.get(v.0 as usize).map_or_else(
                            || "bound to a local here".to_owned(),
                            |n| format!("bound to `{n}` here"),
                        ),
                        _ => "bound to a local here".to_owned(),
                    };
                    self.expr(&binding.value, &Place::Kept(kept));
                    if let Some(otherwise) = &binding.otherwise {
                        self.expr(otherwise, &Place::Kept("used as a value here".into()));
                    }
                }
                StmtKind::Assign(_, place, value) => {
                    self.expr(place, &Place::Kept("used as a value here".into()));
                    self.expr(value, &Place::Kept("assigned here".into()));
                }
                StmtKind::Assert(e) | StmtKind::Expr(e) => {
                    self.expr(e, &Place::Kept("used as a value here".into()));
                }
                // projections.yield: yielding a binding is where it escapes (modes.escaping).
                StmtKind::Yield(e) => {
                    self.expr(e, &Place::Kept("yielded here".into()));
                }
            }
        }
    }
}

fn kept_by_param() -> Place {
    Place::Kept("passed to a parameter that keeps it here".into())
}

/// What keeps a value that is a part of `e`.
fn stored(e: &Expr) -> String {
    match &e.kind {
        ExprKind::Record(item, _, _) => format!("stored in a `{}` here", item.name),
        ExprKind::Construct(item, _, _) => format!("stored in `{}` here", item.name),
        ExprKind::List(_) => "stored in a list here".to_owned(),
        ExprKind::Tuple(_) => "stored in a tuple here".to_owned(),
        _ => "used as a value here".to_owned(),
    }
}

/// The bindings of type `Scope<E>` that a body names, in order (tasks.scope-that-escapes).
fn scopes(block: &Block) -> Vec<LocalId> {
    let mut found = Vec::new();
    walk::exprs_of_block(block, &mut |e| {
        if let ExprKind::Local(v) = e.kind
            && matches!(&e.ty, Ty::Con(item, _) if is_scope(item))
            && !found.contains(&v)
        {
            found.push(v);
        }
    });
    found
}

/// E0508 once for each non-escaping parameter of the body, and E0434 once for each scope it
/// names, that escapes, at the first place in source order where it does. Scopes are numbered
/// after the parameters.
pub(crate) fn errors(sig: &SigInfo<'_>, body: &TypedBody, block: &Block) -> Vec<Diagnostic> {
    let mut passing: Vec<(LocalId, usize)> = body
        .passing
        .iter()
        .filter_map(|v| {
            let index = body.params.iter().position(|(_, w)| w == v)?;
            Some((*v, index))
        })
        .collect();
    let first_scope = body.params.len();
    passing.extend(scopes(block).into_iter().zip(first_scope..));
    if passing.is_empty() {
        return Vec::new();
    }
    let mut escapes = Escapes {
        passing: &passing,
        names: &body.locals,
        found: BTreeMap::new(),
    };
    escapes.block(block, &Place::Kept("returned here".into()));
    let mut found: Vec<_> = escapes.found.into_iter().collect();
    found.sort_by_key(|(index, (start, ..))| (*start, *index));
    found
        .into_iter()
        .map(|(index, (_, at, kept, closure))| {
            match passing
                .iter()
                .find(|(_, i)| *i == index && index >= first_scope)
            {
                Some((v, _)) => scope_escapes(body.locals[v.0 as usize], at, kept, closure),
                None => param_escapes(sig, index, at, kept, closure),
            }
        })
        .collect()
}

/// E0434 for a scope that is kept, by itself or in a closure: it ends when `task.scope` returns.
fn scope_escapes(name: Name, at: TextRange, kept: String, closure: bool) -> Diagnostic {
    let message = if closure {
        format!(
            "this closure is kept, but it captures the scope `{name}`, which ends when \
             `task.scope` returns"
        )
    } else {
        format!("the scope `{name}` is kept, but it ends when `task.scope` returns")
    };
    Diagnostic::new(codes::E0434, at, message).with_label(kept)
}

/// E0508 for the parameter at `index`, kept by itself or in a closure.
fn param_escapes(
    sig: &SigInfo<'_>,
    index: usize,
    at: TextRange,
    kept: String,
    closure: bool,
) -> Diagnostic {
    let name = sig
        .params
        .get(index)
        .map_or_else(|| Name::from("_"), |(n, _)| *n);
    let message = if closure {
        format!(
            "this closure is kept, but it calls `{name}`, whose effects pass through to the caller"
        )
    } else {
        format!("`{name}` is kept, but its effects pass through to the caller")
    };
    let mut d = Diagnostic::new(codes::E0508, at, message).with_label(kept);
    if let Some((_, declared)) = sig.params.get(index) {
        d = d.with_note(*declared, "its effects pass through");
    }
    sig.escaping_fix(index)
        .into_iter()
        .fold(d, Diagnostic::with_fix)
}
