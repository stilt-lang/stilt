//! The sites of facts.in-place-promise: writes in place under `without alloc`
//! (facts.writes-in-place), the copy at a call of an in-place parameter (facts.copy-at-call), and
//! the operations that may not end (facts.div).

use stilt_hir::hir::{LocalId, Mode};
use stilt_syntax::{TextRange, TextSize};

use super::super::in_place::{called, handed, is_window, written_list};
use super::super::limits::describe;
use super::super::{Fact, Pending, Site};
use super::{Finder, through_index};
use crate::tast::{Arg, Callee, Expr, ExprKind, Stmt};
use crate::ty::Ty;

impl Finder<'_> {
    /// The name of a binding, as messages write it.
    fn named(&self, v: LocalId) -> String {
        self.scope
            .body
            .locals
            .get(v.0 as usize)
            .map_or_else(|| "_".to_owned(), |n| format!("`{n}`"))
    }

    /// facts.writes-in-place: whether an assignment to `p`, the statement `s`, writes in place:
    /// under `without alloc`, an element of a list `b` that holds its own storage, `b[i]` or, when
    /// its elements aren't of a copy-on-write type, a part of one. Its site waits for the modes to
    /// say whether modes.shared-writes makes the write shared.
    pub(super) fn in_place(&self, s: &Stmt, p: &Expr) -> bool {
        if !self.scope.limits.alloc {
            return false;
        }
        let Some(v) = written_list(self.decls, p) else {
            return false;
        };
        if self.storage.own(v, s.at.start()).is_none() {
            return false;
        }
        self.push(Site {
            pending: Some(Pending {
                binding: v,
                modified: s.at,
                callee: None,
            }),
            ..Site::new(p.at, Vec::new())
        });
        true
    }

    /// facts.writes-in-place: whether a call is `view.into` or `view.split` on a list that the body
    /// holds the own storage of, under `without alloc`, which then copies nothing unless it is
    /// shared.
    pub(super) fn window(&self, c: &Callee, args: &[Arg]) -> bool {
        if !self.scope.limits.alloc || !is_window(c) {
            return false;
        }
        let Some(a) = args.first().filter(|a| a.mode == Mode::Inout) else {
            return false;
        };
        // A list of the error type allocates nothing that is reported (errors.error-type).
        if a.value.ty == Ty::Error {
            return true;
        }
        let Some(v) = super::super::in_place::named_list(a) else {
            return false;
        };
        if self.storage.own(v, a.value.at.start()).is_none() {
            return false;
        }
        self.push(Site {
            pending: Some(Pending {
                binding: v,
                modified: a.value.at,
                callee: None,
            }),
            ..Site::new(a.value.at, Vec::new())
        });
        true
    }

    /// facts.copy-at-call: each argument of a call that goes to an in-place parameter and needs a
    /// copy, which allocates and copies at the argument; and each `inout` argument that needs none
    /// unless modes.shared-writes makes its modification shared.
    pub(super) fn copies(&self, c: &Callee, args: &[Arg]) {
        let Some(callee) = called(self.decls, c) else {
            return;
        };
        let Some(params) = self.scope.in_place.get(&callee) else {
            return;
        };
        for (_, a) in args.iter().enumerate().filter(|(i, _)| params.contains(i)) {
            // An `inout` argument through an index already allocates, a list literal is a
            // value that nothing else holds, and an argument of the error type causes nothing
            // that is reported (errors.error-type).
            if (a.mode == Mode::Inout && through_index(&a.value))
                || matches!(a.value.kind, ExprKind::List(_))
                || a.value.ty == Ty::Error
            {
                continue;
            }
            match (handed(&self.storage, a), a.value.kind.clone()) {
                (Some(_), ExprKind::Local(v)) if a.mode == Mode::Inout => self.push(Site {
                    pending: Some(Pending {
                        binding: v,
                        modified: a.value.at,
                        callee: Some(callee.clone()),
                    }),
                    ..Site::new(a.value.at, Vec::new())
                }),
                (Some(_), _) => {}
                (None, kind) => {
                    let (what, because) = match kind {
                        ExprKind::Local(v) => {
                            let named = self.named(v);
                            let later = self.storage.later_use(v, a.value.at.start());
                            let because =
                                later.map(|at| (at, format!("{named} is used again here")));
                            (named, because)
                        }
                        _ => ("this argument".to_owned(), None),
                    };
                    let fact = copied(&what, &describe(self.scope.module, &callee));
                    self.push(Site {
                        alloc: Some(fact.clone()),
                        copy: Some(fact),
                        because,
                        ..Site::new(a.value.at, Vec::new())
                    });
                }
            }
        }
    }

    /// facts.div: a call through a function value that a field, a local binding or a parameter
    /// marked `escaping` holds, or any value but a parameter that isn't escaping and a closure
    /// literal written there, may not end.
    pub(super) fn stored_call(&self, e: &Expr, f: &Expr) {
        let body = self.scope.body;
        let through = match &f.instantiated().kind {
            ExprKind::Field(_, name) => format!("the field `{name}`"),
            ExprKind::Local(v) if body.params.iter().any(|(_, p)| p == v) => {
                if body.passing.contains(v) {
                    return;
                }
                format!("the `escaping` parameter {}", self.named(*v))
            }
            ExprKind::Local(v) => format!("the local {}", self.named(*v)),
            ExprKind::Closure(..) => return,
            _ => "a function value".to_owned(),
        };
        self.push(Site {
            div: Some(Fact {
                this: format!("this call through {through}"),
                a: format!("a call through {through}"),
            }),
            ..Site::new(e.at, Vec::new())
        });
    }

    /// handlers.implicit-effects-and-capabilities: a performance calls its handler's operation,
    /// which may not end, and allocates the rest of the performance, which a handler may keep to
    /// resume (facts.allocation).
    pub(super) fn performs(&self, e: &Expr, effect: &stilt_hir::hir::Item, op: &str) {
        let performed = format!("`{}.{op}`", effect.name);
        let fact = Fact {
            this: format!("this performance of {performed}"),
            a: format!("a performance of {performed}"),
        };
        self.push(Site {
            div: Some(fact.clone()),
            alloc: Some(fact),
            ..Site::new(e.at, Vec::new())
        });
    }

    /// facts.div: a `while` loop may not end, at its `while`, and a `loop`, at its `loop`.
    pub(super) fn diverges(&self, e: &Expr) {
        let (keyword, len) = match e.kind {
            ExprKind::Loop(_) => ("`loop`", 4),
            _ => ("`while` loop", 5),
        };
        let at = TextRange::at(e.at.start(), TextSize::from(len));
        // facts.closest-rule: what the counting loop needs.
        let need =
            (self.scope.accepted.loop_need(e.at)).map(|n| (super::super::Effect::Div, n.clone()));
        self.push(Site {
            div: Some(Fact::noun(keyword)),
            need,
            ..Site::new(at, Vec::new())
        });
    }
}

/// The fact of an argument copied for a callee that updates it in place (facts.copy-at-call).
fn copied(what: &str, callee: &str) -> Fact {
    let a = if what == "this argument" {
        "an argument"
    } else {
        what
    };
    Fact {
        this: format!("passing {what} to {callee} copies it, which"),
        a: format!("a copy of {a} for {callee}"),
    }
}
