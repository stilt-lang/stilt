//! Descending self-calls (facts.descending-self-calls): the bindings of a body that hold a part of
//! one of its function's `let` parameters, reached by fields, tuple elements and variants'
//! payloads, and whether every call of the function to itself passes a strict part of one
//! parameter.

use std::collections::HashMap;

use stilt_hir::hir::{LocalId, Mode};

use crate::tast::{Code, Expr, ExprKind, Pat, PatKind, Stmt, StmtKind, TypedBody};

use super::walk_code;

/// The bindings a pattern binds, in order.
pub(super) fn bound(p: &Pat) -> Vec<LocalId> {
    let mut out = Vec::new();
    binders(p, 0, &mut |v, _| out.push(v));
    out
}

/// Each binding of a pattern, with the number of steps it takes into the value: a variant's
/// payload, a tuple's element and a record's field are a step each, and an element of a list
/// isn't a part (the rule takes no step through an index).
fn binders(p: &Pat, depth: u32, f: &mut dyn FnMut(LocalId, Option<u32>)) {
    match &p.kind {
        PatKind::Bind(v) => f(*v, Some(depth)),
        PatKind::Tuple(ps) | PatKind::Variant(_, ps) => {
            for p in ps {
                binders(p, depth + 1, f);
            }
        }
        PatKind::Record(fields) => {
            for (_, p) in fields {
                binders(p, depth + 1, f);
            }
        }
        PatKind::Or(ps) => {
            for p in ps {
                binders(p, depth, f);
            }
        }
        PatKind::List(ps, _) => {
            let mut none = |v, _| f(v, None);
            for p in ps {
                binders(p, depth, &mut none);
            }
        }
        PatKind::Wild
        | PatKind::Int(_)
        | PatKind::Str(_)
        | PatKind::Bool(_)
        | PatKind::Const(_)
        | PatKind::Error => {}
    }
}

/// The parts of a body's `let` parameters that its bindings hold: each binding that holds one,
/// with the parameter, by its place, and whether the part is strict.
#[derive(Debug, Default)]
pub(super) struct Parts {
    held: HashMap<LocalId, (usize, bool)>,
    /// The number of the function's parameters.
    params: usize,
}

impl Parts {
    pub(super) fn of(body: &TypedBody, code: &Code) -> Self {
        let mut parts = Self {
            held: (0..)
                .zip(&body.params)
                .filter(|(_, (mode, _))| *mode == Mode::Let)
                .map(|(i, (_, v))| (*v, (i, false)))
                .collect(),
            params: body.params.len(),
        };
        let stmts = std::cell::RefCell::new(Vec::new());
        let exprs = std::cell::RefCell::new(Vec::new());
        walk_code(code, &mut |s| stmts.borrow_mut().push(s), &mut |e| {
            exprs.borrow_mut().push(e);
        });
        // A binding is bound before it is used, and statements and expressions are walked in
        // the order they are written, so one pass over each in order finds every part.
        let mut stmts = stmts.into_inner().into_iter().peekable();
        for e in exprs.into_inner() {
            while let Some(s) = stmts.next_if(|s: &&Stmt| s.at.start() <= e.at.start()) {
                parts.stmt(s);
            }
            parts.expr(e);
        }
        for s in stmts {
            parts.stmt(s);
        }
        parts
    }

    /// The parameter whose part a place holds, and whether the part is strict: a place made of
    /// fields and tuple elements, rooted in a binding that holds a part.
    fn place(&self, e: &Expr) -> Option<(usize, bool)> {
        match &e.kind {
            ExprKind::Local(v) => self.held.get(v).copied(),
            ExprKind::Field(base, _) | ExprKind::TupleField(base, _) => {
                self.place(base).map(|(p, _)| (p, true))
            }
            _ => None,
        }
    }

    /// The bindings of `p`, which matches `value`, as parts of what `value` is a part of.
    fn matched(&mut self, p: &Pat, value: &Expr) {
        let Some((param, strict)) = self.place(value) else {
            return;
        };
        binders(p, 0, &mut |v, depth| {
            if let Some(depth) = depth {
                self.held.insert(v, (param, strict || depth > 0));
            }
        });
    }

    fn stmt(&mut self, s: &Stmt) {
        if let StmtKind::Let(b) = &s.kind {
            self.matched(&b.pattern, &b.value);
        }
    }

    fn expr(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Match(scrutinee, arms) => {
                for a in arms {
                    self.matched(&a.pattern, scrutinee);
                }
            }
            ExprKind::IfLet(p, scrutinee, ..) => self.matched(p, scrutinee),
            _ => {}
        }
    }

    /// The parameters, by their places, of which each argument of a call of the function to
    /// itself holds a strict part.
    pub(super) fn strict(&self, args: &[&Expr]) -> Vec<bool> {
        (0..self.params)
            .map(|i| {
                args.get(i)
                    .and_then(|a| self.place(a))
                    .is_some_and(|(p, strict)| p == i && strict)
            })
            .collect()
    }

    /// Every parameter: what a call of the function to itself whose arguments are unknown
    /// leaves, none of them.
    pub(super) fn none(&self) -> Vec<bool> {
        vec![false; self.params]
    }
}

/// What the calls of a function to itself have passed so far: for each parameter, whether
/// every call passed a strict part of it.
#[derive(Debug)]
pub(super) struct Descent {
    every: Vec<bool>,
    called: bool,
}

impl Descent {
    pub(super) fn new(params: usize) -> Self {
        Self {
            every: vec![true; params],
            called: false,
        }
    }

    /// One more call, which passes a strict part of each parameter that `strict` marks.
    pub(super) fn call(&mut self, strict: &[bool]) {
        self.called = true;
        for (all, s) in self.every.iter_mut().zip(strict) {
            *all &= *s;
        }
    }

    /// Whether every call passed a strict part of one parameter. A function that never calls
    /// itself descends.
    pub(super) fn descends(&self) -> bool {
        !self.called || self.every.iter().any(|d| *d)
    }
}
