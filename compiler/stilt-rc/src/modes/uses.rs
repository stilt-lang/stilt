//! The uses that `once` reads (modes.once-closures and modes.once-parameters): each use of each
//! local, and each closure literal, with how the code around it uses its value and how many loops
//! and closure literals hold it.

use std::collections::HashMap;

use stilt_hir::hir::{LocalId, Mode};
use stilt_mir::FnRef;
use stilt_syntax::TextRange;
use stilt_types::tast::walk::{self, Part};
use stilt_types::tast::{Block, Callee, Code, Expr, ExprKind, Iterable, PatKind, StmtKind};
use stilt_types::ty::Ty;

/// How the code around a value uses it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Use {
    /// It calls it, as the callee of a call through a value.
    Called,
    /// It passes it as a `let` argument, at this place among the arguments, a receiver first,
    /// to a call that names this function.
    Passed(FnRef, usize),
    /// Any other way.
    Other,
}

/// A use of a local.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Seen {
    pub(crate) at: TextRange,
    /// How many loops and closure literals hold it.
    pub(crate) depth: u32,
    pub(crate) how: Use,
    /// Whether its type is a function type.
    pub(crate) function: bool,
}

/// The uses of a body's locals and closure literals, in the order they are written.
#[derive(Debug, Default)]
pub(crate) struct Uses {
    pub(crate) locals: HashMap<LocalId, Vec<Seen>>,
    /// Each closure literal that a `let` binds to a variable: the variable, the literal, and how
    /// many loops and closure literals hold the `let`.
    pub(crate) bound: Vec<(LocalId, TextRange, u32)>,
    /// Each other closure literal, with how the code around it uses it.
    pub(crate) unbound: Vec<(TextRange, Use)>,
}

/// The uses of a body's code, where `callee` names the function a call by name calls.
pub(crate) fn uses(code: &Code, callee: &dyn Fn(&Callee) -> Option<FnRef>) -> Uses {
    let mut walk = Walk {
        callee,
        depth: 0,
        found: Uses::default(),
    };
    match code {
        Code::Block(b) => walk.block(b),
        Code::Expr(e) => walk.expr(e, Use::Other),
    }
    walk.found
}

struct Walk<'a> {
    callee: &'a dyn Fn(&Callee) -> Option<FnRef>,
    depth: u32,
    found: Uses,
}

impl Walk<'_> {
    fn expr(&mut self, e: &Expr, how: Use) {
        match &e.kind {
            ExprKind::Local(v) => {
                let seen = Seen {
                    at: e.at,
                    depth: self.depth,
                    how,
                    function: matches!(e.ty, Ty::Fn(_)),
                };
                self.found.locals.entry(*v).or_default().push(seen);
            }
            ExprKind::Closure(_, body) => {
                self.found.unbound.push((e.at, how));
                self.nested(|w| w.expr(body, Use::Other));
            }
            // An instantiation is used as the value it instantiates (polymorphism.instantiation).
            ExprKind::Instantiate(value, _) => self.expr(value, how),
            ExprKind::CallValue(f, args) => {
                self.expr(f, Use::Called);
                for a in args {
                    self.expr(&a.value, Use::Other);
                }
            }
            ExprKind::Call(callee, _, args, _) | ExprKind::Project(callee, _, args, _) => {
                let g = (self.callee)(callee);
                for (i, a) in args.iter().enumerate() {
                    let how = match &g {
                        Some(g) if a.mode == Mode::Let => Use::Passed(g.clone(), i),
                        _ => Use::Other,
                    };
                    self.expr(&a.value, how);
                }
            }
            ExprKind::Loop(b) => self.nested(|w| w.block(b)),
            ExprKind::While(c, b) => self.nested(|w| {
                w.expr(c, Use::Other);
                w.block(b);
            }),
            ExprKind::For(_, iterable, b) => {
                match &**iterable {
                    Iterable::Iter(source) => self.expr(source, Use::Other),
                    Iterable::Range(from, to, _) => {
                        self.expr(from, Use::Other);
                        self.expr(to, Use::Other);
                    }
                }
                self.nested(|w| w.block(b));
            }
            _ => {
                for part in walk::parts(e) {
                    match part {
                        Part::Expr(x) => self.expr(x, Use::Other),
                        Part::Block(b) => self.block(b),
                    }
                }
            }
        }
    }

    /// Walks code that a loop or a closure literal holds.
    fn nested(&mut self, f: impl FnOnce(&mut Self)) {
        self.depth += 1;
        f(self);
        self.depth -= 1;
    }

    fn block(&mut self, b: &Block) {
        for s in b {
            match &s.kind {
                StmtKind::Let(binding) => match (&binding.pattern.kind, &binding.value.kind) {
                    (PatKind::Bind(v), ExprKind::Closure(_, body)) => {
                        let found = (*v, binding.value.at, self.depth);
                        self.found.bound.push(found);
                        self.nested(|w| w.expr(body, Use::Other));
                        if let Some(otherwise) = &binding.otherwise {
                            self.expr(otherwise, Use::Other);
                        }
                    }
                    _ => {
                        for e in walk::stmt_exprs(s) {
                            self.expr(e, Use::Other);
                        }
                    }
                },
                _ => {
                    for e in walk::stmt_exprs(s) {
                        self.expr(e, Use::Other);
                    }
                }
            }
        }
    }
}
