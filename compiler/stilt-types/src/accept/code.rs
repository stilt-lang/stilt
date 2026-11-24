//! The words of facts.rules-of-acceptance that read code alone: places, what a test compares and
//! the facts each test gives, the keys of facts.keys, the literals and constants of facts.terms,
//! and the code that can't complete.

use std::collections::BTreeSet;

use stilt_hir::hir::{BinaryOp, LocalId, Name, UnaryOp};

use super::Context;
use crate::tast::{Block, Callee, Expr, ExprKind, StmtKind};
use crate::ty::Ty;

/// A place (facts.acceptance-places): a binding's name with any fields after it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Place {
    pub(super) root: LocalId,
    pub(super) fields: Vec<Name>,
}

/// What one side of a test's comparison is: a binding, a literal or a constant of facts.terms by
/// its number, the length of a place, or anything else.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Term {
    Name(LocalId),
    Num(i128),
    Len(Place),
    Other,
}

/// A key of facts.keys: a binding, or a literal that doesn't interpolate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum KeyTerm {
    Name(LocalId),
    Int(i128),
    Str(String),
    Bool(bool),
}

/// A comparison's operator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Cmp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

impl Cmp {
    fn of(op: BinaryOp) -> Option<Self> {
        Some(match op {
            BinaryOp::Lt => Cmp::Lt,
            BinaryOp::Le => Cmp::Le,
            BinaryOp::Gt => Cmp::Gt,
            BinaryOp::Ge => Cmp::Ge,
            BinaryOp::Eq => Cmp::Eq,
            BinaryOp::Ne => Cmp::Ne,
            _ => return None,
        })
    }

    /// What the comparison's negation compares.
    fn negated(self) -> Self {
        match self {
            Cmp::Lt => Cmp::Ge,
            Cmp::Le => Cmp::Gt,
            Cmp::Gt => Cmp::Le,
            Cmp::Ge => Cmp::Lt,
            Cmp::Eq => Cmp::Ne,
            Cmp::Ne => Cmp::Eq,
        }
    }

    /// The operator with its sides swapped, as `0 <= i` for `i >= 0`.
    pub(super) fn mirrored(self) -> Self {
        match self {
            Cmp::Lt => Cmp::Gt,
            Cmp::Le => Cmp::Ge,
            Cmp::Gt => Cmp::Lt,
            Cmp::Ge => Cmp::Le,
            other => other,
        }
    }
}

/// A fact that a test gives the code it guards (facts.guarding-tests).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Atom {
    Cmp(Term, Cmp, Term),
    /// `!P.is_empty()`, which gives `0 < P.len()` (facts.guards).
    NonEmpty(Place),
    /// `m.contains(k)`, or a store of `k` into `m` (facts.keys).
    Contains(Place, KeyTerm),
}

impl Atom {
    /// Whether the fact compares `a` and `b` by `op`, written either way round.
    pub(super) fn compares(&self, left: &Term, op: Cmp, right: &Term) -> bool {
        match self {
            Atom::Cmp(l, o, r) => {
                (l == left && *o == op && r == right)
                    || (l == right && *o == op.mirrored() && r == left)
            }
            _ => false,
        }
    }
}

/// What the rules read of code alone: the constants of facts.terms and the bindings of `when`s.
pub(super) struct Reader<'r> {
    pub(super) cx: &'r Context<'r>,
    pub(super) whens: &'r BTreeSet<LocalId>,
}

impl Reader<'_> {
    /// The place an expression is, if it is one (facts.acceptance-places).
    pub(super) fn place(&self, e: &Expr) -> Option<Place> {
        match &e.kind {
            ExprKind::Local(v) if !self.whens.contains(v) => Some(Place {
                root: *v,
                fields: Vec::new(),
            }),
            ExprKind::Field(base, name) => {
                let mut p = self.place(base)?;
                p.fields.push(*name);
                Some(p)
            }
            _ => None,
        }
    }

    /// The binding an expression names, if it names one that no `when` binds.
    pub(super) fn binding(&self, e: &Expr) -> Option<LocalId> {
        match &e.kind {
            ExprKind::Local(v) if !self.whens.contains(v) => Some(*v),
            _ => None,
        }
    }

    /// The integer binding an expression names, if it names one that no `when` binds.
    pub(super) fn name(&self, e: &Expr) -> Option<LocalId> {
        self.binding(e).filter(|_| e.ty.integer_name().is_some())
    }

    /// The number of an integer literal, with or without a `-`, or of a constant of facts.terms.
    pub(super) fn number(&self, e: &Expr) -> Option<i128> {
        e.ty.integer_name()?;
        match &e.kind {
            ExprKind::Int(text) => literal(text),
            ExprKind::Unary(UnaryOp::Neg, x) => match &x.kind {
                ExprKind::Int(text) => literal(text).map(|n| -n),
                _ => None,
            },
            ExprKind::Constant(item) => (self.cx.literal)(item, None),
            ExprKind::MemberConstant(item, name, _) => (self.cx.literal)(item, Some(*name)),
            _ => None,
        }
    }

    /// The place whose length an expression is, as `P.len()`.
    pub(super) fn len_of(&self, e: &Expr) -> Option<Place> {
        match &e.kind {
            ExprKind::Call(c, _, args, _) if method(c) == Some("len") && args.len() == 1 => {
                self.place(&args[0].value)
            }
            _ => None,
        }
    }

    /// What one side of a comparison is.
    pub(super) fn term(&self, e: &Expr) -> Term {
        if let Some(v) = self.name(e) {
            Term::Name(v)
        } else if let Some(n) = self.number(e) {
            Term::Num(n)
        } else if let Some(p) = self.len_of(e) {
            Term::Len(p)
        } else {
            Term::Other
        }
    }

    /// The key an expression is (facts.keys): a binding, or a literal that doesn't interpolate.
    pub(super) fn key(&self, e: &Expr) -> Option<KeyTerm> {
        match &e.kind {
            ExprKind::Local(v) if !self.whens.contains(v) => Some(KeyTerm::Name(*v)),
            ExprKind::Int(text) => literal(text).map(KeyTerm::Int),
            ExprKind::Str(s) => Some(KeyTerm::Str(s.clone())),
            ExprKind::Bool(b) => Some(KeyTerm::Bool(*b)),
            _ => None,
        }
    }

    /// `m.contains(k)`, as the map's place and the key.
    pub(super) fn contains(&self, e: &Expr) -> Option<(Place, KeyTerm)> {
        match &e.kind {
            ExprKind::Call(c, _, args, _) if is_map_method(c, "contains") && args.len() == 2 => {
                Some((self.place(&args[0].value)?, self.key(&args[1].value)?))
            }
            _ => None,
        }
    }

    /// The facts a condition gives where it is true, or where it is false (facts.guarding-tests):
    /// each conjunct of its `&&` chain, and for its negation each disjunct's of its `||` chain,
    /// read through `!`.
    pub(super) fn gives(&self, c: &Expr, positive: bool, out: &mut Vec<Atom>) {
        match &c.kind {
            ExprKind::Binary(BinaryOp::And, a, b) if positive => {
                self.gives(a, true, out);
                self.gives(b, true, out);
            }
            ExprKind::Binary(BinaryOp::Or, a, b) if !positive => {
                self.gives(a, false, out);
                self.gives(b, false, out);
            }
            ExprKind::Unary(UnaryOp::Not, a) => self.gives(a, !positive, out),
            ExprKind::Binary(op, a, b) => {
                if let Some(op) = Cmp::of(*op) {
                    let op = if positive { op } else { op.negated() };
                    out.push(Atom::Cmp(self.term(a), op, self.term(b)));
                }
            }
            ExprKind::Call(callee, _, args, _) => {
                if method(callee) == Some("is_empty") && args.len() == 1 && !positive {
                    out.extend(self.place(&args[0].value).map(Atom::NonEmpty));
                } else if positive {
                    out.extend(self.contains(c).map(|(m, k)| Atom::Contains(m, k)));
                }
            }
            _ => {}
        }
    }

    /// The store of a key that a statement is, `m[k] = v` or `m.insert(k, v)` (facts.keys).
    pub(super) fn stored(&self, s: &crate::tast::Stmt) -> Option<(Place, KeyTerm)> {
        match &s.kind {
            StmtKind::Assign(None, place, _) => match &place.kind {
                ExprKind::Index(m, k) if is_map(&m.ty) => Some((self.place(m)?, self.key(k)?)),
                _ => None,
            },
            StmtKind::Expr(e) => match &e.kind {
                ExprKind::Call(c, _, args, _) if is_map_method(c, "insert") && args.len() == 3 => {
                    Some((self.place(&args[0].value)?, self.key(&args[1].value)?))
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// The key that an `if !m.contains(k) { …; m[k] = v }` statement stores (facts.keys).
    pub(super) fn stored_if_missing(&self, s: &crate::tast::Stmt) -> Option<(Place, KeyTerm)> {
        let StmtKind::Expr(e) = &s.kind else {
            return None;
        };
        let ExprKind::If(c, then, _) = &e.kind else {
            return None;
        };
        let ExprKind::Unary(UnaryOp::Not, inner) = &c.kind else {
            return None;
        };
        let tested = self.contains(inner)?;
        (self.stored(then.last()?)? == tested).then_some(tested)
    }
}

/// The name of the method a callee is, if it is one.
pub(super) fn method(c: &Callee) -> Option<&str> {
    match c {
        Callee::Member(_, name) | Callee::TraitMethod(_, name, _) => Some(name),
        _ => None,
    }
}

/// Whether a callee is the prelude's `Map` method `name`.
pub(super) fn is_map_method(c: &Callee, name: &str) -> bool {
    matches!(c, Callee::Member(owner, n) if crate::ty::is_prelude(owner, "Map") && &**n == name)
}

pub(super) fn is_map(ty: &Ty) -> bool {
    ty.is_prelude("Map")
}

/// Whether a type is a list's or an array's.
pub(super) fn is_sequence(ty: &Ty) -> bool {
    ty.is_prelude("List") || ty.arrayed().is_some()
}

/// The value of an integer literal's text, its `-` included.
pub(super) fn literal(text: &str) -> Option<i128> {
    let text = text.replace('_', "");
    match text.strip_prefix('-') {
        Some(rest) => stilt_hir::values::int_literal(rest.trim(), true),
        None => stilt_hir::values::int_literal(&text, false),
    }
}

/// Whether a block can't complete: each of its paths ends in `return`, `break`, `continue`,
/// `raise` or a call of type `Never` (facts.rules-of-acceptance).
pub(super) fn ends_block(b: &Block) -> bool {
    matches!(b.last().map(|s| &s.kind), Some(StmtKind::Expr(e)) if ends(e))
}

fn ends(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Return(_) | ExprKind::Raise(_) | ExprKind::Break | ExprKind::Continue => true,
        ExprKind::Call(..) | ExprKind::CallValue(..) | ExprKind::Project(..) => e.ty == Ty::never(),
        ExprKind::Block(b) => ends_block(b),
        ExprKind::If(_, then, Some(alt)) | ExprKind::IfLet(_, _, then, Some(alt)) => {
            ends_block(then) && ends(alt)
        }
        ExprKind::Match(_, arms) => !arms.is_empty() && arms.iter().all(|a| ends(&a.body)),
        _ => false,
    }
}
