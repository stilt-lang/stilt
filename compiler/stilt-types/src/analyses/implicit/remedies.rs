//! The rewrites that keep an operation from panicking, offered as fixes when a `without panic`
//! rules the operation out (effects.panicking-operations and effects.without-panic): an index read
//! with `get`, whose `None` takes a fallback, and an `assert` that raises instead, in a function
//! that raises a `str`. A division has none, since a division by anything but a nonzero literal can
//! panic however the divisor is tested first, and a hole has none, since only the code still to be
//! written replaces it.

use std::cell::RefCell;

use stilt_diag::{Edit, Fix};
use stilt_hir::hir::{BinaryOp, Mode};
use stilt_syntax::{TextRange, TextSize};

use crate::tast::{Expr, ExprKind, PatKind, Segment, Stmt, StmtKind};
use crate::ty::Ty;

/// A rewrite of an operation that keeps it from panicking.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Remedy {
    /// An index read `a[k]` of a list or a map, which starts at `start`, read with `get`
    /// instead, with `fallback` where `get` gives `None`. `open` runs from the end of `a` to the
    /// start of `k`, and `close` from the end of `k` to the end of the index. `parens` tells
    /// whether the index stands where an `else` needs parentheses.
    Get {
        start: TextSize,
        open: TextRange,
        close: TextRange,
        fallback: &'static str,
        map: bool,
        parens: bool,
    },
    /// An `assert c` of the function's own body, which raises a `str` instead. `keyword` runs
    /// from `assert` to the start of `c`, and `negation` says how to write the opposite of `c`.
    Raise {
        keyword: TextRange,
        condition: TextRange,
        negation: Negation,
    },
}

/// How the opposite of a condition is written.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Negation {
    /// `!c`, for a condition that `!` applies to as it is.
    Not,
    /// `!(c)`.
    NotParenthesized,
    /// The comparison with its operator, which runs over the span, replaced by the opposite
    /// one, as `a > b` is the opposite of `a <= b`. A comparison of floats has none, since
    /// both are false when one side is NaN.
    Opposite(TextRange, &'static str),
}

impl Remedy {
    /// The fix that applies the rewrite, given whether the function's row raises a `str`,
    /// which an `assert` needs to raise instead.
    pub(crate) fn fix(&self, raises_str: bool) -> Option<Fix> {
        match *self {
            Remedy::Get {
                start,
                open,
                close,
                fallback,
                map,
                parens,
            } => {
                let missing = if map {
                    "a missing key"
                } else {
                    "an index out of range"
                };
                let close_paren = if parens { ")" } else { "" };
                let mut edits = vec![
                    Edit::replace(open, ".get("),
                    Edit::replace(close, format!(") else {fallback}{close_paren}")),
                ];
                if parens {
                    edits.insert(0, Edit::insert(start, "("));
                }
                Some(Fix::new(
                    format!("use `get`, with `{fallback}` for {missing}"),
                    edits,
                ))
            }
            Remedy::Raise {
                keyword,
                condition,
                negation,
            } if raises_str => Some(raise(keyword, condition, negation)),
            Remedy::Raise { .. } => None,
        }
    }
}

/// The fix that turns `assert c` into `if` the opposite of `c`, with a block that raises.
fn raise(keyword: TextRange, condition: TextRange, negation: Negation) -> Fix {
    let block = " { raise \"assertion failed\" }";
    let edits = match negation {
        Negation::Not => vec![
            Edit::replace(keyword, "if !"),
            Edit::insert(condition.end(), block),
        ],
        Negation::NotParenthesized => vec![
            Edit::replace(keyword, "if !("),
            Edit::insert(condition.end(), format!("){block}")),
        ],
        Negation::Opposite(operator, opposite) => vec![
            Edit::replace(keyword, "if "),
            Edit::replace(operator, format!(" {opposite} ")),
            Edit::insert(condition.end(), block),
        ],
    };
    Fix::new("raise an error instead", edits)
}

/// The value that stands for a missing element of type `ty`, where the type has an obvious
/// one: zero, the empty string, `false` or `None`.
fn fallback(ty: &Ty) -> Option<&'static str> {
    if ty.integer_name().is_some() {
        Some("0")
    } else if ty.numeric_name().is_some() {
        Some("0.0")
    } else if ty.is_prelude("str") {
        Some("\"\"")
    } else if ty.is_prelude("bool") {
        Some("false")
    } else if ty.is_prelude("Option") {
        Some("None")
    } else {
        None
    }
}

/// Where the operations of a body stand, as a walk that visits each expression before those
/// inside it finds out: which expressions an `else` may replace without parentheses, which
/// are places written to, and which code is inside a closure.
#[derive(Default)]
pub(super) struct Contexts<'a> {
    /// The expressions whose parent takes any expression in their place.
    loose: RefCell<Vec<&'a Expr>>,
    /// The places that assignments and `inout` arguments write to, and the places they go
    /// through.
    places: RefCell<Vec<&'a Expr>>,
    /// The closures found so far.
    closures: RefCell<Vec<TextRange>>,
}

impl<'a> Contexts<'a> {
    /// Records what a statement says of the expressions directly inside it.
    pub(super) fn stmt(&self, s: &'a Stmt) {
        let mut loose = self.loose.borrow_mut();
        match &s.kind {
            StmtKind::Let(b) | StmtKind::Var(b)
                if b.otherwise.is_none()
                    && matches!(b.pattern.kind, PatKind::Bind(_) | PatKind::Wild) =>
            {
                loose.push(&b.value);
            }
            StmtKind::Let(_) | StmtKind::Var(_) => {}
            StmtKind::Assign(_, place, value) => {
                loose.push(value);
                self.place(place);
            }
            StmtKind::Assert(e) | StmtKind::Expr(e) => loose.push(e),
            StmtKind::Yield(place) => self.place(place),
        }
    }

    /// Records what an expression says of the expressions directly inside it.
    pub(super) fn expr(&self, e: &'a Expr) {
        let mut loose = self.loose.borrow_mut();
        match &e.kind {
            ExprKind::Call(_, _, args, _)
            | ExprKind::Project(_, _, args, _)
            | ExprKind::CallValue(_, args) => {
                for a in args {
                    // A method's receiver is written before the call's name.
                    if a.value.at.start() != e.at.start() {
                        loose.push(&a.value);
                    }
                    if a.mode == Mode::Inout {
                        self.place(&a.value);
                    }
                }
            }
            ExprKind::List(es) | ExprKind::Tuple(es) | ExprKind::Construct(_, _, es) => {
                loose.extend(es);
            }
            ExprKind::Record(_, _, fields) => loose.extend(fields.iter().map(|(_, e)| e)),
            ExprKind::Index(_, k) | ExprKind::Raise(k) | ExprKind::Else(_, k) => loose.push(k),
            ExprKind::Return(Some(v)) => loose.push(v),
            ExprKind::Interpolated(segments) => {
                loose.extend(segments.iter().filter_map(|s| match s {
                    Segment::Splice(e, _) => Some(&**e),
                    Segment::Text(_) => None,
                }));
            }
            ExprKind::Closure(..) => self.closures.borrow_mut().push(e.at),
            _ => {}
        }
    }

    /// Records a place written to, and the places it goes through.
    fn place(&self, place: &'a Expr) {
        self.places.borrow_mut().push(place);
        match &place.kind {
            ExprKind::Field(base, _) | ExprKind::TupleField(base, _) | ExprKind::Index(base, _) => {
                self.place(base);
            }
            _ => {}
        }
    }

    /// The rewrite of the index `e`, of `a` by `k`, when it is read rather than written and its
    /// element has a fallback.
    pub(super) fn index(&self, e: &'a Expr, a: &Expr, k: &Expr, map: bool) -> Option<Remedy> {
        let is = |list: &RefCell<Vec<&'a Expr>>| list.borrow().iter().any(|p| std::ptr::eq(*p, e));
        if is(&self.places) {
            return None;
        }
        Some(Remedy::Get {
            start: e.at.start(),
            open: TextRange::new(a.at.end(), k.at.start()),
            close: TextRange::new(k.at.end(), e.at.end()),
            fallback: fallback(&e.ty)?,
            map,
            parens: !is(&self.loose),
        })
    }

    /// The rewrite of the statement `assert c`, unless it is inside a closure, whose row isn't
    /// the function's.
    pub(super) fn assert(&self, s: &Stmt, c: &Expr) -> Option<Remedy> {
        if self
            .closures
            .borrow()
            .iter()
            .any(|at| at.contains_range(s.at))
        {
            return None;
        }
        Some(Remedy::Raise {
            keyword: TextRange::new(s.at.start(), c.at.start()),
            condition: c.at,
            negation: negation(c),
        })
    }
}

/// How to write the opposite of the condition `c`.
fn negation(c: &Expr) -> Negation {
    match &c.kind {
        ExprKind::Binary(op, a, b) if !is_float(&a.ty) => {
            let opposite = match op {
                BinaryOp::Lt => ">=",
                BinaryOp::Le => ">",
                BinaryOp::Gt => "<=",
                BinaryOp::Ge => "<",
                BinaryOp::Eq => "!=",
                BinaryOp::Ne => "==",
                _ => return Negation::NotParenthesized,
            };
            Negation::Opposite(TextRange::new(a.at.end(), b.at.start()), opposite)
        }
        ExprKind::Bool(_)
        | ExprKind::Local(_)
        | ExprKind::Constant(_)
        | ExprKind::ValueParam(_)
        | ExprKind::Reflect(..)
        | ExprKind::MemberConstant(..)
        | ExprKind::Field(..)
        | ExprKind::TupleField(..)
        | ExprKind::Call(..)
        | ExprKind::Project(..)
        | ExprKind::CallValue(..)
        | ExprKind::Index(..) => Negation::Not,
        _ => Negation::NotParenthesized,
    }
}

/// Whether a type is a float type.
fn is_float(ty: &Ty) -> bool {
    matches!(ty, Ty::Con(item, _) if crate::ty::is_float(item))
}
