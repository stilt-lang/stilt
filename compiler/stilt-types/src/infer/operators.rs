//! Operators, and the types they are defined on (numbers.division-and-remainder,
//! numbers.bitwise-operators and numbers.comparisons).

use stilt_diag::{Edit, Fix, codes};
use stilt_hir::decls::prelude_item;
use stilt_hir::hir::{self, BinaryOp};
use stilt_syntax::{TextRange, TextSize};

use super::{Cx, Rule, State, node};
use crate::tast::{self, ExprKind};
use crate::ty::{Kind, Ty};

impl State<'_> {
    /// Whether a type supports an operator (numbers.division-and-remainder,
    /// numbers.bitwise-operators and numbers.comparisons), or `None` while the type is still open.
    pub(super) fn supports(&self, ty: &Ty, rule: Rule) -> Option<bool> {
        let t = &self.table.shape(ty);
        Some(match (t, rule) {
            (Ty::Var(_), _) => return None,
            (Ty::Error, _) => true,
            (t, _) if *t == Ty::never() => true,
            (t, Rule::Numeric) => t.numeric_name().is_some(),
            (t, Rule::Integer) => t.integer_name().is_some(),
            (t, Rule::Negatable) => t.numeric_name().is_some_and(|n| !n.starts_with('u')),
            (t, Rule::BoolOrInteger) => *t == Ty::bool() || t.integer_name().is_some(),
        })
    }

    pub(super) fn unsupported(&mut self, ty: &Ty, rule: Rule, at: TextRange) {
        let hint = if *self.table.resolve(ty) == Ty::str() && rule == Rule::Numeric {
            "; build strings with interpolation, as in \"{a}{b}\""
        } else if self.optional(ty, rule) {
            "; it may be `None`: give that case a value first, as in `(x else 0)`"
        } else {
            ""
        };
        let message = format!("this operator isn't defined on `{}`{hint}", self.show(ty));
        self.error(codes::E0317, at, message);
    }

    /// Whether `ty` is an `Option` of a type that supports the operator, as a conversion that
    /// can fail gives one (expressions.option-fallback).
    fn optional(&self, ty: &Ty, rule: Rule) -> bool {
        let t = self.table.shape(ty);
        matches!(&t, Ty::Con(_, args) if t.is_prelude("Option")
            && args.len() == 1 && self.supports(&args[0], rule) == Some(true))
    }

    /// The type of an operator's result, which is the type `ty` of its operands. An operator that
    /// `ty` doesn't support is an error, and its result then has the error type
    /// (errors.error-type). While `ty` is open, the check waits for the end of the body.
    pub(super) fn operator(&mut self, ty: &Ty, rule: Rule, at: TextRange) -> Ty {
        match self.supports(ty, rule) {
            Some(true) => ty.clone(),
            Some(false) => {
                self.unsupported(ty, rule, at);
                Ty::Error
            }
            None => {
                self.operators.push((ty.clone(), rule, at));
                ty.clone()
            }
        }
    }

    /// The right operand, and the operands' one type, which is unknown when they disagree. A
    /// left operand of type `Never` converts to the right one's (declarations.never).
    fn operands(&mut self, cx: &mut Cx, x: &tast::Expr, b: &hir::Expr) -> (tast::Expr, Option<Ty>) {
        if self.is_never(&x.ty) {
            let y = self.infer(cx, None, b);
            let ty = y.ty.clone();
            (y, Some(ty))
        } else {
            let (y, same) = self.check_fits(cx, &x.ty, b);
            (y, same.then(|| x.ty.clone()))
        }
    }

    pub(super) fn not_an_amount(&mut self, ty: &Ty, at: TextRange) {
        let message = format!(
            "expected an integer type for the shift amount, found `{}`",
            self.show(ty)
        );
        self.error(codes::E0311, at, message);
    }

    /// A shift amount, checked with no expected type, must be an integer (numbers.shift-amounts).
    /// While its type is open, the check waits for the end of the body, where an open literal
    /// has its default type.
    fn amount(&mut self, cx: &mut Cx, b: &hir::Expr) -> tast::Expr {
        let y = self.infer(cx, None, b);
        match self.supports(&y.ty, Rule::Integer) {
            Some(false) => self.not_an_amount(&y.ty, b.at),
            None => self.amounts.push((y.ty.clone(), b.at)),
            Some(true) => {}
        }
        y
    }

    /// The amount by which a place of type `ty` is shifted, or the value that a place of a type
    /// that no shift is defined on is assigned, checked alone.
    pub(super) fn amount_of(&mut self, cx: &mut Cx, ty: &Ty, b: &hir::Expr) -> tast::Expr {
        if self.supports(ty, Rule::Integer) == Some(false) {
            self.infer(cx, None, b)
        } else {
            self.amount(cx, b)
        }
    }

    /// A shift's result has the type of its left operand, which an amount of any integer type
    /// shifts (numbers.shifts).
    fn shift(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        op: BinaryOp,
        x: tast::Expr,
        b: &hir::Expr,
    ) -> tast::Expr {
        let (y, ty) = if self.supports(&x.ty, Rule::Integer) == Some(false) {
            self.unsupported(&x.ty, Rule::Integer, at);
            (self.infer(cx, None, b), Ty::Error)
        } else {
            let y = self.amount(cx, b);
            let ty = self.operator(&x.ty, Rule::Integer, at);
            (y, ty)
        };
        node(ExprKind::Binary(op, Box::new(x), Box::new(y)), ty, at)
    }

    /// The operands of a binary operator have one type (numbers.no-implicit-conversions and
    /// numbers.comparisons), but for a shift's.
    pub(super) fn binary(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        op: BinaryOp,
        a: &hir::Expr,
        b: &hir::Expr,
    ) -> tast::Expr {
        let x = self.infer(cx, None, a);
        let binary = |x, y, ty| node(ExprKind::Binary(op, Box::new(x), Box::new(y)), ty, at);
        match op {
            BinaryOp::And | BinaryOp::Or => {
                self.subsume(a.at, &Ty::bool(), &x.ty);
                let y = self.check(cx, &Ty::bool(), b);
                binary(x, y, Ty::bool())
            }
            BinaryOp::Eq
            | BinaryOp::Ne
            | BinaryOp::Lt
            | BinaryOp::Le
            | BinaryOp::Gt
            | BinaryOp::Ge => {
                let (y, ty) = self.operands(cx, &x, b);
                let trait_name = if matches!(op, BinaryOp::Eq | BinaryOp::Ne) {
                    "Eq"
                } else {
                    "Ord"
                };
                if let Some(ty) = ty {
                    self.obligation(&ty, prelude_item(trait_name), at);
                }
                binary(x, y, Ty::bool())
            }
            BinaryOp::Shl | BinaryOp::Shr => self.shift(cx, at, op, x, b),
            _ => {
                let rule = match op {
                    BinaryOp::Add
                    | BinaryOp::Sub
                    | BinaryOp::Mul
                    | BinaryOp::Div
                    | BinaryOp::Rem => Rule::Numeric,
                    _ => Rule::Integer,
                };
                // expressions.left-operand-first: an operator that the left operand's known type
                // doesn't support is the error, and the right operand is checked alone.
                if self.supports(&x.ty, rule) == Some(false) {
                    let reported = self.errors.len();
                    self.unsupported(&x.ty, rule, at);
                    let y = self.infer(cx, None, b);
                    let added = binary(x, y, Ty::Error);
                    if op == BinaryOp::Add {
                        self.errors[reported].fixes =
                            self.interpolation(&added).into_iter().collect();
                    }
                    return added;
                }
                let (y, ty) = self.operands(cx, &x, b);
                if ty.is_none() {
                    self.offer_conversion(b.at, a, (&x.ty, &y.ty));
                }
                let ty = ty.map_or(Ty::Error, |ty| self.operator(&ty, rule, at));
                let done = binary(x, y, ty);
                // The `+` of a string that starts a chain of them is fixed with the whole chain.
                if let Some(i) = self.chain_start(&done) {
                    self.errors[i].fixes = self.interpolation(&done).into_iter().collect();
                }
                done
            }
        }
    }
}

impl State<'_> {
    /// The error of the `+` of a string that starts the chain of `+` that `chain` ends, if it
    /// is the chain's leftmost and its fix still holds.
    fn chain_start(&self, chain: &tast::Expr) -> Option<usize> {
        let ExprKind::Binary(BinaryOp::Add, first, _) = &chain.kind else {
            return None;
        };
        let mut first: &tast::Expr = first;
        if !matches!(first.kind, ExprKind::Binary(BinaryOp::Add, ..)) {
            return None;
        }
        while let ExprKind::Binary(BinaryOp::Add, l, _) = &first.kind
            && matches!(l.kind, ExprKind::Binary(BinaryOp::Add, ..))
        {
            first = l;
        }
        self.errors
            .iter()
            .rposition(|d| d.code == codes::E0317 && d.range == first.at && !d.fixes.is_empty())
    }

    /// The fix that writes a chain of `+` whose first operand is a string as one interpolated
    /// string, the operands that aren't string literals spliced into it (lexical.interpolation).
    /// The other operands are strings, numbers or `bool`s, which every type can show, and are
    /// names, fields, elements, calls or literals, which a splice holds as they are written.
    fn interpolation(&self, chain: &tast::Expr) -> Option<Fix> {
        let mut operands = Vec::new();
        let mut e = chain;
        while let ExprKind::Binary(BinaryOp::Add, l, r) = &e.kind {
            // An operand in parentheses doesn't start or end where its operation does.
            if l.at.start() != e.at.start() || r.at.end() != e.at.end() {
                return None;
            }
            operands.push(&**r);
            e = l;
        }
        operands.push(e);
        operands.reverse();
        // A number whose literal hasn't taken its type yet shows as any number does.
        let literal_number = |t: &Ty| {
            matches!(
                self.table.unsolved(t).map(|v| v.kind),
                Some(Kind::IntLiteral | Kind::FloatLiteral)
            )
        };
        let shown = |t: &Ty| {
            let t = &self.table.shape(t);
            *t == Ty::str() || *t == Ty::bool() || t.numeric_name().is_some() || literal_number(t)
        };
        if *self.table.resolve(&operands[0].ty) != Ty::str()
            || !operands.iter().all(|o| shown(&o.ty) && spliced(o))
        {
            return None;
        }
        let literal =
            |o: &tast::Expr| matches!(o.kind, ExprKind::Str(_) | ExprKind::Interpolated(_));
        let quote = TextSize::from(1);
        let mut edits = Vec::new();
        if !literal(operands[0]) {
            edits.push(Edit::insert(operands[0].at.start(), "\"{"));
        }
        for pair in operands.windows(2) {
            let (l, r) = (pair[0], pair[1]);
            let from = if literal(l) {
                l.at.end() - quote
            } else {
                l.at.end()
            };
            let to = if literal(r) {
                r.at.start() + quote
            } else {
                r.at.start()
            };
            let close = if literal(l) { "" } else { "}" };
            let open = if literal(r) { "" } else { "{" };
            edits.push(Edit::replace(
                TextRange::new(from, to),
                format!("{close}{open}"),
            ));
        }
        let last = operands[operands.len() - 1];
        if !literal(last) {
            edits.push(Edit::insert(last.at.end(), "}\""));
        }
        Some(Fix::new("build the string with interpolation", edits))
    }
}

/// Whether a splice holds the operand as it is written: one that has no `:` outside brackets,
/// which would start a format spec, and no newline (lexical.interpolation).
fn spliced(o: &tast::Expr) -> bool {
    matches!(
        o.kind,
        ExprKind::Str(_)
            | ExprKind::Interpolated(_)
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Bool(_)
            | ExprKind::Local(_)
            | ExprKind::Constant(_)
            | ExprKind::ValueParam(_)
            | ExprKind::Field(..)
            | ExprKind::TupleField(..)
            | ExprKind::Index(..)
            | ExprKind::Call(..)
            | ExprKind::Project(..)
            | ExprKind::CallValue(..)
    )
}
