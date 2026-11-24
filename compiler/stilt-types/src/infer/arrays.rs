//! Arrays (generics.array-literals and generics.array-patterns): a list literal where an `Array<T,
//! n>` is expected, and a list pattern matched against one.
//!
//! An array's size is compared while the program is checked: a size that a value parameter gives is
//! equal only to itself (generics.equal-types), so only a literal's own length, or a pattern's, can
//! meet a size that a value argument or inference gives.

use stilt_diag::codes;
use stilt_hir::hir::{self, ListRest, Value};
use stilt_syntax::TextRange;

use super::exprs::is_spread;
use super::{Cx, State, error_node, node};
use crate::tast;
use crate::ty::Ty;

/// What an array's size is known to be where it is checked.
enum Size {
    /// A value, as a value argument or inference gives it.
    Known(i128),
    /// A value parameter, equal only to itself.
    Param(String),
    /// A size that inference hasn't found yet.
    Open,
    /// The error type.
    Error,
}

impl State<'_> {
    /// The element type and the size of an `Array<T, n>`, if `t` is one.
    pub(super) fn array_of(&self, t: &Ty) -> Option<(Ty, Ty)> {
        let t = self.resolved(t);
        t.arrayed().map(|(elem, size)| (elem.clone(), size.clone()))
    }

    fn size(&self, size: &Ty) -> Size {
        match self.resolved(size) {
            Ty::Value(Value::Int(k)) => Size::Known(k),
            Ty::Param(_) => Size::Param(self.show(size)),
            Ty::Var(_) => Size::Open,
            _ => Size::Error,
        }
    }

    /// A list literal whose expected type is `Array<elem, size>`, `expected`
    /// (generics.array-literals): each element of type `elem`, exactly as many as the size, or
    /// E0311 at the literal, naming both lengths; a spread among them is E0311 at the spread.
    pub(super) fn array_literal(
        &mut self,
        cx: &mut Cx,
        (at, expected): (TextRange, &Ty),
        (elem, size): (Ty, Ty),
        es: &[hir::Expr],
    ) -> tast::Expr {
        if let Some(spread) = es.iter().find(|e| is_spread(e)) {
            for e in es {
                match &e.kind {
                    hir::ExprKind::Spread(inner) => self.abandon(cx, inner),
                    _ => self.abandon(cx, e),
                };
            }
            let message = format!(
                "expected `{}`, found a spread among the elements, whose length is known only at \
                 run time",
                self.show(expected)
            );
            self.error(codes::E0311, spread.at, message);
            return error_node(at);
        }
        let items: Vec<tast::Expr> = es.iter().map(|e| self.check(cx, &elem, e)).collect();
        let len = i128::try_from(es.len()).unwrap_or(i128::MAX);
        let fits = match self.size(&size) {
            Size::Known(k) => k == len,
            Size::Open => self.table.unify(&size, &Ty::Value(Value::Int(len))),
            Size::Param(_) => false,
            Size::Error => true,
        };
        if !fits {
            let message = format!(
                "expected `{}`, an array of {}, found a list literal of {}",
                self.show(expected),
                self.length(&size),
                elements(len)
            );
            self.error(codes::E0311, at, message);
            return error_node(at);
        }
        node(tast::ExprKind::List(items), expected.clone(), at)
    }

    /// An array's length as a message names it.
    fn length(&self, size: &Ty) -> String {
        match self.size(size) {
            Size::Known(k) => elements(k),
            Size::Param(n) => format!("`{n}` elements, which only `{n}` equals"),
            Size::Open | Size::Error => "some elements".to_owned(),
        }
    }

    /// A list pattern matched against `Array<elem, size>`, `ty` (generics.array-patterns): one of
    /// exactly the size, or with a rest, of at most the size, which binds no name, or E0311.
    pub(super) fn array_pattern(
        &mut self,
        cx: &mut Cx,
        p: &hir::Pat,
        (ty, elem, size): (&Ty, Ty, Ty),
        (ps, rest): (&[hir::Pat], ListRest),
    ) -> tast::PatKind {
        self.array_patterns.insert(p.at, elem.clone());
        let len = i128::try_from(ps.len()).unwrap_or(i128::MAX);
        let exact = rest == ListRest::Exact;
        let fits = match (self.size(&size), rest) {
            (_, ListRest::Bind(_)) => false,
            (Size::Error, _) => true,
            (Size::Known(k), _) => len == k || (!exact && len <= k),
            (Size::Open, ListRest::Exact) => self.table.unify(&size, &Ty::Value(Value::Int(len))),
            (Size::Param(_), ListRest::Rest) => len == 0,
            (Size::Open | Size::Param(_), _) => false,
        };
        if !fits {
            self.mismatched_pattern(p, ty, &size, (len, rest));
            for q in ps {
                self.pattern(cx, q, &Ty::Error);
            }
            return tast::PatKind::Error;
        }
        let items = ps.iter().map(|q| self.pattern(cx, q, &elem)).collect();
        tast::PatKind::List(items, rest)
    }

    /// E0311 for a list pattern whose length doesn't fit an array's size, or whose rest binds a
    /// name, whose length would be arithmetic.
    fn mismatched_pattern(
        &mut self,
        p: &hir::Pat,
        ty: &Ty,
        size: &Ty,
        (len, rest): (i128, ListRest),
    ) {
        let message = match rest {
            ListRest::Bind(_) => format!(
                "a rest that binds a name can't match `{}`: its length would be the array's size \
                 less {len}, which no type writes; write `..` alone",
                self.show(ty)
            ),
            ListRest::Rest => format!(
                "expected `{}`, an array of {}, found a list pattern of at least {}",
                self.show(ty),
                self.length(size),
                elements(len)
            ),
            ListRest::Exact => format!(
                "expected `{}`, an array of {}, found a list pattern of {}",
                self.show(ty),
                self.length(size),
                elements(len)
            ),
        };
        self.error(codes::E0311, p.at, message);
    }
}

/// A number of elements, as messages write it.
fn elements(n: i128) -> String {
    if n == 1 {
        "1 element".to_owned()
    } else {
        format!("{n} elements")
    }
}
