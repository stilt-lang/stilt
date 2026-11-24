//! Reflection (meta.shape-and-name and meta.reflects): `T.shape()` and `T.name()` where a module
//! names `std.meta` (meta.shape-and-name), the cases of a shape matched by patterns (meta.shapes),
//! the fresh types of their arms and of loops over fields and cases (meta.fresh-types, meta.fields
//! and meta.variant-cases), and bound tests (meta.bound-tests).

use stilt_diag::codes;
use stilt_hir::hir::{self, Ident, MemberOwner, TraitRef, TypeRef};
use stilt_syntax::TextRange;

use super::members::Found;
use super::{Cx, State, error_node, node};
use crate::tast::{self, Reflection};
use crate::ty::{META, SHAPE_CASES, Ty, case_payload, is_meta, meta_item, meta_ty};

impl State<'_> {
    /// Whether the module names `std.meta`, or is it, where `T.shape()` and `T.name()` reflect
    /// (meta.shape-and-name).
    fn names_meta(&self) -> bool {
        &*self.env.module == META || self.env.imports.iter().any(|m| &**m == META)
    }

    /// What `T.shape` or `T.name` reads of `T`, when it reflects: in a module that names
    /// `std.meta`, and when traits.qualified-calls and traits.shared-member-names find no member of
    /// that name on the type, its own or a visible trait's, or on a type parameter, its bounds'
    /// (meta.shape-and-name). A member that an error leaves out is still the type's
    /// (errors.broken-blocks).
    fn reflection(&mut self, t: &TypeRef, name: &Ident) -> Option<(Reflection, Ty)> {
        let what = match &*name.name {
            "shape" => Reflection::Shape,
            "name" => Reflection::Name,
            _ => return None,
        };
        if !self.names_meta() {
            return None;
        }
        let ty = self.named_type(t);
        let resolved = self.resolved(&ty);
        if resolved == Ty::Error
            || !matches!(self.find_method(&resolved, &name.name), Found::Missing)
            || self.left_out(&resolved, &name.name)
        {
            return None;
        }
        Some((what, ty))
    }

    /// The type of what a reflection reads: a `meta.Shape<T>` or a `str`.
    fn reflected(what: Reflection, ty: &Ty) -> Ty {
        match what {
            Reflection::Shape => meta_ty("Shape", vec![ty.clone()]),
            Reflection::Name => Ty::str(),
        }
    }

    /// `T.shape()` or `T.name()`, if it reflects: a function of no parameters, so a call with
    /// arguments is E0315, and still reads what it reads (traits.qualified-calls).
    pub(super) fn reflect_call(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        owner: &MemberOwner,
        name: &Ident,
        args: &[hir::Arg],
    ) -> Option<tast::Expr> {
        let MemberOwner::Type(t) = owner else {
            return None;
        };
        let (what, ty) = self.reflection(t, name)?;
        if !args.is_empty() {
            self.arguments(cx, at, &[], &[], args);
        }
        let result = Self::reflected(what, &ty);
        Some(node(tast::ExprKind::Reflect(what, ty), result, at))
    }

    /// `T.shape` or `T.name` as a value: a function of no parameters, as `Type.m` is
    /// (traits.qualified-calls), which reads it when called.
    pub(super) fn reflect_value(
        &mut self,
        at: TextRange,
        owner: &MemberOwner,
        name: &Ident,
    ) -> Option<tast::Expr> {
        let MemberOwner::Type(t) = owner else {
            return None;
        };
        let (what, ty) = self.reflection(t, name)?;
        let result = Self::reflected(what, &ty);
        let read = node(tast::ExprKind::Reflect(what, ty), result.clone(), at);
        let fty = Ty::func(Vec::new(), result, crate::ty::Row::EMPTY);
        Some(node(
            tast::ExprKind::Closure(Vec::new(), Box::new(read)),
            fty,
            at,
        ))
    }

    /// A pattern that names a case of a shape, `Int(n)` matched against a `meta.Shape<T>`: its one
    /// payload has the type meta.shapes gives the case, whose fresh types are the arm's
    /// (meta.fresh-types).
    pub(super) fn shape_case(
        &mut self,
        cx: &mut Cx,
        p: &hir::Pat,
        ty: &Ty,
        (n, ps): (&Ident, &[hir::Pat]),
    ) -> Option<tast::PatKind> {
        let t = self.resolved(ty).meta_of("Shape").cloned()?;
        let case = SHAPE_CASES.iter().find(|c| **c == &*n.name)?;
        let mut fresh = |letter| self.fresh_type(letter);
        let payload = case_payload(case, &t, &mut fresh)?;
        if ps.len() != 1 {
            let message = format!(
                "`{case}` has 1 payload field, but the pattern has {}",
                ps.len()
            );
            self.error(codes::E0315, p.at, message);
            for q in ps {
                self.pattern(cx, q, &Ty::Error);
            }
            return Some(tast::PatKind::Error);
        }
        let inner = self.pattern(cx, &ps[0], &payload);
        Some(tast::PatKind::Variant(meta_item(case), vec![inner]))
    }

    /// The element of a `for` over a `meta.Fields<T>` or a `meta.Cases<T>`: a field, whose type is
    /// fresh in the loop's body, or a case, whose payload's type is (meta.fields and
    /// meta.variant-cases).
    pub(super) fn reflected_element(&mut self, t: &Ty) -> Option<Ty> {
        match t {
            Ty::Con(item, args) if is_meta(item, "Fields") && args.len() == 1 => {
                let f = self.fresh_type('F');
                Some(meta_ty("Field", vec![args[0].clone(), f]))
            }
            Ty::Con(item, args) if is_meta(item, "Cases") && args.len() == 1 => {
                let p = self.fresh_type('P');
                Some(meta_ty("Case", vec![args[0].clone(), p]))
            }
            _ => None,
        }
    }

    /// An `if` whose condition is a bound test (meta.bound-tests): inside the branch it guards, the
    /// type parameter has the bounds besides its own, and the `else` branch knows nothing more.
    pub(super) fn bound_if(
        &mut self,
        cx: &mut Cx,
        (expected, at): (Option<&Ty>, TextRange),
        cond: &hir::Expr,
        test: &hir::BoundTest,
        (body, alt): (&[hir::Stmt], Option<&hir::Expr>),
    ) -> tast::Expr {
        let Some(param) = &test.param else {
            self.broken = true;
            let (b, alt, ty) = self.branches(cx, expected, at, body, alt);
            return node(
                tast::ExprKind::If(Box::new(error_node(cond.at)), b, alt),
                ty,
                at,
            );
        };
        let tested = Ty::Param(param.clone());
        let mut traits = Vec::new();
        for (bound, _) in &test.bounds {
            match bound {
                TraitRef::Trait(item, args) => {
                    let args: Vec<Ty> = args
                        .iter()
                        .map(|a| Ty::from_hir(a, self.env.self_ty.as_ref()))
                        .collect();
                    traits.push((item.clone(), args));
                }
                TraitRef::Error => self.broken = true,
            }
        }
        let (bounds, bound_args) = (self.env.bounds.len(), self.env.bound_args.len());
        let obligations = self.obligations.len();
        self.env.bounds.push((
            tested.clone(),
            traits.iter().map(|(t, _)| t.clone()).collect(),
        ));
        for (t, args) in traits.iter().filter(|(_, args)| !args.is_empty()) {
            self.env
                .bound_args
                .push((tested.clone(), t.clone(), args.clone()));
        }
        let (b, ty) = self.block_expr(cx, at, expected.filter(|_| alt.is_some()), body);
        // The bounds hold only in the branch, so what it needs of them is decided there.
        self.settle_args();
        self.discharge(obligations);
        self.env.bounds.truncate(bounds);
        self.env.bound_args.truncate(bound_args);
        let (alt, ty) = self.after_branch(cx, (expected, at), ty, alt);
        let c = node(tast::ExprKind::Bound(tested, traits), Ty::bool(), cond.at);
        node(tast::ExprKind::If(Box::new(c), b, alt), ty, at)
    }

    /// The obligations from `start` on that the bounds in scope now meet, which leave the
    /// list: a bound test's branch meets them with the bounds it adds.
    fn discharge(&mut self, start: usize) {
        let traits = crate::implements::Traits {
            decls: self.env.decls,
            scope: &self.env.bound_args,
            table: &self.table,
        };
        let bounds = &self.env.bounds;
        let mut index = 0;
        self.obligations.retain(|(ty, t, _)| {
            index += 1;
            index <= start || traits.implements(bounds, ty, t) != crate::implements::Answer::Yes
        });
    }
}
