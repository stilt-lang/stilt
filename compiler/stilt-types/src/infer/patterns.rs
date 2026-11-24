//! Patterns: their types (patterns.pattern-types).

use stilt_diag::{Edit, Fix, codes};
use stilt_hir::decls::{TypeDefInfo, prelude_item};
use stilt_hir::hir::{self, FieldPat, Ident, Item, ListRest, PatKind, TypeRef};

use stilt_syntax::{TextRange, TextSize};

use super::{Cx, State, node};
use crate::tast::{self, ExprKind};
use crate::ty::{Ty, instantiate, is_float};

impl State<'_> {
    /// Whether a value of type `t` can hold a value of a type constructor that `at` picks,
    /// through its elements, fields and payloads. A type met again inside itself can add only
    /// what its arguments hold.
    fn holds(&self, at: &dyn Fn(&Item) -> bool, seen: &[Item], t: &Ty) -> bool {
        match &self.table.shape(t) {
            Ty::Con(item, _) if at(item) => true,
            Ty::Con(item, args) if seen.contains(item) => {
                args.iter().any(|a| self.holds(at, seen, a))
            }
            Ty::Con(item, args) => {
                let inside: Vec<Item> = std::iter::once(item.clone())
                    .chain(seen.iter().cloned())
                    .collect();
                let held = |t: &hir::Ty, params: &[_]| {
                    self.holds(at, &inside, &instantiate(t, params, args))
                };
                match self.env.decls.type_info(item) {
                    Some(info) => match &info.def {
                        TypeDefInfo::Builtin => args.iter().any(|a| self.holds(at, &inside, a)),
                        TypeDefInfo::Record(fields) => {
                            fields.iter().any(|(_, t)| held(t, &info.params))
                        }
                        TypeDefInfo::Variants(vs) => vs
                            .iter()
                            .any(|(_, payload)| payload.iter().any(|t| held(t, &info.params))),
                    },
                    None => false,
                }
            }
            Ty::Tuple(ts) => ts.iter().any(|t| self.holds(at, seen, t)),
            Ty::Spread(s) => self.holds(at, seen, &s.elem),
            Ty::Param(_)
            | Ty::Handler(_)
            | Ty::SelfTy
            | Ty::App(..)
            | Ty::Fn(_)
            | Ty::Var(_)
            | Ty::Value(_)
            | Ty::Error => false,
        }
    }

    /// patterns.floats.
    pub(super) fn holds_float(&self, t: &Ty) -> bool {
        self.holds(&is_float, &[], t)
    }

    /// patterns.constants-with-written-eq.
    fn holds_written_eq(&self, t: &Ty) -> bool {
        let decls = self.env.decls;
        let eq = prelude_item("Eq");
        self.holds(&|item| decls.trait_impl(&eq, item).is_some(), &[], t)
    }

    /// The parts of a pattern's type, made of `parts` by `make`: the parts when the pattern's
    /// type `ty` is made that way, and the error type for each part when it is the error type
    /// or can't be (errors.error-type). The variables in `parts` then stand for nothing, so they
    /// are tainted.
    fn shaped(
        &mut self,
        p: &hir::Pat,
        ty: &Ty,
        parts: Vec<Ty>,
        make: impl Fn(Vec<Ty>) -> Ty,
    ) -> Vec<Ty> {
        let fits =
            *self.table.resolve(ty) != Ty::Error && self.agrees(p.at, ty, &make(parts.clone()));
        if fits {
            parts
        } else {
            for t in &parts {
                self.table.taint(t);
            }
            parts.iter().map(|_| Ty::Error).collect()
        }
    }

    /// A constant that a pattern `p` matches, of type `t`.
    fn comparable(&mut self, p: &hir::Pat, t: &Ty) {
        if self.holds_float(t) {
            let message = "this constant holds a float, which a pattern can't match";
            self.error(codes::E0328, p.at, message.to_owned());
        } else if self.holds_written_eq(t) {
            let message = "this constant holds a type whose `Eq` you wrote, so compare it with `==` in a guard";
            self.error(codes::E0331, p.at, message.to_owned());
        }
    }

    pub(super) fn const_pattern(&mut self, p: &hir::Pat, ty: &Ty, item: &Item) -> tast::PatKind {
        let Some(t) = self.env.decls.constant(item).map(|t| Ty::from_hir(t, None)) else {
            return tast::PatKind::Error;
        };
        self.expect(p.at, ty, &t);
        self.comparable(p, &t);
        tast::PatKind::Const(Box::new(node(ExprKind::Constant(item.clone()), t, p.at)))
    }

    fn assoc_const_pattern(
        &mut self,
        cx: &mut Cx,
        p: &hir::Pat,
        ty: &Ty,
        t: &TypeRef,
        name: &Ident,
    ) -> tast::PatKind {
        let value = self.member_value(cx, (p.at, None), &hir::MemberOwner::Type(t.clone()), name);
        match &value.kind {
            ExprKind::MemberConstant(..) => {
                let vty = value.ty.clone();
                self.expect(p.at, ty, &vty);
                self.comparable(p, &vty);
                tast::PatKind::Const(Box::new(value))
            }
            ExprKind::Error => tast::PatKind::Error,
            _ => {
                let message = format!("`{}` is not a constant", name.name);
                self.error(codes::E0311, name.at, message);
                tast::PatKind::Error
            }
        }
    }

    /// A tuple's pattern, which can't take apart a pack tuple, whose arity isn't known
    /// (variadics.pack-tuples).
    fn tuple_pattern(
        &mut self,
        cx: &mut Cx,
        p: &hir::Pat,
        ty: &Ty,
        ps: &[hir::Pat],
    ) -> tast::PatKind {
        if self.pack_tuple(ty) {
            self.unknown_arity(p.at, "a pattern can't take it apart");
            for q in ps {
                self.pattern(cx, q, &Ty::Error);
            }
            return tast::PatKind::Error;
        }
        let parts = ps.iter().map(|q| self.fresh(q.at)).collect();
        let items = self.shaped(p, ty, parts, Ty::Tuple);
        tast::PatKind::Tuple(
            ps.iter()
                .zip(&items)
                .map(|(q, t)| self.pattern(cx, q, t))
                .collect(),
        )
    }

    pub(super) fn pattern(&mut self, cx: &mut Cx, p: &hir::Pat, ty: &Ty) -> tast::Pat {
        let kind = match &p.kind {
            PatKind::Wild => tast::PatKind::Wild,
            PatKind::Bind(v) => {
                if let Some(earlier) = self.locals.get(v).cloned() {
                    // The same variable in another alternative of an or-pattern.
                    self.expect(p.at, &earlier, ty);
                } else {
                    self.locals.insert(*v, ty.clone());
                    self.bound.insert(*v, p.at);
                }
                tast::PatKind::Bind(*v)
            }
            PatKind::Int(text) => {
                let (negative, digits) = match text.strip_prefix('-') {
                    Some(digits) => (true, digits),
                    None => (false, text.as_str()),
                };
                let lit = self.literal(digits, negative, false, p.at);
                self.expect(p.at, ty, &lit);
                self.int_patterns.push((ty.clone(), p.at));
                tast::PatKind::Int(text.clone())
            }
            PatKind::Str(s) => {
                self.expect(p.at, ty, &Ty::str());
                tast::PatKind::Str(s.clone())
            }
            PatKind::Bool(b) => {
                self.expect(p.at, ty, &Ty::bool());
                tast::PatKind::Bool(*b)
            }
            PatKind::Tuple(ps) => self.tuple_pattern(cx, p, ty, ps),
            PatKind::Const(item) => self.const_pattern(p, ty, item),
            PatKind::AssocConst(t, name) => self.assoc_const_pattern(cx, p, ty, t, name),
            PatKind::Variant(item, ps) => self.variant_pattern(cx, p, ty, item, ps),
            PatKind::Bare(n, ps, fallback) => self.bare_pattern(cx, p, ty, (n, ps, fallback)),
            PatKind::Record(t, fields, rest) => self.record_pattern(cx, p, ty, t, fields, *rest),
            PatKind::AnonRecord(fields, rest) => self.anon_record_pattern(cx, p, ty, fields, *rest),
            PatKind::List(ps, rest) => self.list_pattern(cx, p, ty, ps, *rest),
            PatKind::Or(alternatives) => tast::PatKind::Or(
                alternatives
                    .iter()
                    .map(|q| self.pattern(cx, q, ty))
                    .collect(),
            ),
            PatKind::Error => {
                self.broken = true;
                tast::PatKind::Error
            }
        };
        tast::Pat {
            kind,
            ty: ty.clone(),
            at: p.at,
        }
    }

    pub(super) fn variant_pattern(
        &mut self,
        cx: &mut Cx,
        p: &hir::Pat,
        ty: &Ty,
        item: &Item,
        ps: &[hir::Pat],
    ) -> tast::PatKind {
        let Some(v) = self.env.decls.variant(item) else {
            return tast::PatKind::Error;
        };
        let (_, args, params) = self.instantiate_type(p.at, &v.ty);
        let owner = v.ty.clone();
        let args = self.shaped(p, ty, args, |args| Ty::Con(owner.clone(), args));
        let payload: Vec<Ty> = v
            .payload
            .iter()
            .map(|t| instantiate(t, &params, &args))
            .collect();
        if payload.len() != ps.len() {
            let s = if payload.len() == 1 { "" } else { "s" };
            let message = format!(
                "`{}` has {} payload field{s}, but the pattern has {}",
                item.name,
                payload.len(),
                ps.len()
            );
            self.error(codes::E0315, p.at, message);
            for q in ps {
                self.pattern(cx, q, &Ty::Error);
            }
            return tast::PatKind::Error;
        }
        let items = ps
            .iter()
            .zip(&payload)
            .map(|(q, t)| self.pattern(cx, q, t))
            .collect();
        tast::PatKind::Variant(item.clone(), items)
    }

    fn record_pattern(
        &mut self,
        cx: &mut Cx,
        p: &hir::Pat,
        ty: &Ty,
        t: &TypeRef,
        fields: &[FieldPat],
        rest: bool,
    ) -> tast::PatKind {
        let rty = self.named_type(t);
        self.expect(p.at, ty, &rty);
        let Some(declared) = self.record_fields(&rty) else {
            if *self.table.resolve(&rty) != Ty::Error {
                let message = format!("`{}` is not a record type", self.show(&rty));
                self.error(codes::E0311, t.at, message);
            }
            for f in fields {
                self.pattern(cx, &f.pattern, &Ty::Error);
            }
            return tast::PatKind::Error;
        };
        self.field_patterns(cx, (p, t.at), &rty, &declared, fields, rest)
    }

    /// The fields `fields` of a record pattern `p`, matched against the record type `rty`,
    /// whose fields are `declared`, reported at `at`: each a field of the type, once (E0313,
    /// E0316), and every field unless `rest` (E0316).
    pub(super) fn field_patterns(
        &mut self,
        cx: &mut Cx,
        (p, at): (&hir::Pat, TextRange),
        rty: &Ty,
        declared: &[(stilt_hir::hir::Name, Ty)],
        fields: &[FieldPat],
        rest: bool,
    ) -> tast::PatKind {
        let mut seen = Vec::new();
        let mut matched = Vec::new();
        for (i, f) in fields.iter().enumerate() {
            let name = f.field.name;
            let field_ty = if let Some((_, ft)) = declared.iter().find(|(n, _)| *n == name) {
                if seen.contains(&name) {
                    let message = format!("the field `{name}` is matched twice");
                    let gone = TextRange::new(fields[i - 1].pattern.at.end(), f.pattern.at.end());
                    let fix = Fix::new("delete the repeated field", vec![Edit::delete(gone)]);
                    self.error_fixed(codes::E0316, f.field.at, message, vec![fix]);
                }
                seen.push(name);
                ft.clone()
            } else {
                let message = format!("`{}` has no field `{name}`", self.show(rty));
                let unmatched = declared
                    .iter()
                    .map(|(n, _)| &**n)
                    .filter(|n| fields.iter().all(|f| &*f.field.name != *n));
                self.not_found(codes::E0313, &f.field, message, unmatched);
                Ty::Error
            };
            matched.push((name, self.pattern(cx, &f.pattern, &field_ty)));
        }
        let missing: Vec<String> = declared
            .iter()
            .filter(|(n, _)| !seen.contains(n))
            .map(|(n, _)| format!("`{n}`"))
            .collect();
        if !rest && !missing.is_empty() {
            let s = if missing.len() == 1 { "" } else { "s" };
            let message = format!("this pattern lacks the field{s} {}", missing.join(", "));
            let rest = match fields.last() {
                Some(last) => Edit::insert(last.pattern.at.end(), ", .."),
                None => Edit::insert(p.at.end() - TextSize::from(1), ".."),
            };
            let fix = Fix::new(format!("ignore the other field{s}"), vec![rest]);
            self.error_fixed(codes::E0316, at, message, vec![fix]);
        }
        tast::PatKind::Record(matched)
    }

    fn list_pattern(
        &mut self,
        cx: &mut Cx,
        p: &hir::Pat,
        ty: &Ty,
        ps: &[hir::Pat],
        rest: ListRest,
    ) -> tast::PatKind {
        // generics.array-patterns: a list pattern matches an array whose size its length fits.
        if let Some((elem, size)) = self.array_of(ty) {
            return self.array_pattern(cx, p, (ty, elem, size), (ps, rest));
        }
        let parts = vec![self.fresh(p.at)];
        let elem = match self
            .shaped(p, ty, parts, |mut parts| match parts.pop() {
                Some(elem) if parts.is_empty() => Ty::list(elem),
                _ => Ty::Error,
            })
            .as_slice()
        {
            [elem] => elem.clone(),
            _ => Ty::Error,
        };
        let items = ps.iter().map(|q| self.pattern(cx, q, &elem)).collect();
        if let ListRest::Bind(v) = rest {
            self.locals.insert(v, Ty::list(elem));
        }
        tast::PatKind::List(items, rest)
    }
}
