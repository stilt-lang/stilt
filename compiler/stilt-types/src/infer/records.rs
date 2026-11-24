//! Record bounds, updates and the patterns that name no type (records.anonymous-patterns,
//! records.record-bounds and records.update).

use stilt_diag::{Edit, Fix, codes};
use stilt_hir::hir::{self, FieldInit, FieldPat, Item, Name, TypeRef};
use stilt_syntax::TextRange;

use super::{Cx, State, error_node, node};
use crate::tast;
use crate::ty::Ty;

impl State<'_> {
    /// A record bound as a program writes it, `{ f: T, .. }`, with the field types `types`.
    fn bound_text(&self, bound: &Item, types: &[Ty]) -> String {
        let fields: Vec<String> = bound
            .record_fields()
            .iter()
            .zip(types)
            .map(|(f, t)| format!("{f}: {}", self.show(t)))
            .collect();
        format!("{{ {}, .. }}", fields.join(", "))
    }

    /// E0318: `ty` lacks a field that the record bound `bound` names, whose types are `wanted`
    /// (records.record-bounds).
    pub(super) fn record_missing(&mut self, ty: &Ty, bound: &Item, wanted: &[Ty], at: TextRange) {
        let text = self.bound_text(bound, wanted);
        let shown = self.show(ty);
        let fields = self.record_fields(ty);
        let message = match fields {
            None => {
                let first = bound.record_fields().into_iter().next().unwrap_or_default();
                format!(
                    "`{shown}` isn't a record, so it has no field `{first}`, which the bound \
                     `{text}` needs"
                )
            }
            Some(fields) => {
                let lacking: Vec<String> = bound
                    .record_fields()
                    .into_iter()
                    .filter(|n| fields.iter().all(|(m, _)| m != n))
                    .map(|n| format!("`{n}`"))
                    .collect();
                let s = if lacking.len() == 1 { "" } else { "s" };
                format!(
                    "`{shown}` has no field{s} {}, which the bound `{text}` needs",
                    lacking.join(", ")
                )
            }
        };
        self.error(codes::E0318, at, message);
    }

    /// E0318 unless each field that the record bound `bound` names has, in `ty`, the type the
    /// bound gives it (records.record-bounds).
    pub(super) fn meet_record(
        &mut self,
        ty: &Ty,
        bound: &Item,
        (wanted, actual): (&[Ty], &[Ty]),
        at: TextRange,
    ) {
        let names = bound.record_fields();
        let differing = names
            .iter()
            .zip(wanted.iter().zip(actual))
            .find(|(_, (w, a))| !self.table.unify(w, a));
        if let Some((name, (w, a))) = differing {
            let message = format!(
                "the field `{name}` of `{}` is `{}`, but the bound `{}` needs `{}`",
                self.show(ty),
                self.show(a),
                self.bound_text(bound, wanted),
                self.show(w),
            );
            self.error(codes::E0318, at, message);
        }
    }

    /// An update, `Name { ..base, f: e }` or `{ ..base, f: e }`, of `base`'s type, with the
    /// fields written replaced (records.update): each one of the type's, or of a bound's for a
    /// type parameter (E0313), at most once (E0316), with its type (E0311).
    pub(super) fn update_expr(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        (t, base): (Option<&TypeRef>, &hir::Expr),
        fields: &[FieldInit],
    ) -> tast::Expr {
        // A named update has the type it names, whose fields' types hold even when its base
        // fails to check (errors.error-type).
        let (b, named) = match t {
            Some(t) => {
                let ty = self.named_type(t);
                (self.check(cx, &ty, base), Some(ty))
            }
            None => (self.infer(cx, None, base), None),
        };
        let Some(ty) = self.known(base.at, named.as_ref().unwrap_or(&b.ty)) else {
            for f in fields {
                self.abandon(cx, &f.value);
            }
            return error_node(at);
        };
        let Some(declared) = self.record_fields(&ty) else {
            if ty != Ty::Error {
                let message = format!(
                    "`{}` isn't a record, so it has no fields to update",
                    self.show(&ty)
                );
                self.error(codes::E0311, base.at, message);
            }
            for f in fields {
                self.abandon(cx, &f.value);
            }
            return error_node(at);
        };
        if t.is_none()
            && let Ty::Con(item, _) = &ty
            && !item.is_record()
        {
            // The update fails to check, so it has the error type, and its fields are checked
            // as code no type expects (errors.error-type).
            self.declared_update(at, base.at, item);
            for f in fields {
                self.abandon(cx, &f.value);
            }
            return error_node(at);
        }
        let shown = self.show(&ty);
        let values = self.updated(cx, &shown, &declared, fields);
        node(tast::ExprKind::Update(Box::new(b), values), ty, at)
    }

    /// E0311 at the base `base` of the update at `at`: `{ ..base, … }` on a declared record,
    /// whose update names it (records.update).
    fn declared_update(&mut self, at: TextRange, base: TextRange, item: &Item) {
        let name = &item.name;
        let message = format!("`{name}` is a declared record, so its update names it");
        let fix = Fix::new(
            format!("write `{name} {{ … }}`"),
            vec![Edit::insert(at.start(), format!("{name} "))],
        );
        self.error_fixed(codes::E0311, base, message, vec![fix]);
    }

    /// The values of an update's fields, each checked against its field's type.
    fn updated(
        &mut self,
        cx: &mut Cx,
        record: &str,
        declared: &[(Name, Ty)],
        fields: &[FieldInit],
    ) -> Vec<(Name, tast::Expr)> {
        let mut values: Vec<(Name, tast::Expr)> = Vec::new();
        for (i, f) in fields.iter().enumerate() {
            let name = f.field.name;
            let Some((_, t)) = declared.iter().find(|(n, _)| *n == name) else {
                let message =
                    format!("`{record}` has no field `{name}`, and an update never adds one");
                let names = declared.iter().map(|(n, _)| &**n);
                self.not_found(codes::E0313, &f.field, message, names);
                let v = self.abandon(cx, &f.value);
                values.push((name, v));
                continue;
            };
            if values.iter().any(|(n, _)| *n == name) {
                let message = format!("the field `{name}` is given twice");
                let gone = TextRange::new(fields[i - 1].value.at.end(), f.value.at.end());
                let fix = Fix::new("delete the repeated field", vec![Edit::delete(gone)]);
                self.error_fixed(codes::E0316, f.field.at, message, vec![fix]);
            }
            let v = self.check(cx, t, &f.value);
            values.push((name, v));
        }
        values
    }

    /// A pattern that names no type, `{ f, g: p }`, of a record whose fields its type tells:
    /// an anonymous record, a declared one, or a type parameter whose bounds name them
    /// (records.anonymous-patterns).
    pub(super) fn anon_record_pattern(
        &mut self,
        cx: &mut Cx,
        p: &hir::Pat,
        ty: &Ty,
        fields: &[FieldPat],
        rest: bool,
    ) -> tast::PatKind {
        let declared = match self.known(p.at, ty) {
            Some(Ty::Error) | None => None,
            Some(t) => {
                if let Some(declared) = self.record_fields(&t) {
                    Some((t, declared))
                } else {
                    let message = format!(
                        "`{}` isn't a record, so a record pattern can't match it",
                        self.show(&t)
                    );
                    self.error(codes::E0311, p.at, message);
                    None
                }
            }
        };
        let Some((rty, declared)) = declared else {
            for f in fields {
                self.pattern(cx, &f.pattern, &Ty::Error);
            }
            return tast::PatKind::Error;
        };
        // A bound never names every field of the type that meets it (records.anonymous-patterns).
        if matches!(rty, Ty::Param(_)) && !rest {
            let message = format!(
                "`{}` may have fields that its bound doesn't name, so this pattern ends with `..`",
                self.show(&rty)
            );
            let rest = match fields.last() {
                Some(last) => Edit::insert(last.pattern.at.end(), ", .."),
                None => Edit::insert(p.at.end() - stilt_syntax::TextSize::from(1), ".."),
            };
            let fix = Fix::new("ignore the other fields", vec![rest]);
            self.error_fixed(codes::E0316, p.at, message, vec![fix]);
        }
        let rest = rest || matches!(rty, Ty::Param(_));
        self.field_patterns(cx, (p, p.at), &rty, &declared, fields, rest)
    }
}
