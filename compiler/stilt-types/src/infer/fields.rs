//! Fields: places, reads of fields, through an `Option` too (types.fields-through-option), and
//! record literals.

use stilt_diag::{Edit, Fix, codes};
use stilt_hir::decls::prelude_item;
use stilt_hir::hir::{self, FieldInit, Ident, Name, TypeRef};
use stilt_syntax::TextRange;

use super::{Cx, State, error_node, node};
use crate::tast::{self, Arm, ExprKind, Pat, PatKind};
use crate::ty::Ty;

/// expressions.places: a variable, or a field or element of a place.
pub(super) fn is_place(e: &hir::Expr) -> bool {
    match &e.kind {
        hir::ExprKind::Local(_) => true,
        hir::ExprKind::Field(base, _) | hir::ExprKind::Index(base, _) => is_place(base),
        _ => false,
    }
}

/// Whether `e` may be a place once checked: a place, or a call that may be a projection's
/// (projections.call-is-place), which only its callee decides.
pub(super) fn may_be_place(e: &hir::Expr) -> bool {
    match &e.kind {
        hir::ExprKind::Local(_) | hir::ExprKind::Call(..) => true,
        hir::ExprKind::Field(base, _) | hir::ExprKind::Index(base, _) => may_be_place(base),
        _ => false,
    }
}

/// expressions.places and projections.call-is-place: whether `e`, whose checked form is `checked`,
/// is a place.
pub(super) fn checked_place(e: &hir::Expr, checked: &tast::Expr) -> bool {
    is_place(e) || checked.rooted_in_projection()
}

/// types.option-field-not-place: whether the checked form of a place reads a field through an
/// `Option`, which makes it a copy rather than a place. Such a read is checked as a `match`.
pub(super) fn through_option(e: &tast::Expr) -> bool {
    match &e.kind {
        ExprKind::Match(..) => true,
        ExprKind::Field(base, _) | ExprKind::TupleField(base, _) | ExprKind::Index(base, _) => {
            through_option(base)
        }
        _ => false,
    }
}

/// Why the checked form of a place is no place: a field read through an `Option` is a copy
/// (types.option-field-not-place). An element read through a view is a place, rooted in the view's
/// binding (projections.places-through-views).
pub(super) fn not_a_place(e: &tast::Expr) -> Option<&'static str> {
    through_option(e).then_some("a field read through an `Option` is a copy")
}

impl State<'_> {
    /// The fields of a record type, with their types for its arguments.
    /// A type parameter's are those its record bounds name (records.bound-fields).
    pub(super) fn record_fields(&self, ty: &Ty) -> Option<Vec<(Name, Ty)>> {
        self.args().fields_of(&self.table.shape(ty))
    }

    /// A field of `b`, whose type `ty` is known and isn't an `Option`: an element of a tuple,
    /// or a field of a record.
    fn read_direct(&mut self, at: TextRange, b: tast::Expr, ty: &Ty, field: &Ident) -> tast::Expr {
        if ty.shared().is_some() {
            return self.shared_member(at, &b, ty, field);
        }
        let found = match field.name.parse::<usize>() {
            Ok(_) if self.pack_tuple(ty) => {
                self.unknown_arity(at, "no element of it can be named");
                return error_node(at);
            }
            Ok(i) => match ty {
                Ty::Tuple(ts) if i < ts.len() => Some(node(
                    ExprKind::TupleField(Box::new(b), i),
                    ts[i].clone(),
                    at,
                )),
                _ => None,
            },
            Err(_) => self
                .record_fields(ty)
                .and_then(|fields| fields.into_iter().find(|(n, _)| *n == field.name))
                .map(|(_, t)| node(ExprKind::Field(Box::new(b), field.name), t, at)),
        };
        found.unwrap_or_else(|| {
            let length = is_length(&field.name) && has_len(ty);
            let hint = if ty.is_prelude("Result") {
                "; convert a `Result` with `.ok()` first"
            } else if length {
                "; a length is the method `len()`"
            } else {
                ""
            };
            let message = format!("`{}` has no field `{}`{hint}", self.show(ty), field.name);
            let names: Vec<Name> = self
                .record_fields(ty)
                .into_iter()
                .flatten()
                .map(|(n, _)| n)
                .collect();
            self.not_found(codes::E0313, field, message, names.iter().map(|n| &**n));
            if let Some(d) = self.errors.last_mut().filter(|_| length) {
                let fix = Fix::new("call `len()`", vec![Edit::replace(field.at, "len()")]);
                d.fixes.insert(0, fix);
                *d = d
                    .clone()
                    .with_help("Strings, lists, arrays, maps and sets have a `len` method.");
            }
            error_node(at)
        })
    }

    /// shared.std-sync: a `Shared<T>` has no field; its value is reached in a `when`, which the
    /// fix puts around the statement, when the handle is a local and no closure or `when` is
    /// between them.
    fn shared_member(
        &mut self,
        at: TextRange,
        b: &tast::Expr,
        ty: &Ty,
        field: &Ident,
    ) -> tast::Expr {
        let message = format!(
            "`{}` has no field `{}`: its value is reached only inside a `when` that names it",
            self.show(ty),
            field.name
        );
        let fix = match (&b.kind, self.wrap) {
            (ExprKind::Local(v), Some(wrap)) => {
                let handle = &self.local_names[v.0 as usize];
                vec![Fix::new(
                    format!("read it inside `when {handle}`"),
                    vec![
                        Edit::insert(wrap.start(), format!("when {handle} {{ ")),
                        Edit::insert(wrap.end(), " }"),
                    ],
                )]
            }
            _ => Vec::new(),
        };
        self.error_fixed(codes::E0313, field.at, message, fix);
        error_node(at)
    }

    /// The field `field` of `b`, whose type `ty` is known. types.fields-through-option: on an
    /// `Option`, the read goes through it, as `match b { Some(x) => x.field, None => None }`, where
    /// the value of `x.field` is wrapped in `Some` unless it is an `Option` already.
    fn read_field(&mut self, at: TextRange, b: tast::Expr, ty: &Ty, field: &Ident) -> tast::Expr {
        match ty {
            Ty::Con(_, args) if ty.is_prelude("Option") && args.len() == 1 => {
                match self.known(b.at, &args[0]) {
                    None => error_node(at),
                    Some(inner) => self.read_through(at, b, ty, &args[0], &inner, field),
                }
            }
            _ => self.read_direct(at, b, ty, field),
        }
    }

    /// A read through `b`, an `Option` of type `ty` whose values have type `t`, which is known
    /// to be `inner_ty`.
    fn read_through(
        &mut self,
        at: TextRange,
        b: tast::Expr,
        ty: &Ty,
        t: &Ty,
        inner_ty: &Ty,
        field: &Ident,
    ) -> tast::Expr {
        let x = self.synthetic("x");
        let local = node(ExprKind::Local(x), t.clone(), b.at);
        let inner = self.read_field(at, local, inner_ty, field);
        let scrutinee_at = b.at;
        let through = |value: tast::Expr, u: Ty| {
            let arm = |variant: &str, payload: Vec<Pat>, body: tast::Expr| Arm {
                pattern: Pat {
                    kind: PatKind::Variant(prelude_item(variant), payload),
                    ty: ty.clone(),
                    at: scrutinee_at,
                },
                guard: None,
                because: false,
                body,
            };
            let option = Ty::option(u.clone());
            let none = ExprKind::Construct(prelude_item("None"), vec![u], Vec::new());
            let binding = Pat {
                kind: PatKind::Bind(x),
                ty: t.clone(),
                at: scrutinee_at,
            };
            let arms = vec![
                arm("Some", vec![binding], value),
                arm("None", Vec::new(), node(none, option.clone(), at)),
            ];
            node(ExprKind::Match(Box::new(b), arms), option, at)
        };
        // types.option-field-known: whether the read adds a level of `Option` depends on the
        // field's type, which must be known here.
        match self.known(at, &inner.ty) {
            None => error_node(at),
            Some(Ty::Error) => inner,
            Some(Ty::Con(item, args))
                if crate::ty::is_prelude(&item, "Option") && args.len() == 1 =>
            {
                let u = args[0].clone();
                through(inner, u)
            }
            Some(u) => {
                let some = ExprKind::Construct(prelude_item("Some"), vec![u.clone()], vec![inner]);
                let wrapped = node(some, Ty::option(u.clone()), at);
                through(wrapped, u)
            }
        }
    }

    pub(super) fn field_access(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        base: &hir::Expr,
        field: &Ident,
    ) -> tast::Expr {
        let b = self.infer(cx, None, base);
        match self.known(base.at, &b.ty) {
            None => error_node(at),
            Some(ty) => self.read_field(at, b, &ty, field),
        }
    }

    /// A struct literal, or an anonymous one, whose type is that of its fields' values, taking the
    /// field types of an expected anonymous record of the same fields first
    /// (records.anonymous-literals).
    pub(super) fn struct_literal(
        &mut self,
        cx: &mut Cx,
        (at, expected): (TextRange, Option<&Ty>),
        t: &TypeRef,
        fields: &[FieldInit],
    ) -> tast::Expr {
        let ty = self.named_type(t);
        if let (Ty::Con(item, _), Some(e)) = (self.resolved(&ty), expected)
            && item.is_record()
            && matches!(self.resolved(e), Ty::Con(other, _) if other == item)
        {
            self.table.unify(&ty, e);
        }
        match (self.resolved(&ty), self.record_fields(&ty)) {
            (Ty::Error, _) => {
                for f in fields {
                    self.abandon(cx, &f.value);
                }
                error_node(at)
            }
            (Ty::Con(item, args), Some(declared)) => {
                let (values, seen) = self.record_values(cx, &item.name, &declared, fields);
                let missing: Vec<String> = declared
                    .iter()
                    .filter(|(n, _)| !seen.contains(n))
                    .map(|(n, _)| format!("`{n}`"))
                    .collect();
                if !missing.is_empty() {
                    let s = if missing.len() == 1 { "" } else { "s" };
                    let message = format!("this literal lacks the field{s} {}", missing.join(", "));
                    self.error(codes::E0316, t.at, message);
                }
                node(ExprKind::Record(item, args, values), ty, at)
            }
            (other, _) => {
                let message = format!("`{}` is not a record type", self.show(&other));
                self.error(codes::E0311, t.at, message);
                for f in fields {
                    self.abandon(cx, &f.value);
                }
                error_node(at)
            }
        }
    }

    /// The values of a record literal's fields, each checked against its field's type, and the
    /// declared fields given.
    fn record_values(
        &mut self,
        cx: &mut Cx,
        record: &str,
        declared: &[(Name, Ty)],
        fields: &[FieldInit],
    ) -> (Vec<(Name, tast::Expr)>, Vec<Name>) {
        let mut seen: Vec<Name> = Vec::new();
        let mut values = Vec::new();
        for (i, f) in fields.iter().enumerate() {
            let name = f.field.name;
            if let Some((_, t)) = declared.iter().find(|(n, _)| *n == name) {
                if seen.contains(&name) {
                    let message = format!("the field `{name}` is given twice");
                    let gone = TextRange::new(fields[i - 1].value.at.end(), f.value.at.end());
                    let fix = Fix::new("delete the repeated field", vec![Edit::delete(gone)]);
                    self.error_fixed(codes::E0316, f.field.at, message, vec![fix]);
                }
                seen.push(name);
                let v = self.check(cx, t, &f.value);
                // A field of an anonymous literal has its value's type, `Never` among them, as an
                // element of a list does (records.anonymous-literals).
                if matches!(self.resolved(t), Ty::Var(_)) {
                    self.table.unify(t, &v.ty);
                }
                values.push((name, v));
            } else {
                let message = format!("`{record}` has no field `{name}`");
                let unnamed = declared
                    .iter()
                    .map(|(n, _)| &**n)
                    .filter(|n| fields.iter().all(|f| &*f.field.name != *n));
                self.not_found(codes::E0313, &f.field, message, unnamed);
                let v = self.abandon(cx, &f.value);
                values.push((name, v));
            }
        }
        (values, seen)
    }
}

/// Whether another language names a collection's length `name`, as a field.
fn is_length(name: &str) -> bool {
    matches!(name, "length" | "size" | "count" | "len")
}

/// Whether values of `ty` have a `len` method: strings, lists, arrays, maps and sets.
fn has_len(ty: &Ty) -> bool {
    ty.is_prelude("str")
        || ["List", "Map", "Set"].iter().any(|n| ty.is_prelude(n))
        || matches!(ty, Ty::Con(item, _) if crate::ty::is_array(item))
}
