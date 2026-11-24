//! Whether patterns can fail to match (patterns.irrefutable-positions), and the variants that names
//! written without a module name in them (patterns.variants-by-type).

use stilt_diag::codes;
use stilt_hir::decls::TypeDefInfo;
use stilt_hir::hir::{self, Fallback, GenericId, Item, ListRest, Name, PatKind, TypeRef};

use super::State;
use crate::ty::{Ty, instantiate};

/// What a name that a pattern writes without a module names, once the pattern is checked.
#[derive(Clone, Debug)]
pub(super) enum Named {
    Variant(Item),
    Const,
    Error,
}

impl State<'_> {
    /// patterns.variants-by-type: the variant `name` of `ty`, when `ty` is known by its outermost
    /// constructor to be a variant type with a variant of that name, or a shape with a case of
    /// that name (meta.shapes).
    pub(super) fn matched_variant(&self, ty: &Ty, name: &str) -> Option<Item> {
        if self.table.resolve(ty).meta_of("Shape").is_some() {
            return crate::ty::SHAPE_CASES
                .contains(&name)
                .then(|| crate::ty::meta_item(name));
        }
        let Ty::Con(owner, _) = &self.table.shape(ty) else {
            return None;
        };
        let info = self.env.decls.type_info(owner)?;
        match &info.def {
            TypeDefInfo::Variants(vs) if vs.iter().any(|(n, _)| &**n == name) => Some(Item {
                home: owner.home,
                name: Name::from(name),
            }),
            _ => None,
        }
    }

    /// The arguments of `ty` as a value of the type constructor `owner`, or the error type for
    /// each when `ty` isn't known to be one.
    fn type_arguments(&self, ty: &Ty, owner: &Item, params: &[GenericId]) -> Vec<Ty> {
        match &self.table.shape(ty) {
            Ty::Con(o, args) if o == owner && args.len() == params.len() => args.clone(),
            _ => params.iter().map(|_| Ty::Error).collect(),
        }
    }

    /// The types of the `n` parts of a pattern of type `ty`, which `owner` declares as
    /// `declared` in terms of its `params`, when `ty` is given.
    fn parts(
        &self,
        ty: Option<&Ty>,
        owner: &Item,
        params: &[GenericId],
        declared: &[hir::Ty],
        n: usize,
    ) -> Vec<Option<Ty>> {
        match ty {
            Some(t) if declared.len() == n => {
                let args = self.type_arguments(t, owner, params);
                declared
                    .iter()
                    .map(|d| Some(instantiate(d, params, &args)))
                    .collect()
            }
            _ => vec![None; n],
        }
    }

    /// The types of the fields of the record type `t` that a pattern of type `ty` names, when
    /// `ty` is given.
    fn record_parts(&self, ty: Option<&Ty>, t: &TypeRef) -> Vec<(Name, Ty)> {
        let (Some(ty), hir::Ty::Con(item, _)) = (ty, &t.ty) else {
            return Vec::new();
        };
        let Some(info) = self.env.decls.type_info(item) else {
            return Vec::new();
        };
        let TypeDefInfo::Record(fields) = &info.def else {
            return Vec::new();
        };
        let args = self.type_arguments(ty, item, &info.params);
        fields
            .iter()
            .map(|(n, ft)| (*n, instantiate(ft, &info.params, &args)))
            .collect()
    }

    /// The element type of the array a list pattern matches, if it matches one: as matched
    /// against `ty`, or the `Option` of it before a let-else's `else`, which a pattern that
    /// can't fail reads as `let p = (e else x)` (patterns.let-else), or as checking the pattern
    /// found it. generics.array-patterns: a list pattern on an array is irrefutable when its
    /// elements are; one whose length doesn't fit the array's size is an error of its own.
    fn array_element(&self, p: &hir::Pat, ty: Option<&Ty>) -> Option<Ty> {
        let matched = |t: &Ty| match self.resolved(t) {
            Ty::Con(item, args) if crate::ty::is_prelude(&item, "Option") && args.len() == 1 => {
                self.array_of(&args[0])
            }
            _ => self.array_of(t),
        };
        ty.and_then(matched)
            .map(|(elem, _)| elem)
            .or_else(|| self.array_patterns.get(&p.at).cloned())
    }

    /// patterns.irrefutable-positions: a pattern is irrefutable when its form alone guarantees a
    /// match, given how many variants the types it names have. A name written without a module
    /// names what checking the pattern found it to name, or, before the pattern is checked, what it
    /// names as matched against `ty` where that is given (patterns.variants-by-type), as for a
    /// let-else (patterns.let-else).
    pub(super) fn irrefutable(&self, p: &hir::Pat, ty: Option<&Ty>) -> bool {
        match &p.kind {
            PatKind::Wild | PatKind::Bind(_) | PatKind::Error => true,
            PatKind::Tuple(ps) => {
                let items: Vec<Option<Ty>> = match ty.map(|t| self.table.resolve(t)) {
                    Some(Ty::Tuple(ts)) if ts.len() == ps.len() => {
                        ts.iter().cloned().map(Some).collect()
                    }
                    _ => vec![None; ps.len()],
                };
                ps.iter()
                    .zip(&items)
                    .all(|(q, t)| self.irrefutable(q, t.as_ref()))
            }
            PatKind::AnonRecord(fields, _) => {
                let declared = ty.and_then(|t| self.record_fields(t)).unwrap_or_default();
                fields.iter().all(|f| {
                    let field = declared.iter().find(|(n, _)| *n == f.field.name);
                    self.irrefutable(&f.pattern, field.map(|(_, t)| t))
                })
            }
            PatKind::Record(t, fields, _) => {
                let declared = self.record_parts(ty, t);
                fields.iter().all(|f| {
                    let field = declared.iter().find(|(n, _)| *n == f.field.name);
                    self.irrefutable(&f.pattern, field.map(|(_, t)| t))
                })
            }
            PatKind::Variant(item, ps) => self.variant_irrefutable(ty, item, ps),
            PatKind::Bare(n, ps, fallback) => match self.bare.get(&p.at) {
                Some(Named::Variant(item)) => self.variant_irrefutable(None, item, ps),
                Some(Named::Const) => false,
                Some(Named::Error) => true,
                None => match (
                    ty.and_then(|t| self.matched_variant(t, &n.name)),
                    &**fallback,
                ) {
                    (Some(item), _) => self.variant_irrefutable(ty, &item, ps),
                    (None, Fallback::Variant(item)) => self.variant_irrefutable(ty, item, ps),
                    (None, Fallback::Const(_)) => false,
                    (None, Fallback::Error | Fallback::Failed(_)) => true,
                },
            },
            PatKind::List(ps, ListRest::Rest | ListRest::Bind(_)) if ps.is_empty() => true,
            PatKind::List(ps, _) if let Some(elem) = self.array_element(p, ty) => {
                ps.iter().all(|q| self.irrefutable(q, Some(&elem)))
            }
            PatKind::Or(alternatives) => alternatives.iter().any(|q| self.irrefutable(q, ty)),
            PatKind::Int(_)
            | PatKind::Str(_)
            | PatKind::Bool(_)
            | PatKind::Const(_)
            | PatKind::AssocConst(..)
            | PatKind::List(..) => false,
        }
    }

    fn variant_irrefutable(&self, ty: Option<&Ty>, item: &Item, ps: &[hir::Pat]) -> bool {
        // A shape has many cases (meta.shapes).
        if crate::ty::is_shape_case(item) {
            return false;
        }
        let Some(v) = self.env.decls.variant(item) else {
            return true;
        };
        let Some(info) = self.env.decls.type_info(&v.ty) else {
            return false;
        };
        if !matches!(&info.def, TypeDefInfo::Variants(vs) if vs.len() == 1) {
            return false;
        }
        let types = self.parts(ty, &v.ty, &info.params, &v.payload, ps.len());
        ps.iter()
            .zip(&types)
            .all(|(q, t)| self.irrefutable(q, t.as_ref()))
    }

    /// Reports a pattern that can fail to match where it must not, once it is checked.
    pub(super) fn require_irrefutable(&mut self, p: &hir::Pat) {
        if !self.irrefutable(p, None) {
            let message = "this pattern can fail to match, which isn't allowed here";
            self.error(codes::E0321, p.at, message.to_owned());
        }
    }
}
