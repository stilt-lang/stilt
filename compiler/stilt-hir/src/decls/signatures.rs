//! Signatures, and when two are the same (traits.impl-signatures).

use std::collections::BTreeSet;

use super::{BoundArgs, Bounds, FnSig};
use crate::hir::{FnDecl, Generic, GenericId, GenericKind, Mode, Owner, Param, Row, TraitRef, Ty};

pub(super) fn unit_ty() -> Ty {
    Ty::Tuple(Vec::new())
}

/// The type parameters among the generics that `owner` declares, with their bounds. A bound
/// with an error is left out, since the error type satisfies every bound (errors.error-type).
#[must_use]
pub fn bounds_of(generics: &[Generic], owner: &Owner) -> Bounds {
    (0..)
        .zip(generics)
        .filter_map(|(index, g)| match &g.kind {
            GenericKind::Type(bounds) => Some((
                GenericId {
                    owner: owner.clone(),
                    index,
                },
                bounds
                    .iter()
                    .filter_map(|b| match b {
                        TraitRef::Trait(item, _) => Some(item.clone()),
                        TraitRef::Error => None,
                    })
                    .collect(),
            )),
            // A value parameter is instantiated at each use as a type parameter is, with no
            // bounds (generics.value-parameter-inference).
            GenericKind::Value(_) => Some((
                GenericId {
                    owner: owner.clone(),
                    index,
                },
                Vec::new(),
            )),
            GenericKind::Row => None,
        })
        .collect()
}

/// The value parameters among the generics that `owner` declares, with their types
/// (generics.value-parameters).
#[must_use]
pub(super) fn values_of(generics: &[Generic], owner: &Owner) -> Vec<(GenericId, Ty)> {
    (0..)
        .zip(generics)
        .filter_map(|(index, g)| {
            let id = GenericId {
                owner: owner.clone(),
                index,
            };
            g.value_type().map(|t| (id, t.clone()))
        })
        .collect()
}

/// The arguments that the bounds of the generics that `owner` declares give the traits with
/// parameters, in order (traits.bound-arguments).
#[must_use]
pub fn bound_args_of(generics: &[Generic], owner: &Owner) -> Vec<BoundArgs> {
    (0..)
        .zip(generics)
        .flat_map(|(index, g)| {
            let param = GenericId {
                owner: owner.clone(),
                index,
            };
            g.bounds().iter().filter_map(move |b| match b {
                TraitRef::Trait(item, args) if !args.is_empty() => Some(BoundArgs {
                    param: param.clone(),
                    trait_item: item.clone(),
                    args: args.clone(),
                }),
                _ => None,
            })
        })
        .collect()
}

/// The signature of a function declared by `owner`, whose receiver has type `self_ty` unless it
/// writes its own (traits.receiver-types), after the type parameters `outer` of its impl block,
/// whose bounds give `outer_args`.
#[must_use]
pub fn signature(
    f: &FnDecl,
    owner: &Owner,
    self_ty: &Ty,
    (outer, outer_args): (&Bounds, &[BoundArgs]),
) -> FnSig {
    let mut type_params = outer.clone();
    type_params.extend(bounds_of(&f.generics, owner));
    let mut bound_args = outer_args.to_vec();
    bound_args.extend(bound_args_of(&f.generics, owner));
    // traits.where: a function of an inherent impl bounds its block's member types, which
    // its body assumes and its callers meet as the block's own bounds.
    for (id, refs) in &f.assumed {
        if let Some((_, traits)) = type_params.iter_mut().find(|(v, _)| v == id) {
            traits.extend(refs.iter().filter_map(|r| match r {
                TraitRef::Trait(item, _) => Some(item.clone()),
                TraitRef::Error => None,
            }));
        }
        // Their traits' arguments, as a bound beside a parameter gives them
        // (traits.bound-arguments).
        bound_args.extend(refs.iter().filter_map(|r| match r {
            TraitRef::Trait(item, args) if !args.is_empty() => Some(BoundArgs {
                param: id.clone(),
                trait_item: item.clone(),
                args: args.clone(),
            }),
            _ => None,
        }));
    }
    FnSig {
        owner: owner.clone(),
        type_params,
        values: values_of(&f.generics, owner),
        bound_args,
        row_params: (0..)
            .zip(&f.generics)
            .filter(|(_, g)| g.kind == GenericKind::Row)
            .map(|(index, _)| GenericId {
                owner: owner.clone(),
                index,
            })
            .collect(),
        params: f
            .params
            .iter()
            .map(|p| match p {
                Param::SelfParam(mode, written) => {
                    (*mode, written.clone().unwrap_or_else(|| self_ty.clone()))
                }
                Param::Param(mode, t, _) => (*mode, t.clone()),
            })
            .collect(),
        passing: f.params.iter().map(Param::passes).collect(),
        ret: f.ret.clone().unwrap_or_else(unit_ty),
        projection: f.projection,
        row: f.row.clone(),
        foreign: f.foreign,
        trusted: if f.foreign {
            f.limits
        } else {
            crate::hir::Limits::default()
        },
    }
}

/// The signature of a constant declared by `owner`, after the type parameters `outer` of its
/// impl block: it takes nothing and returns its type.
#[must_use]
pub(super) fn const_signature(owner: &Owner, outer: &Bounds, ty: &Ty) -> FnSig {
    FnSig {
        owner: owner.clone(),
        type_params: outer.clone(),
        values: Vec::new(),
        bound_args: Vec::new(),
        row_params: Vec::new(),
        params: Vec::new(),
        passing: Vec::new(),
        ret: ty.clone(),
        projection: false,
        row: Row::default(),
        foreign: false,
        trusted: crate::hir::Limits::default(),
    }
}

/// A trait's signature `sig` with its parameters replaced by `types`, the arguments an impl
/// gives them (traits.trait-arguments), as the impl's dictionary entries see it.
#[must_use]
pub fn substituted(sig: &FnSig, types: &[(GenericId, Ty)]) -> FnSig {
    let s = Subst {
        types: types.to_vec(),
        ..Subst::default()
    };
    FnSig {
        params: sig.params.iter().map(|(m, t)| (*m, s.ty(t))).collect(),
        ret: s.ty(&sig.ret),
        row: s.row(&sig.row),
        bound_args: sig
            .bound_args
            .iter()
            .map(|b| BoundArgs {
                args: b.args.iter().map(|a| s.ty(a)).collect(),
                ..b.clone()
            })
            .collect(),
        ..sig.clone()
    }
}

/// A substitution of types for type parameters and `Self`, and of rows for row variables.
#[derive(Default)]
pub(super) struct Subst {
    pub(super) self_ty: Option<Ty>,
    pub(super) types: Vec<(GenericId, Ty)>,
    pub(super) rows: Vec<(GenericId, Row)>,
}

impl Subst {
    pub(super) fn ty(&self, t: &Ty) -> Ty {
        match t {
            Ty::Con(item, args) => Ty::Con(item.clone(), args.iter().map(|a| self.ty(a)).collect()),
            Ty::Param(p) => self
                .types
                .iter()
                .find(|(q, _)| q == p)
                .map_or_else(|| t.clone(), |(_, t)| t.clone()),
            Ty::SelfTy => self.self_ty.clone().unwrap_or(Ty::SelfTy),
            Ty::App(head, args) => apply(self.ty(head), args.iter().map(|a| self.ty(a)).collect()),
            Ty::Tuple(ts) => Ty::Tuple(self.elements(ts)),
            Ty::Spread(p, elem) => Ty::Spread(p.clone(), Box::new(self.ty(elem))),
            Ty::Fn(f) => Ty::Fn(Box::new(crate::hir::FnTy {
                generics: f.generics.clone(),
                params: self.params(&f.params),
                ret: Some(self.ty(f.ret.as_ref().unwrap_or(&unit_ty()))),
                row: self.row(&f.row),
            })),
            Ty::Handler(h) => Ty::Handler(Box::new(crate::hir::HandlerTy {
                effect: self.effect(&h.effect),
                answer: h.answer.as_ref().map(|t| self.ty(t)),
                row: self.row(&h.row),
            })),
            Ty::Value(_) | Ty::Error => t.clone(),
        }
    }

    /// The elements of a tuple type, each spread whose pack the substitution replaces by a
    /// tuple of its elements standing for one element for each of them (variadics.type-spreads).
    fn elements(&self, ts: &[Ty]) -> Vec<Ty> {
        let mut out = Vec::new();
        for t in ts {
            let Ty::Spread(pack, elem) = t else {
                out.push(self.ty(t));
                continue;
            };
            match self.types.iter().find(|(q, _)| q == pack) {
                Some((_, Ty::Tuple(seq))) => {
                    for s in seq {
                        let (inner, spread) = match s {
                            Ty::Spread(q, e) => (&**e, Some(q)),
                            s => (s, None),
                        };
                        let mut types = self.types.clone();
                        types.retain(|(q, _)| q != pack);
                        types.push((pack.clone(), inner.clone()));
                        let one = Self {
                            types,
                            rows: Vec::new(),
                            self_ty: self.self_ty.clone(),
                        }
                        .ty(elem);
                        out.push(match spread {
                            Some(q) => Ty::Spread(q.clone(), Box::new(one)),
                            None => one,
                        });
                    }
                }
                Some((_, Ty::Param(q))) => {
                    out.push(Ty::Spread(q.clone(), Box::new(self.ty(elem))));
                }
                _ => out.push(Ty::Spread(pack.clone(), Box::new(self.ty(elem)))),
            }
        }
        out
    }

    /// The parameters of a function type, with their spreads substituted as a tuple's
    /// elements are.
    fn params(&self, params: &[(Mode, Ty)]) -> Vec<(Mode, Ty)> {
        let modes: Vec<Mode> = params.iter().map(|(m, _)| *m).collect();
        let types: Vec<Ty> = params.iter().map(|(_, t)| t.clone()).collect();
        let types = self.elements(&types);
        if types.len() == modes.len() {
            modes.into_iter().zip(types).collect()
        } else {
            types.into_iter().map(|t| (Mode::Let, t)).collect()
        }
    }

    /// An effect with its type arguments substituted.
    fn effect(&self, e: &crate::hir::EffectInst) -> crate::hir::EffectInst {
        crate::hir::EffectInst {
            effect: e.effect.clone(),
            args: e.args.iter().map(|a| self.ty(a)).collect(),
        }
    }

    fn effects(&self, es: &[crate::hir::EffectInst]) -> Vec<crate::hir::EffectInst> {
        es.iter().map(|e| self.effect(e)).collect()
    }

    /// A row with its raise substituted. A row variable that the substitution replaces gives
    /// way to the replacement, which gains the row's labels.
    pub(super) fn row(&self, r: &Row) -> Row {
        let raise = r.raise.as_ref().map(|t| Box::new(self.ty(t)));
        let replacement = r
            .var
            .as_ref()
            .and_then(|v| self.rows.iter().find(|(q, _)| q == v));
        match replacement {
            Some((_, replacement)) => Row {
                io: replacement.io || r.io,
                raise: replacement.raise.clone().or(raise),
                var: replacement.var.clone(),
                effects: merged_effects(&self.effects(&r.effects), &replacement.effects),
            },
            None => Row {
                io: r.io,
                raise,
                var: r.var.clone(),
                effects: self.effects(&r.effects),
            },
        }
    }
}

/// A constructor applied to `args` (traits.constructor-traits and traits.constructor-parameters): a
/// type constructor written without its arguments takes them, and a constructor parameter or `Self`
/// stays applied.
#[must_use]
pub(super) fn apply(head: Ty, args: Vec<Ty>) -> Ty {
    match head {
        Ty::Con(item, none) if none.is_empty() => Ty::Con(item, args),
        head @ (Ty::Param(_) | Ty::SelfTy) => Ty::App(Box::new(head), args),
        _ => Ty::Error,
    }
}

/// Whether two types are the same, the error type being the same as any.
pub(super) fn equal(a: &Ty, b: &Ty) -> bool {
    match (a, b) {
        (Ty::Error, _) | (_, Ty::Error) | (Ty::SelfTy, Ty::SelfTy) => true,
        (Ty::Con(i, xs), Ty::Con(j, ys)) => i == j && equal_all(xs, ys),
        (Ty::Param(p), Ty::Param(q)) => p == q,
        (Ty::App(f, xs), Ty::App(g, ys)) => equal(f, g) && equal_all(xs, ys),
        (Ty::Tuple(xs), Ty::Tuple(ys)) => equal_all(xs, ys),
        (Ty::Fn(f), Ty::Fn(g)) if !f.generics.is_empty() || !g.generics.is_empty() => {
            // Polymorphic function types are the same once their parameters are renamed in
            // order (polymorphism.instantiation).
            let same_bounds = f.generics.len() == g.generics.len()
                && f.generics.iter().zip(&g.generics).all(|((_, a), (_, b))| {
                    let traits = |bs: &[TraitRef]| -> BTreeSet<String> {
                        bs.iter().map(|b| format!("{b:?}")).collect()
                    };
                    traits(a) == traits(b)
                });
            let rename = Subst {
                types: g
                    .generics
                    .iter()
                    .zip(&f.generics)
                    .map(|((q, _), (p, _))| (q.clone(), Ty::Param(p.clone())))
                    .collect(),
                ..Subst::default()
            };
            let mono = |h: &crate::hir::FnTy| {
                Ty::Fn(Box::new(crate::hir::FnTy {
                    generics: Vec::new(),
                    ..h.clone()
                }))
            };
            same_bounds && equal(&mono(f), &rename.ty(&mono(g)))
        }
        (Ty::Fn(f), Ty::Fn(g)) => {
            f.params.len() == g.params.len()
                && f.params
                    .iter()
                    .zip(&g.params)
                    .all(|((m, x), (n, y))| m == n && equal(x, y))
                && equal(
                    f.ret.as_ref().unwrap_or(&unit_ty()),
                    g.ret.as_ref().unwrap_or(&unit_ty()),
                )
                && equal_row(&f.row, &g.row)
        }
        _ => false,
    }
}

fn equal_all(xs: &[Ty], ys: &[Ty]) -> bool {
    xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| equal(x, y))
}

fn equal_row(a: &Row, b: &Row) -> bool {
    a.io == b.io
        && match (&a.raise, &b.raise) {
            (None, None) => true,
            (Some(x), Some(y)) => equal(x, y),
            _ => false,
        }
        && a.var == b.var
}

/// traits.impl-signatures: whether an impl method's signature is the trait's, once `Self` is the
/// impl's type, each trait parameter the impl's argument for it (traits.trait-arguments), and the
/// method's generics correspond in order, with the same bounds and parameters written
/// `escaping`. The first `own` type parameters of `actual` are its impl block's.
pub(super) fn matches_trait(
    (self_ty, trait_args): (&Ty, &[(GenericId, Ty)]),
    expected: &FnSig,
    actual: &FnSig,
    own: usize,
) -> bool {
    let own_params = &actual.type_params[own.min(actual.type_params.len())..];
    if expected.type_params.len() != own_params.len()
        || expected.row_params.len() != actual.row_params.len()
    {
        return false;
    }
    let sub = trait_subst((self_ty, trait_args), expected, actual, own_params);
    let own_args: Vec<&BoundArgs> = actual
        .bound_args
        .iter()
        .filter(|b| own_params.iter().any(|(p, _)| *p == b.param))
        .collect();
    expected
        .type_params
        .iter()
        .zip(own_params)
        .all(|((_, a), (_, b))| a.iter().collect::<BTreeSet<_>>() == b.iter().collect())
        && expected.bound_args.len() == own_args.len()
        && expected.bound_args.iter().all(|b| {
            let param = sub.ty(&Ty::Param(b.param.clone()));
            own_args.iter().any(|c| {
                Ty::Param(c.param.clone()) == param
                    && c.trait_item == b.trait_item
                    && equal_all(&b.args.iter().map(|a| sub.ty(a)).collect::<Vec<_>>(), &c.args)
            })
        })
        && expected.params.len() == actual.params.len()
        && expected.passing == actual.passing
        && expected
            .params
            .iter()
            .zip(&actual.params)
            .all(|((m, a), (n, b))| m == n && equal(&sub.ty(a), b))
        && equal(&sub.ty(&expected.ret), &actual.ret)
        // A trait's projection is implemented by a projection, and a method that isn't by one
        // that isn't (projections.declaring-projection).
        && expected.projection == actual.projection
        && equal_row(&sub.row(&expected.row), &actual.row)
}

/// What a trait's signature `expected` becomes in an impl: `Self` the impl's type, the trait's
/// parameters its arguments, and the method's generics and row variables those of `actual`.
fn trait_subst(
    (self_ty, trait_args): (&Ty, &[(GenericId, Ty)]),
    expected: &FnSig,
    actual: &FnSig,
    own_params: &[(GenericId, Vec<crate::hir::Item>)],
) -> Subst {
    let mut types: Vec<(GenericId, Ty)> = trait_args.to_vec();
    types.extend(
        expected
            .type_params
            .iter()
            .zip(own_params)
            .map(|((v, _), (w, _))| (v.clone(), Ty::Param(w.clone()))),
    );
    Subst {
        self_ty: Some(self_ty.clone()),
        types,
        rows: expected
            .row_params
            .iter()
            .zip(&actual.row_params)
            .map(|(v, w)| {
                let row = Row {
                    var: Some(w.clone()),
                    ..Row::default()
                };
                (v.clone(), row)
            })
            .collect(),
    }
}

/// The effects of a row, then those of the row that replaces its variable that it lacks.
fn merged_effects(
    own: &[crate::hir::EffectInst],
    replacement: &[crate::hir::EffectInst],
) -> Vec<crate::hir::EffectInst> {
    let mut all = own.to_vec();
    for e in replacement {
        if !all.iter().any(|f| f.effect == e.effect) {
            all.push(e.clone());
        }
    }
    all
}
