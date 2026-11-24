//! Whether a type implements a trait, through an impl block or structurally
//! (traits.structural-impls; std.map-key-bounds and traits.hash-follows-written-eq), for types that
//! inference may not have decided yet.

use stilt_hir::decls::Lookup;
use stilt_hir::decls::{ImplInfo, TypeDefInfo, prelude_item};
use stilt_hir::hir::{self, Item};

use stilt_hir::hir::GenericId;

use crate::params::{Args, TraitArgs, instantiated};
use crate::ty::{Table, Ty, instantiate, is_prelude};

/// The rigid types of a body, its type parameters and `Self`, each with the traits that bound it. A
/// bound with an error is left out, since the error type satisfies every bound (errors.error-type).
pub type Bounds = Vec<(Ty, Vec<Item>)>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Answer {
    Yes,
    No,
    /// It depends on a type variable that isn't solved yet.
    Unknown,
}

fn all(answers: impl IntoIterator<Item = Answer>) -> Answer {
    let answers: Vec<_> = answers.into_iter().collect();
    if answers.contains(&Answer::No) {
        Answer::No
    } else if answers.contains(&Answer::Unknown) {
        Answer::Unknown
    } else {
        Answer::Yes
    }
}

/// The traits that types implement structurally (traits.structural-impls).
pub(crate) fn structural(trait_item: &Item) -> bool {
    &*trait_item.home == "std.prelude" && ["Eq", "Ord", "Hash", "Show"].contains(&&*trait_item.name)
}

/// Where trait implementations are looked up: the declarations, the arguments the bounds in
/// scope give traits with parameters, and the variables of the body.
pub(crate) struct Traits<'a> {
    pub(crate) decls: &'a dyn Lookup,
    pub(crate) scope: &'a [crate::params::BoundArg],
    pub(crate) table: &'a Table,
}

impl Traits<'_> {
    /// Whether `ty` implements `trait_item`, where the rigid types have `bounds`. The error type
    /// implements every trait.
    pub(crate) fn implements(&self, bounds: &Bounds, ty: &Ty, trait_item: &Item) -> Answer {
        self.implements_in(bounds, &[], ty, trait_item)
    }

    fn implements_in(
        &self,
        bounds: &Bounds,
        visiting: &[(Item, Item)],
        ty: &Ty,
        trait_item: &Item,
    ) -> Answer {
        let each = |ts: &[Ty]| {
            all(ts
                .iter()
                .map(|t| self.implements_in(bounds, visiting, t, trait_item)))
        };
        match &self.table.shape(ty) {
            Ty::Error => Answer::Yes,
            Ty::Var(_) => Answer::Unknown,
            // A constructor parameter applied implements the traits over types that its
            // constructor's impls give, which the bounds don't tell
            // (traits.constructor-parameters).
            Ty::App(head, _) if self.table.unsolved(head).is_some() => Answer::Unknown,
            rigid @ (Ty::Param(_) | Ty::SelfTy) => {
                if bounds
                    .iter()
                    .any(|(v, traits)| v == rigid && traits.contains(trait_item))
                {
                    Answer::Yes
                } else {
                    Answer::No
                }
            }
            Ty::Tuple(ts) if structural(trait_item) => each(ts),
            // A spread's elements meet a bound when its element type does, which names its
            // pack, whose bounds its elements meet (variadics.pack-tuples).
            Ty::Spread(s) if self.table.unsolved(&s.pack).is_some() => Answer::Unknown,
            Ty::Spread(s) => self.implements_in(bounds, visiting, &s.elem, trait_item),
            Ty::App(..) | Ty::Fn(_) | Ty::Handler(_) | Ty::Tuple(_) | Ty::Value(_) => Answer::No,
            Ty::Con(item, args) => match self.decls.trait_impl(trait_item, item) {
                Some(impl_info) => {
                    self.through_impl(bounds, visiting, impl_info, &self.table.shape(ty))
                }
                None if !structural(trait_item) => Answer::No,
                // traits.hash-follows-written-eq: a written `Eq` takes the automatic `Hash` away.
                None if is_prelude(trait_item, "Hash")
                    && self.decls.trait_impl(&prelude_item("Eq"), item).is_some() =>
                {
                    Answer::No
                }
                None if visiting.contains(&(item.clone(), trait_item.clone())) => Answer::Yes,
                None => self.structurally(bounds, visiting, item, args, trait_item),
            },
        }
    }

    /// Whether the type `ty` meets the bounds of the generics of `impl_info`, the impl block
    /// that the program writes for its constructor, the member types its bounds give among them
    /// (traits.member-types), and whether the impl's bounds' traits are given their arguments.
    fn through_impl(
        &self,
        bounds: &Bounds,
        visiting: &[(Item, Item)],
        impl_info: &ImplInfo,
        ty: &Ty,
    ) -> Answer {
        let args = Args {
            decls: self.decls,
            scope: self.scope,
            table: self.table,
        };
        let targs = args.impl_targs(impl_info, ty);
        let of = |v: &GenericId| {
            impl_info
                .generics
                .iter()
                .position(|(w, _)| w == v)
                .and_then(|i| targs.get(i))
        };
        let given = impl_info.bound_args.iter().map(|b| {
            let Some(arg) = of(&b.param) else {
                return Answer::Yes;
            };
            let wanted = instantiated(impl_info, &targs, &b.args);
            match args.of(arg, &b.trait_item) {
                TraitArgs::Known(actual) => self.same(&wanted, &actual),
                TraitArgs::Unknown => Answer::Unknown,
                TraitArgs::Missing => Answer::No,
            }
        });
        let met = impl_info
            .generics
            .iter()
            .zip(&targs)
            .flat_map(|((_, traits), arg)| {
                traits
                    .iter()
                    .map(move |t| self.implements_in(bounds, visiting, arg, t))
            });
        all(met.chain(given).collect::<Vec<_>>())
    }

    /// Whether two lists of types are the same, as far as the variables solved so far tell.
    pub(crate) fn same(&self, xs: &[Ty], ys: &[Ty]) -> Answer {
        let one = |x: &Ty, y: &Ty| {
            let (x, y) = (self.table.freeze(x), self.table.freeze(y));
            if x == y || x == Ty::Error || y == Ty::Error {
                Answer::Yes
            } else if holds_var(&x) || holds_var(&y) {
                Answer::Unknown
            } else {
                Answer::No
            }
        };
        all(xs
            .iter()
            .zip(ys)
            .map(|(x, y)| one(x, y))
            .collect::<Vec<_>>())
    }

    /// Whether the type constructor `item`, applied to `args`, implements the structural
    /// `trait_item` without an impl block, through what its values hold.
    fn structurally(
        &self,
        bounds: &Bounds,
        visiting: &[(Item, Item)],
        item: &Item,
        args: &[Ty],
        trait_item: &Item,
    ) -> Answer {
        let Some(info) = self.decls.type_info(item) else {
            return Answer::Yes;
        };
        // A value argument is no type, and holds no trait: an array meets a structural trait
        // when its element type does (generics.array-traits).
        let each = || {
            all((0..)
                .zip(args)
                .filter(|(i, _)| !info.values.iter().any(|(v, _)| v == i))
                .map(|(_, t)| self.implements_in(bounds, visiting, t, trait_item)))
        };
        let inside: Vec<(Item, Item)> = std::iter::once((item.clone(), trait_item.clone()))
            .chain(visiting.iter().cloned())
            .collect();
        let held = |ts: &mut dyn Iterator<Item = &hir::Ty>| {
            all(ts
                .map(|t| instantiate(t, &info.params, args))
                .collect::<Vec<_>>()
                .iter()
                .map(|t| self.implements_in(bounds, &inside, t, trait_item)))
        };
        match &info.def {
            // std.map-key-bounds: comparing maps finds keys, so it needs the key type's `Hash`
            // too.
            TypeDefInfo::Builtin if is_prelude(item, "Map") && is_prelude(trait_item, "Eq") => {
                let key = self.implements_in(bounds, visiting, &args[0], &prelude_item("Hash"));
                all([each(), key])
            }
            TypeDefInfo::Builtin if builtin_has(item, trait_item) => each(),
            TypeDefInfo::Builtin => Answer::No,
            TypeDefInfo::Record(fields) => held(&mut fields.iter().map(|(_, t)| t)),
            TypeDefInfo::Variants(variants) => {
                held(&mut variants.iter().flat_map(|(_, payload)| payload))
            }
        }
    }

    /// Whether a type constructor has a structural impl of a trait: whether its type would
    /// implement it with every type parameter implementing it (traits.structural-impls).
    fn structural_impl(&self, item: &Item, trait_item: &Item) -> bool {
        structural(trait_item)
            && self.decls.type_info(item).is_some_and(|info| {
                let params: Vec<Ty> = info.params.iter().cloned().map(Ty::Param).collect();
                let bounds = params
                    .iter()
                    .map(|p| (p.clone(), vec![trait_item.clone()]))
                    .collect();
                let ty = Ty::Con(item.clone(), params);
                self.implements(&bounds, &ty, trait_item) == Answer::Yes
            })
    }

    /// Whether the head constructor of `ty`, a named type or a tuple, has an impl of
    /// `trait_item`, written or structural, whatever the bounds of that impl ask of its
    /// arguments (traits.method-resolution).
    pub(crate) fn has_impl(&self, ty: &Ty, trait_item: &Item) -> bool {
        match &self.table.shape(ty) {
            Ty::Con(item, _) => {
                self.decls.trait_impl(trait_item, item).is_some()
                    || self.structural_impl(item, trait_item)
            }
            Ty::Tuple(_) => structural(trait_item),
            Ty::Handler(_)
            | Ty::Param(_)
            | Ty::SelfTy
            | Ty::App(..)
            | Ty::Fn(_)
            | Ty::Spread(_)
            | Ty::Var(_)
            | Ty::Value(_)
            | Ty::Error => false,
        }
    }
}

/// traits.built-in-impls and traits.floats: floats have no `Hash`, and maps no `Ord` or `Hash`.
fn builtin_has(item: &Item, trait_item: &Item) -> bool {
    match &*item.name {
        "f32" | "f64" => !is_prelude(trait_item, "Hash"),
        "Map" => is_prelude(trait_item, "Eq") || is_prelude(trait_item, "Show"),
        // views.iterator-traits: iterators have none of the structural traits,
        // polymorphism.lazy-unobservable: nor do lazy values, which they would compute unseen,
        // and meta.std-meta: nor do shapes, which have no written representation.
        "Iter" if &*item.home == "std.view" => false,
        "Lazy" if &*item.home == "std.lazy" => false,
        "Shape" if &*item.home == "std.meta" => false,
        _ => true,
    }
}

/// Whether a type of a typed body implements a trait, where the type parameters and `Self`
/// have `bounds`, whose traits with parameters they give `scope`. The backend asks it to build
/// the dictionaries of structural impls.
#[must_use]
pub fn implements_trait(
    decls: &dyn Lookup,
    (bounds, scope): (&Bounds, &[crate::params::BoundArg]),
    ty: &Ty,
    trait_item: &Item,
) -> bool {
    let table = Table::default();
    Traits {
        decls,
        scope,
        table: &table,
    }
    .implements(bounds, ty, trait_item)
        == Answer::Yes
}

/// Whether a frozen type holds a variable.
fn holds_var(t: &Ty) -> bool {
    match t {
        Ty::Var(_) => true,
        Ty::Con(_, ts) | Ty::Tuple(ts) => ts.iter().any(holds_var),
        Ty::App(head, ts) => holds_var(head) || ts.iter().any(holds_var),
        Ty::Fn(f) => f.params.iter().any(|(_, t)| holds_var(t)) || holds_var(&f.ret),
        Ty::Spread(s) => holds_var(&s.pack) || holds_var(&s.elem),
        Ty::Handler(h) => h.args.iter().chain(&h.answer).any(holds_var),
        Ty::Param(_) | Ty::SelfTy | Ty::Value(_) | Ty::Error => false,
    }
}
