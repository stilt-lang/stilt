//! Spreads of packs (variadics.packs, variadics.type-spreads and variadics.pack-inference): `..T`
//! among a tuple type's elements or a function type's parameters, which stands for one element for
//! each element of the pack it names.
//!
//! A spread holds its pack, the type parameter `of` that its element type names to stand for
//! each element, and that type. The pack is the type parameter itself in the body that declares
//! it, a variable at a use of its function, which a tuple of elements solves, or that tuple once
//! substituted; each element is a type, or a spread of another pack, which keeps that pack's
//! elements in place, as `(..Ts, i64)` gives `nest` a pack one element longer. A tuple type
//! whose spread's pack is a tuple is expanded, the spread giving way to one element for each of
//! the tuple's.

use stilt_hir::hir::{GenericId, Mode};

use super::{FnTy, Table, Ty};

/// `..elem`, one element for each element of `pack`, with `of` standing for it in `elem`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Spread {
    /// The pack.
    pub pack: Ty,
    /// The parameter that stands for an element in `elem`.
    pub of: GenericId,
    /// The type of each element.
    pub elem: Ty,
}

impl Ty {
    /// The spread of `pack` whose element type `elem` names `of` for each element. A spread of
    /// a type parameter names the parameter itself, so that two spreads of one pack are equal.
    #[must_use]
    pub fn spread(pack: Ty, of: GenericId, elem: Ty) -> Self {
        let (of, elem) = match &pack {
            Ty::Param(p) if *p != of => (p.clone(), replace(&elem, &of, &Ty::Param(p.clone()))),
            _ => (of, elem),
        };
        Self::Spread(Box::new(Spread { pack, of, elem }))
    }

    /// The spread, if the type is one.
    #[must_use]
    pub fn as_spread(&self) -> Option<&Spread> {
        match self {
            Self::Spread(s) => Some(s),
            _ => None,
        }
    }

    /// Whether a tuple type spreads a pack among its elements, so that its arity isn't known
    /// (variadics.pack-tuples).
    #[must_use]
    pub fn is_pack_tuple(&self) -> bool {
        matches!(self, Self::Tuple(ts) if ts.iter().any(|t| t.as_spread().is_some()))
    }

    /// The single spread of a pack tuple whose elements are all one spread's, as `(..List<Ts>)`.
    #[must_use]
    pub fn single_spread(&self) -> Option<&Spread> {
        match self {
            Self::Tuple(ts) => match ts.as_slice() {
                [only] => only.as_spread(),
                _ => None,
            },
            _ => None,
        }
    }
}

impl FnTy {
    /// Whether one of its parameters is a spread (variadics.type-spreads).
    #[must_use]
    pub fn has_spread(&self) -> bool {
        self.params.iter().any(|(_, t)| t.as_spread().is_some())
    }

    /// The types of its parameters.
    #[must_use]
    pub fn param_types(&self) -> Vec<Ty> {
        self.params.iter().map(|(_, t)| t.clone()).collect()
    }
}

/// `t` with the type parameter `of` replaced by `with`.
#[must_use]
pub fn replace(t: &Ty, of: &GenericId, with: &Ty) -> Ty {
    let r = |t: &Ty| replace(t, of, with);
    match t {
        Ty::Param(p) if p == of => with.clone(),
        Ty::Con(item, args) => Ty::Con(item.clone(), args.iter().map(r).collect()),
        Ty::App(head, args) => Ty::App(Box::new(r(head)), args.iter().map(r).collect()),
        Ty::Tuple(ts) => Ty::Tuple(ts.iter().map(r).collect()),
        Ty::Spread(s) => Ty::Spread(Box::new(Spread {
            pack: r(&s.pack),
            of: s.of.clone(),
            elem: if s.of == *of {
                s.elem.clone()
            } else {
                r(&s.elem)
            },
        })),
        Ty::Fn(f) => {
            let mut f = (**f).clone();
            f.params = f.params.iter().map(|(m, t)| (*m, r(t))).collect();
            f.ret = r(&f.ret);
            f.row.raise = f.row.raise.map(|t| Box::new(r(&t)));
            Ty::Fn(Box::new(f))
        }
        Ty::Handler(h) => {
            let mut h = (**h).clone();
            h.args = h.args.iter().map(r).collect();
            h.answer = h.answer.as_ref().map(r);
            Ty::Handler(Box::new(h))
        }
        Ty::Param(_) | Ty::SelfTy | Ty::Var(_) | Ty::Value(_) | Ty::Error => t.clone(),
    }
}

/// How [`Table::expand`] makes each element's type: given the type and the type parameter it
/// must leave as it is, a spread's own, if any.
pub(crate) type Each<'a> = dyn FnMut(&Table, &Ty, Option<&GenericId>) -> Ty + 'a;

impl Table {
    /// The elements `ts` of a tuple type or of a function type's parameters, each spread whose
    /// pack, as `pack` gives it, is a tuple expanded into its elements, and every element's
    /// type as `each` gives it, which leaves a spread's own type parameter for its elements to
    /// replace. `each` is given no spread's pack, nor the elements that a pack's tuple holds,
    /// which are as they are.
    pub(crate) fn expand(
        &self,
        ts: &[Ty],
        pack: &mut dyn FnMut(&Self, &Ty) -> Ty,
        each: &mut Each<'_>,
    ) -> Vec<Ty> {
        let mut out = Vec::new();
        for t in ts {
            let Ty::Spread(s) = t else {
                out.push(each(self, t, None));
                continue;
            };
            let p = pack(self, &s.pack);
            let elem = each(self, &s.elem, Some(&s.of));
            self.place(&mut out, p, &s.of, &elem);
        }
        out
    }

    /// Pushes onto `out` the elements of the spread of `pack` whose element type `elem` names
    /// `of`: the spread itself while its pack isn't a tuple, and otherwise one element for each
    /// of the tuple's, a spread among them placed again, so that a pack solved in turn by
    /// another's tuple is expanded too.
    fn place(&self, out: &mut Vec<Ty>, pack: Ty, of: &GenericId, elem: &Ty) {
        let Ty::Tuple(seq) = self.resolve(&pack).clone() else {
            out.push(Ty::spread(pack, of.clone(), elem.clone()));
            return;
        };
        for element in seq {
            match element {
                Ty::Spread(inner) => {
                    let e = replace(elem, of, &inner.elem);
                    self.place(out, inner.pack.clone(), &inner.of, &e);
                }
                element => out.push(replace(elem, of, &element)),
            }
        }
    }

    /// The elements of a tuple type, its spreads whose packs are solved expanded, the others
    /// as they are.
    #[must_use]
    pub fn elements(&self, ts: &[Ty]) -> Vec<Ty> {
        self.expand(ts, &mut |_, p| p.clone(), &mut |_, t, _| t.clone())
    }

    /// The parameters of a function type, expanded as a tuple's elements are, each spread's
    /// elements taking a parameter without a mode.
    pub(crate) fn expand_params(
        &self,
        params: &[(Mode, Ty)],
        pack: &mut dyn FnMut(&Self, &Ty) -> Ty,
        each: &mut Each<'_>,
    ) -> Vec<(Mode, Ty)> {
        let mut out = Vec::new();
        for (m, t) in params {
            if t.as_spread().is_some() {
                let types = self.expand(std::slice::from_ref(t), pack, each);
                out.extend(types.into_iter().map(|t| (Mode::Let, t)));
            } else {
                out.push((*m, each(self, t, None)));
            }
        }
        out
    }
}
