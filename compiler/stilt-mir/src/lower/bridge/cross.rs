//! The functions that convert a value of a recursive type or a closure into code past the caps
//! and back (`super`), keyed by the type's structure ([`Cross`]): a function made for that
//! structure, over generics made up for its leaves, each with the witness of the type it stands
//! for, which the code that calls it, or the closure that holds it, gives in the order of the
//! leaves.

use stilt_hir::hir::{GenericId, Item};
use stilt_types::ty::{FnTy, Row, Ty};

use super::Dir;
use crate::lower::Lower;
use crate::lower::calls::Target;
use crate::lower::keys::key_word;
use crate::lower::words::word;
use crate::mir::{Arg, Const, Heapness, Local, Operand, ParamMode, Repr};
use crate::{Cross, FnRef, Held, Word};

/// Where the witnesses of the leaves of a structure are: in the function's parameters, or in a
/// closure's fields from `next` on, of `len` in all.
pub(crate) enum Witnesses {
    Params,
    Env { env: Local, len: u32, next: u32 },
}

/// How a generic made up for a leaf of these words holds its values.
pub(crate) fn held_of_words(words: &[Word]) -> Held {
    if matches!(words, [w] if !matches!(w, Word::Array(_))) {
        Held::Word
    } else {
        Held::Words(words.into())
    }
}

impl Lower<'_> {
    /// The words of the layout of a type, as a key says them.
    pub(crate) fn key_words(&self, ty: &Ty) -> Box<[Word]> {
        self.layout(ty).into_iter().map(key_word).collect()
    }

    /// The structure of a type that converts from `n` outside to `u` past the caps, and the
    /// witnesses of its leaves, in order.
    pub(crate) fn cross_of(&mut self, n: &Ty, u: &Ty, witnesses: &mut Vec<Operand>) -> Cross {
        // A type parameter of a polymorphic function type has the witness that each call gives.
        if let Some(k) = self.rigid.iter().position(|t| t == n) {
            return Cross::Rigid(u32::try_from(k).expect("under 4G type parameters"));
        }
        if let Some(inner) = self.crossing_of(u) {
            let c = self.cross_of(n, &inner, witnesses);
            witnesses.push(self.witness(&inner));
            return Cross::Boxed(Box::new(c));
        }
        if !self.converts(n, u) {
            witnesses.push(self.witness(n));
            return Cross::Same(self.key_words(n));
        }
        match (n, u) {
            (Ty::Fn(nf), Ty::Fn(uf)) if nf.is_poly() => self.cross_of_poly(nf, uf, witnesses),
            (Ty::Tuple(ns), Ty::Tuple(us)) => Cross::Tuple(
                ns.iter()
                    .zip(us)
                    .map(|(n, u)| self.cross_of(n, u, witnesses))
                    .collect(),
            ),
            (Ty::Con(item, ns), Ty::Con(_, us)) => Cross::Con(
                item.clone(),
                ns.iter()
                    .zip(us)
                    .map(|(n, u)| self.cross_of(n, u, witnesses))
                    .collect(),
            ),
            (Ty::Fn(nf), Ty::Fn(uf)) => {
                let params = nf
                    .params
                    .iter()
                    .zip(&uf.params)
                    .map(|((m, n), (_, u))| {
                        let inout = *m == stilt_hir::hir::Mode::Inout;
                        (inout, self.cross_of(n, u, witnesses))
                    })
                    .collect();
                let ret = self.cross_of(&nf.ret, &uf.ret, witnesses);
                let err = match (&nf.row.raise, &uf.row.raise) {
                    (Some(n), Some(u)) => Some(Box::new(self.cross_of(n, u, witnesses))),
                    _ => None,
                };
                Cross::Fn(params, Box::new(ret), err)
            }
            _ => {
                witnesses.push(self.witness(n));
                Cross::Same(self.key_words(n))
            }
        }
    }

    /// The structure of a polymorphic function type `nf` outside, `uf` past the caps: its
    /// function type's, in which its type parameters are rigid.
    fn cross_of_poly(&mut self, nf: &FnTy, uf: &FnTy, witnesses: &mut Vec<Operand>) -> Cross {
        let depth = self.rigid.len();
        self.rigid
            .extend(nf.generics.iter().map(|(g, _)| Ty::Param(g.clone())));
        let (n, u) = (Ty::Fn(Box::new(nf.body())), Ty::Fn(Box::new(uf.body())));
        let body = self.cross_of(&n, &u, witnesses);
        self.rigid.truncate(depth);
        let bounds = nf
            .generics
            .iter()
            .map(|(_, traits)| traits.clone().into_boxed_slice())
            .collect();
        Cross::Poly(bounds, Box::new(body))
    }

    /// The next witness of a structure's leaves, from `from`.
    fn next_witness(&mut self, from: &mut Witnesses) -> Local {
        match from {
            Witnesses::Params => self.b.param(Repr::Scalar, ParamMode::Borrowed, None),
            Witnesses::Env { env, len, next } => {
                let w = self.borrowed_field(*env, *len, *next, Repr::Scalar);
                *next += 1;
                w
            }
        }
    }

    /// The types a structure stands for, outside and past the caps, over generics made up for
    /// its leaves and brought into scope, with their witnesses from `from`.
    pub(crate) fn cross_types(&mut self, c: &Cross, from: &mut Witnesses) -> (Ty, Ty) {
        match c {
            Cross::Same(words) => {
                let witness = self.next_witness(from);
                let n = self.cross_generic();
                self.push_generic(n.clone(), witness, Vec::new(), Some(&held_of_words(words)));
                (n.clone(), n)
            }
            Cross::Boxed(c) => {
                let (n, inner) = self.cross_types(c, from);
                let witness = self.next_witness(from);
                let u = self.cross_generic();
                self.push_generic(u.clone(), witness, Vec::new(), Some(&Held::Word));
                self.crossing.push((u.clone(), inner));
                (n, u)
            }
            Cross::Tuple(cs) => {
                let (ns, us) = cs.iter().map(|c| self.cross_types(c, from)).unzip();
                (Ty::Tuple(ns), Ty::Tuple(us))
            }
            Cross::Rigid(k) => {
                let t = self.rigid[*k as usize].clone();
                (t.clone(), t)
            }
            Cross::Poly(bounds, body) => self.poly_types(bounds, body, from),
            Cross::Con(item, cs) => {
                let (ns, us) = cs.iter().map(|c| self.cross_types(c, from)).unzip();
                (Ty::Con(item.clone(), ns), Ty::Con(item.clone(), us))
            }
            Cross::Fn(ps, ret, err) => {
                let mut np = Vec::new();
                let mut up = Vec::new();
                for (inout, c) in ps {
                    let mode = if *inout {
                        stilt_hir::hir::Mode::Inout
                    } else {
                        stilt_hir::hir::Mode::Let
                    };
                    let (n, u) = self.cross_types(c, from);
                    np.push((mode, n));
                    up.push((mode, u));
                }
                let (nr, ur) = self.cross_types(ret, from);
                let errs = err.as_ref().map(|e| self.cross_types(e, from));
                let fty = |params, ret, raise: Option<Ty>| {
                    Ty::Fn(Box::new(FnTy {
                        generics: Vec::new(),
                        bound_args: Vec::new(),
                        params,
                        ret,
                        row: Row {
                            raise: raise.map(Box::new),
                            ..Row::EMPTY
                        },
                    }))
                };
                let (ne, ue) = errs.map_or((None, None), |(n, u)| (Some(n), Some(u)));
                (fty(np, nr, ne), fty(up, ur, ue))
            }
        }
    }

    /// The types a polymorphic function type's structure stands for, with type parameters made
    /// up for it, of the bounds `bounds`.
    fn poly_types(
        &mut self,
        bounds: &[Box<[Item]>],
        body: &Cross,
        from: &mut Witnesses,
    ) -> (Ty, Ty) {
        let depth = self.rigid.len();
        let generics: Vec<(GenericId, Vec<Item>)> = bounds
            .iter()
            .map(|traits| {
                let Ty::Param(g) = self.cross_generic() else {
                    unreachable!("a made-up generic is a type parameter")
                };
                (g, traits.to_vec())
            })
            .collect();
        self.rigid
            .extend(generics.iter().map(|(g, _)| Ty::Param(g.clone())));
        let (n, u) = self.cross_types(body, from);
        self.rigid.truncate(depth);
        let poly = |t: Ty| match t {
            Ty::Fn(f) => Ty::Fn(Box::new(FnTy {
                generics: generics.clone(),
                ..*f
            })),
            t => t,
        };
        (poly(n), poly(u))
    }

    /// A value of a recursive type whose nodes hold a crossing argument, its nodes rebuilt by
    /// the function made for its structure.
    pub(crate) fn rebuild(
        &mut self,
        words: Vec<Operand>,
        n: &Ty,
        u: &Ty,
        dir: Dir,
    ) -> Vec<Operand> {
        let mut witnesses = Vec::new();
        let cross = self.cross_of(n, u, &mut witnesses);
        let f = FnRef::Rebuild(Box::new(cross), dir == Dir::In);
        let hidden = witnesses.into_iter().map(Arg::Borrow).collect();
        let to = if dir == Dir::In { u } else { n };
        let values = words.into_iter().map(Arg::Borrow).collect();
        let loc = Operand::Local(self.loc);
        self.emit_call(
            Target::Direct(f, hidden),
            values,
            &[],
            loc,
            false,
            to,
            &Row::EMPTY,
        )
    }

    /// A closure held by one that converts what it takes and gives, whose code is made for the
    /// closure's type's structure, and which holds the witnesses of its leaves.
    pub(crate) fn adapt(&mut self, words: &[Operand], n: &Ty, u: &Ty, dir: Dir) -> Vec<Operand> {
        let mut witnesses = Vec::new();
        let cross = self.cross_of(n, u, &mut witnesses);
        let code = FnRef::Adapt(Box::new(cross), dir == Dir::In);
        let mut env = vec![
            (Operand::Const(Const::Code(code)), Heapness::Static(false)),
            (word(words, 0), Heapness::Static(true)),
        ];
        env.extend(witnesses.into_iter().map(|w| (w, Heapness::Static(false))));
        vec![self.alloc(0, env)]
    }
}
