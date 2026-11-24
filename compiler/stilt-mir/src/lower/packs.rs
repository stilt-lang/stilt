//! Packs: a generic function is compiled once for each arity of its packs
//! that a call reaches. The instance's key gives each pack the keys of its elements
//! ([`Held::Pack`]); each element is a generic of its own, with its witness and the
//! dictionaries of the pack's bounds, and the instance's code is retyped with the pack the
//! tuple of its elements, which expands every spread of it. A spread's body is lowered once
//! for each element, retyped with the spread's type parameter that element, and with each pack
//! tuple it maps bound to that element's words.
//!
//! A pack whose length grows within its own cycle of the call graph, which only polymorphic
//! recursion does, would have instances without end: its length is known at run time only
//! (`dynamic`).

mod convert;
mod dynamic;
mod types;

pub(crate) use dynamic::is_dynamic_tuple;
pub(crate) use types::{components, has_pack};

use stilt_hir::decls::Lookup;
use stilt_hir::hir::{DeclId, GenericId, Item, LocalId, Owner};
use stilt_types::tast::retype::Retype;
use stilt_types::tast::{self, Expr, ExprKind, SpreadExpr};
use stilt_types::ty::{Row, Subst, Table, Ty};

use super::{Lower, Var};
use crate::mir::{Arg, Local, Operand, Repr, Rvalue};
use crate::{FnRef, Held};

/// The generic that stands for element `i` of the pack `g`, in an instance compiled for its
/// arity.
pub(crate) fn pack_element(g: &GenericId, i: usize) -> GenericId {
    let i = u32::try_from(i).expect("under 4G elements");
    GenericId {
        owner: Owner {
            decl: DeclId {
                module: format!(
                    "#pack:{}:{}:{}",
                    g.owner.decl.module, g.owner.decl.index, g.index
                )
                .into(),
                index: g.owner.member.unwrap_or(u32::MAX),
            },
            member: None,
        },
        index: i,
    }
}

/// The type of a local that a spread's body names, as it stands for its element there.
fn local_type(body: &Expr, v: LocalId) -> Option<Ty> {
    let mut found = None;
    tast::walk::iter(body, &mut |_| {}, &mut |e| {
        if found.is_none()
            && let ExprKind::Local(w) = e.kind
            && w == v
        {
            found = Some(e.ty.clone());
        }
    });
    found
}

/// The elements of a pack's tuple, or `None` while a spread of a pack that no instance expands
/// is among them.
pub(crate) fn static_elements(pack: &Ty) -> Option<Vec<Ty>> {
    match pack {
        Ty::Tuple(ts) => {
            let ts = Table::default().elements(ts);
            ts.iter().all(|t| t.as_spread().is_none()).then_some(ts)
        }
        _ => None,
    }
}

/// The type constructor of a structural impl, or of a dictionary's entry of one.
fn structural_con(f: &FnRef) -> Option<&Item> {
    match f {
        FnRef::Structural(_, _, crate::items::Shape::Con(item)) => Some(item),
        FnRef::Entry(imp, _) => match &**imp {
            crate::items::ImplRef::Structural {
                shape: crate::items::Shape::Con(item),
                ..
            } => Some(item),
            crate::items::ImplRef::Structural { .. } | crate::items::ImplRef::Written { .. } => {
                None
            }
        },
        _ => None,
    }
}

impl Lower<'_> {
    /// The packs among the generics of `f`, in the order of its hidden parameters.
    pub(crate) fn pack_positions(&self, f: &FnRef) -> Vec<bool> {
        let decls = self.decls();
        let g = f.generic();
        let mut out = Vec::new();
        if let FnRef::DefaultMethod(t, _) = g {
            let params = decls.trait_info(t).map_or(0, |i| i.params.len());
            out.extend(std::iter::repeat_n(false, 1 + params));
        }
        // A structural impl of a type with a pack, and its dictionary's entries.
        if let Some(item) = structural_con(g) {
            let n = decls.type_info(item).map_or(0, |t| t.params.len());
            let pack = has_pack(&decls, item);
            out.extend((0..n).map(|i| pack && i + 1 == n));
            return out;
        }
        if let Some(sig) = super::functions::signature(&decls, g) {
            let packs = sig.packs();
            out.extend(sig.type_params.iter().map(|(p, _)| packs.contains(p)));
        }
        out
    }

    /// The key of a pack instantiated with the tuple `ty`: its elements' keys, or a pack whose
    /// length the instance takes at run time.
    pub(crate) fn pack_key(&self, f: &FnRef, ty: &Ty, needs: &[Item], capped: bool) -> Held {
        match static_elements(ty) {
            Some(es) if !self.is_dynamic_at(ty, Some(f)) => Held::Pack(Some(
                es.iter().map(|e| self.key(e, needs, capped)).collect(),
            )),
            _ => Held::Word,
        }
    }

    /// Takes the next generic of the instance's key as the pack `g`'s, bounded by `traits`.
    pub(crate) fn add_pack_param(&mut self, g: &GenericId, traits: &[Item]) {
        let index = self.key_index();
        self.cons.taken += 1;
        match self.held.get(index).cloned() {
            Some(Held::Pack(Some(elements))) => {
                let mut types = Vec::new();
                for (i, key) in elements.iter().enumerate() {
                    let e = Ty::Param(pack_element(g, i));
                    self.add_generic_held(e.clone(), traits, Some(key));
                    self.cons.extra += 1;
                    types.push(e);
                }
                self.cons.params.push((g.clone(), Ty::Tuple(types)));
            }
            _ => self.add_dynamic_pack(g, traits),
        }
    }

    /// The hidden arguments of a pack bounded by `traits` instantiated with the tuple `ty`: each
    /// element's witness and dictionaries, or for a pack whose length is known at run time
    /// only, its lists of them.
    pub(crate) fn pack_args(&mut self, traits: &[Item], ty: &Ty, dynamic: bool) -> Vec<Arg> {
        let traits = super::records::dict_bounds(traits);
        match static_elements(ty) {
            Some(es) if !dynamic => es
                .iter()
                .flat_map(|e| self.bound_witness(&traits, e))
                .collect(),
            _ => self.dynamic_pack_args(&traits, ty),
        }
    }

    /// The packs of a signature, each with whether the code that a call with the type
    /// arguments `targs` reaches takes its length at run time: a pack instantiated with a
    /// tuple that spreads such a pack, or, for a call of `f` within this function's cycle of the
    /// call graph, one longer than any of this instance's own, which would grow its instances
    /// without end.
    pub(crate) fn pack_kinds(
        &self,
        sig: &stilt_hir::decls::FnSig,
        targs: &[Ty],
        f: Option<&FnRef>,
    ) -> Vec<(GenericId, bool)> {
        let packs = sig.packs();
        sig.type_params
            .iter()
            .zip(targs)
            .filter(|((g, _), _)| packs.contains(g))
            .map(|((g, _), t)| (g.clone(), self.is_dynamic_at(t, f)))
            .collect()
    }

    /// Whether a pack instantiated with `ty` in a call of `f` takes its length at run time.
    pub(crate) fn is_dynamic_at(&self, ty: &Ty, f: Option<&FnRef>) -> bool {
        let Some(es) = static_elements(ty) else {
            return true;
        };
        let own = self
            .held
            .iter()
            .filter_map(|h| match h {
                Held::Pack(Some(es)) => Some(es.len()),
                _ => None,
            })
            .max()
            .unwrap_or(0);
        es.len() > own && f.is_some_and(|f| self.in_cycle(f))
    }

    /// The substitution that retypes a spread's body for one element: the code's own, with
    /// the spread's type parameter `of` standing for `element`, and the type parameter of each
    /// spread around it for its element.
    fn element_subst(&self, of: &GenericId, element: Ty) -> Subst {
        let mut types: Vec<(GenericId, Ty)> = self
            .cons
            .params
            .iter()
            .filter(|(g, _)| g != of && self.elements.iter().all(|(h, _)| h != g))
            .cloned()
            .collect();
        types.extend(self.elements.iter().filter(|(h, _)| h != of).cloned());
        types.push((of.clone(), element));
        Subst {
            self_ty: self.cons.self_ty.clone(),
            types,
            rows: Vec::new(),
        }
    }

    /// The value of each element of a spread, in order, with its type: its body lowered once
    /// for each element of its pack (variadics.spread-expressions).
    pub(crate) fn spread_values(&mut self, s: &SpreadExpr) -> Vec<(Vec<Operand>, Ty)> {
        let Some(elements) = static_elements(&self.cons.ty(&s.pack)) else {
            return vec![self.dynamic_spread(s)];
        };
        // A spread among a call's arguments, or a tuple's or a list's that the instance knows.
        let mapped: Vec<(LocalId, Ty)> = s
            .mapped
            .iter()
            .filter_map(|v| local_type(&s.body, *v).map(|t| (*v, t)))
            .collect();
        let mut tuples = Vec::new();
        for (v, t) in &mapped {
            let each: Vec<Ty> = elements
                .iter()
                .map(|e| self.retyped_with(t, &s.of, e.clone()))
                .collect();
            let words = self.read_var(*v, &Ty::Tuple(each.clone()));
            let var = self.var(*v, &Ty::Tuple(each.clone()));
            tuples.push((*v, words, each, var));
        }
        let mut offsets = vec![0; tuples.len()];
        let mut values = Vec::new();
        for (i, element) in elements.iter().enumerate() {
            for (k, (v, words, each, _)) in tuples.iter().enumerate() {
                let layout = self.layout(&each[i]);
                let slice = words[offsets[k]..offsets[k] + layout.len()].to_vec();
                offsets[k] += layout.len();
                let locals = self.locals_of(slice, &layout);
                self.vars.insert(
                    *v,
                    Var::Value {
                        locals,
                        mutable: false,
                    },
                );
            }
            values.push(self.element_value(s, element.clone()));
        }
        for (v, _, _, var) in tuples {
            self.vars.insert(v, var);
        }
        values
    }

    /// The value of a spread's body for one element, and its type.
    fn element_value(&mut self, s: &SpreadExpr, element: Ty) -> (Vec<Operand>, Ty) {
        let body = self.body_for(s, element.clone());
        self.elements.push((s.of.clone(), element));
        let words = self.expr(&body);
        self.elements.pop();
        (words, body.ty)
    }

    /// A spread's body retyped for one element.
    pub(crate) fn body_for(&self, s: &SpreadExpr, element: Ty) -> Expr {
        let subst = self.element_subst(&s.of, element);
        let mut body = s.body.clone();
        let ty = |t: &Ty| Table::default().subst(&subst, t);
        let row = |r: &Row| Table::default().subst_row(&subst, r);
        Retype {
            ty: &ty,
            row: &row,
            spreads: false,
        }
        .expr(&mut body);
        body
    }

    /// A type that a spread's body names, with its type parameter `of` standing for `element`
    /// and the code's own substitution.
    pub(crate) fn retyped_with(&self, t: &Ty, of: &GenericId, element: Ty) -> Ty {
        Table::default().subst(&self.element_subst(of, element), t)
    }

    /// Locals that hold `words`, of the representations `layout` gives, which later code reads.
    pub(crate) fn locals_of(&mut self, words: Vec<Operand>, layout: &[Repr]) -> Vec<Local> {
        words
            .into_iter()
            .zip(layout)
            .map(|(w, r)| match w {
                Operand::Local(l) => l,
                c @ Operand::Const(_) => self.b.define(*r, Rvalue::Use(c)),
            })
            .collect()
    }

    /// A spread that no tuple, list or call holds, which lowering never meets: each of those
    /// lowers the spreads among its elements.
    pub(crate) fn stray_spread(&mut self) -> Vec<Operand> {
        self.b.met_error();
        vec![Operand::word(0)]
    }

    /// The values of the elements of a tuple, a list or a call, each spread's one for each of
    /// its pack's elements.
    pub(crate) fn element_values(&mut self, es: &[Expr]) -> Vec<(Vec<Operand>, Ty)> {
        let mut out = Vec::new();
        for e in es {
            match &e.kind {
                ExprKind::Spread(s) => out.extend(self.spread_values(s)),
                _ => out.push((self.expr(e), e.ty.clone())),
            }
        }
        out
    }
}
