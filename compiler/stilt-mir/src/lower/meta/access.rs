//! The code of a descriptor's accessors (meta.shape-accessors, meta.fields and meta.variant-cases),
//! compiled for the layout of the type its form describes: each takes and gives values in the one
//! word that holds them where a type parameter stands, which the code that reflects holds a fresh
//! type's values in, so that it reads and makes values whose layouts it doesn't know.

use stilt_types::ty::Ty;

use super::{B, DESC_LEN, desc_ty};
use crate::described::{Access, Described, numbered};
use crate::lower::words::word;
use crate::lower::{Conv, Cx, Lower};
use crate::mir::{Arg, Callee, Function, Operand, ParamMode, Repr};
use crate::{FnRef, Held};

/// The code of the accessor `op` of the values of the form `d`.
pub(crate) fn access(cx: &Cx<'_>, f: &FnRef, d: &Described, op: Access) -> Option<Function> {
    let ty = d.ty()?;
    let mut l = Lower::new(cx, f.clone(), true);
    l.open_form(d);
    let out = match op {
        Access::Field(i) => l.field_get(&ty, i),
        Access::Build => l.build_fields(&ty),
        Access::CaseGet(i) => l.case_get(&ty, i),
        Access::CaseMake(i) => l.case_make(&ty, i),
        Access::OptionGet => l.option_get(&ty),
        Access::OptionMake => l.option_make(&ty),
        Access::ArrayGet => l.array_get(&ty),
        Access::ArrayMake => l.array_make(&ty),
    };
    l.return_(out);
    Some(l.into_function())
}

impl Lower<'_> {
    /// A parameter that holds a value of type `ty` in one word, and its words.
    fn held_param(&mut self, ty: &Ty) -> Vec<Operand> {
        let p = self.b.param(self.repr(ty), ParamMode::Borrowed, None);
        self.unbox_lasting(p, ty)
    }

    /// A type parameter, beyond those of the form, that stands for the type `part` in the
    /// values the code gives, held in one word: a fresh type of the code that reflects.
    fn held_as(&mut self, part: &Ty) -> Ty {
        let n = u32::try_from(self.generics.len()).expect("under 4G generics");
        let ty = Ty::Param(numbered(1000 + n));
        let w = self.witness(part);
        let w = self.b.define(Repr::Scalar, crate::mir::Rvalue::Use(w));
        self.push_generic(ty.clone(), w, Vec::new(), Some(&Held::Word));
        ty
    }

    fn field_get(&mut self, ty: &Ty, i: u32) -> Vec<Operand> {
        let v = self.held_param(ty);
        let part = self.named_parts(ty)[i as usize].1.clone();
        self.ret = Conv::boxed(part);
        let fields = self.fields_of(ty, 0);
        self.field_words(&v, &fields, i as usize)
    }

    /// A value of `ty` from what the closure it is given, of `fn<F>(Field<T, F>) -> F`, gives
    /// each field's entry of the descriptor it is given, in order (meta.building). The closure's
    /// raises pass through, as from a row variable.
    fn build_fields(&mut self, ty: &Ty) -> Vec<Operand> {
        let desc = Operand::Local(self.b.param(Repr::Heap, ParamMode::Borrowed, None));
        let f = Operand::Local(self.b.param(Repr::Heap, ParamMode::Borrowed, None));
        self.ret = Conv::boxed(ty.clone());
        let entries = self.read(desc, DESC_LEN, B, Repr::Heap);
        let loc = Operand::Local(self.loc);
        let mut values = Vec::new();
        for (j, (_, part)) in self.named_parts(ty).into_iter().enumerate() {
            let at = Operand::word(j as u64);
            let entry = self.list_element(entries.clone(), at, loc.clone(), &desc_ty());
            let w = self.witness(&part);
            let args = vec![Arg::Borrow(w), Arg::Borrow(word(&entry, 0))];
            let (ret, err) = (Conv::boxed(part), Conv::boxed(Ty::Error));
            let callee = Callee::Value(f.clone());
            values.push(self.finish_call(callee, args, &[], loc.clone(), true, &ret, &err));
        }
        self.build(ty, 0, values)
    }

    /// `Some` of the payload of variant `i`, a tuple held in one word, or `None`.
    fn case_get(&mut self, ty: &Ty, i: u32) -> Vec<Operand> {
        let v = self.held_param(ty);
        let payload = self.cases(ty)[i as usize].1.clone();
        let held = self.held_as(&payload);
        let option = Ty::option(held);
        self.ret = Conv::boxed(option.clone());
        let is = self.is_variant(&v, ty, i);
        let n = match &payload {
            Ty::Tuple(ts) => ts.len(),
            _ => 0,
        };
        self.option_from(is, &option, |l| {
            let fields = l.fields_of(ty, i as usize);
            let parts = (0..n).map(|j| l.field_words(&v, &fields, j)).collect();
            let tuple = l.build(&payload, 0, parts);
            vec![l.boxed(tuple, &payload)]
        })
    }

    /// The value of variant `i` from its payload, a tuple held in one word.
    fn case_make(&mut self, ty: &Ty, i: u32) -> Vec<Operand> {
        let payload = self.cases(ty)[i as usize].1.clone();
        let p = self.held_param(&payload);
        self.ret = Conv::boxed(ty.clone());
        let n = match &payload {
            Ty::Tuple(ts) => ts.len(),
            _ => 0,
        };
        let fields = self.fields_of(&payload, 0);
        let parts = (0..n).map(|j| self.field_words(&p, &fields, j)).collect();
        self.build(ty, i as usize, parts)
    }

    /// An option of the one word that holds its element.
    fn option_get(&mut self, ty: &Ty) -> Vec<Operand> {
        let v = self.held_param(ty);
        let elem = element(ty);
        let held = self.held_as(&elem);
        let option = Ty::option(held);
        self.ret = Conv::boxed(option.clone());
        let is = self.is_variant(&v, ty, 1);
        self.option_from(is, &option, |l| {
            let fields = l.fields_of(ty, 1);
            let x = l.field_words(&v, &fields, 0);
            vec![l.boxed(x, &elem)]
        })
    }

    /// An option from an option of the one word that holds its element.
    fn option_make(&mut self, ty: &Ty) -> Vec<Operand> {
        let elem = element(ty);
        let held = self.held_as(&elem);
        let option = Ty::option(held);
        let v = self.held_param(&option);
        self.ret = Conv::boxed(ty.clone());
        let is = self.is_variant(&v, &option, 1);
        self.option_from(is, ty, |l| {
            let fields = l.fields_of(&option, 1);
            let x = l.field_words(&v, &fields, 0);
            l.unbox(word(&x, 0), &elem)
        })
    }

    /// An array's elements, as a list.
    fn array_get(&mut self, ty: &Ty) -> Vec<Operand> {
        let v = self.held_param(ty);
        let (elem, n) = arrayed(self, ty);
        let list = Ty::list(elem.clone());
        self.ret = Conv::boxed(list.clone());
        if let Some(e) = self.array_in_memory(ty) {
            return vec![self.list_of_array(&v, ty, (&elem, e))];
        }
        let fields = self.fields_of(ty, 0);
        let values = (0..n).map(|j| self.field_words(&v, &fields, j)).collect();
        vec![self.list_literal(values, &list)]
    }

    /// An array of the elements of a list of as many, which the caller checked.
    fn array_make(&mut self, ty: &Ty) -> Vec<Operand> {
        let (elem, n) = arrayed(self, ty);
        let xs = word(&self.held_param(&Ty::list(elem.clone())), 0);
        self.ret = Conv::boxed(ty.clone());
        if let Some(e) = self.array_in_memory(ty) {
            return self.listed_in_memory(e, &xs, &elem);
        }
        let loc = Operand::Local(self.loc);
        let values = (0..n)
            .map(|j| self.list_element(xs.clone(), Operand::word(j as u64), loc.clone(), &elem))
            .collect();
        self.build(ty, 0, values)
    }
}

/// The element type of an option type.
fn element(ty: &Ty) -> Ty {
    match ty {
        Ty::Con(_, args) => args.first().cloned().unwrap_or(Ty::Error),
        _ => Ty::Error,
    }
}

/// The element type and the size of an array type.
fn arrayed(l: &Lower<'_>, ty: &Ty) -> (Ty, usize) {
    let (elem, n) = ty.arrayed().expect("an array type");
    let n = l.value_of(n).unwrap_or(0).max(0);
    (elem.clone(), usize::try_from(n).unwrap_or(0))
}
