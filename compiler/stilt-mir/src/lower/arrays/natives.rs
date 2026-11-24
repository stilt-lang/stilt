//! The natives of `std.array` (generics.arrays): `fill`, `from_list` and `Array.map`, which
//! compile inline, since an array's words are the caller's own, as many as its size, which the
//! caller knows. Each takes its values in the words of their layouts, as compiled code does.

use stilt_hir::decls::prelude_item;
use stilt_types::tast::{self, Callee, Expr};
use stilt_types::ty::{Row, Ty};

use super::BOUNDS;
use crate::FnRef;
use crate::lower::calls::{can_raise, error_type};
use crate::lower::words::word;
use crate::lower::{Conv, Lower};
use crate::mir::{Arg, Callee as MirCallee, Operand, Repr, Runtime, Rvalue};

/// The native of `std.array` that a function names, if it compiles inline.
pub(crate) fn array_native(f: &FnRef) -> Option<&'static str> {
    match f {
        FnRef::Function(item) if &*item.home == "std.array" => match &*item.name {
            "fill" => Some("fill"),
            "from_list" => Some("from_list"),
            _ => None,
        },
        FnRef::Member(owner, name) if stilt_types::ty::is_array(owner) && &**name == "map" => {
            Some("map")
        }
        _ => None,
    }
}

/// The function a callee of a typed body names, as the code of functions does.
fn named(callee: &Callee) -> Option<FnRef> {
    match callee {
        Callee::Function(item) => Some(FnRef::Function(item.clone())),
        Callee::Member(owner, name) => Some(FnRef::Member(owner.clone(), *name)),
        _ => None,
    }
}

impl Lower<'_> {
    /// A call of a native of `std.array`, if `callee` names one: its arguments are evaluated
    /// from left to right, then it runs inline.
    pub(crate) fn array_call(
        &mut self,
        callee: &Callee,
        args: &[tast::Arg],
        row: &Row,
        e: &Expr,
    ) -> Option<Vec<Operand>> {
        let name = array_native(&named(callee)?)?;
        let values: Vec<(Vec<Operand>, Ty)> = args
            .iter()
            .map(|a| (self.expr(&a.value), a.value.ty.clone()))
            .collect();
        let loc = self.loc_at(e.at);
        Some(self.array_native(name, &values, (&e.ty, row), loc))
    }

    /// A native of `std.array`, if `f` names one, on the arguments that the code of a
    /// function used as a value gives it, in the words of their layouts, of types `params`.
    pub(crate) fn inline_array(
        &mut self,
        f: &FnRef,
        args: &[Arg],
        params: &[Ty],
        (ret, row): (&Ty, &Row),
    ) -> Option<Vec<Operand>> {
        let name = array_native(f)?;
        let mut words = args.iter().flat_map(|a| a.operands().into_iter().cloned());
        let values: Vec<(Vec<Operand>, Ty)> = params
            .iter()
            .map(|t| {
                let n = self.layout(t).len();
                (words.by_ref().take(n).collect(), t.clone())
            })
            .collect();
        let loc = Operand::Local(self.loc);
        Some(self.array_native(name, &values, (ret, row), loc))
    }

    fn array_native(
        &mut self,
        name: &str,
        values: &[(Vec<Operand>, Ty)],
        (ret, row): (&Ty, &Row),
        loc: Operand,
    ) -> Vec<Operand> {
        match (name, values) {
            ("fill", [(x, _)]) => self.fill(x, ret, loc),
            ("from_list", [(xs, _)]) => self.listed(&word(xs, 0), ret),
            ("map", [(array, aty), (f, _)]) => {
                self.map_array(array, aty, &word(f, 0), (ret, row, loc))
            }
            _ => {
                self.b.met_error();
                vec![Operand::word(0)]
            }
        }
    }

    /// `fill(x)`: `n` copies of `x`, or a panic with `bounds` when `n` is negative.
    fn fill(&mut self, x: &[Operand], ret: &Ty, loc: Operand) -> Vec<Operand> {
        let Some((elem, size)) = self.array_parts(ret) else {
            self.b.met_error();
            return vec![Operand::word(0)];
        };
        if size < 0 {
            return vec![self.panic(BOUNDS, None, loc)];
        }
        if let Some(e) = self.array_in_memory(ret) {
            return self.filled(e, x, &elem);
        }
        let k = usize::try_from(size).unwrap_or(0);
        super::repeated(x, k, Operand::word(0))
    }

    /// `from_list(xs)`: `Some` of the elements of `xs` when it has exactly `n` of them, and
    /// otherwise `None`, as always for a negative `n`, which no list's length is
    /// (generics.array-sizes).
    fn listed(&mut self, xs: &Operand, ret: &Ty) -> Vec<Operand> {
        let array = match ret {
            Ty::Con(_, args) => args.first().cloned().unwrap_or(Ty::Error),
            _ => Ty::Error,
        };
        let Some((elem, size)) = self.array_parts(&array) else {
            self.b.met_error();
            return vec![Operand::word(0)];
        };
        if size < 0 {
            let index = self.variant_index(&prelude_item("None")) as usize;
            return self.build(ret, index, Vec::new());
        }
        let out = self.temps(ret);
        let (some, none, join) = (self.b.new_block(), self.b.new_block(), self.b.new_block());
        let len = self.b.define_op(
            Repr::Scalar,
            Rvalue::Runtime(Runtime::ListLen, vec![xs.clone()]),
        );
        let n = u64::try_from(size).unwrap_or(0);
        let fits = self.word_eq(len, Operand::word(n));
        self.b.branch(fits, some, none);
        self.b.switch_to(some);
        let at = Operand::Local(self.loc);
        let elements = match self.array_in_memory(&array) {
            Some(e) => self.listed_in_memory(e, xs, &elem),
            None => (0..n)
                .flat_map(|i| self.list_element(xs.clone(), Operand::word(i), at.clone(), &elem))
                .collect(),
        };
        let index = self.variant_index(&prelude_item("Some")) as usize;
        let words = self.build(ret, index, vec![elements]);
        self.assign_all(&out, words);
        self.b.goto(join);
        self.b.switch_to(none);
        let index = self.variant_index(&prelude_item("None")) as usize;
        let words = self.build(ret, index, Vec::new());
        self.assign_all(&out, words);
        self.b.goto(join);
        self.b.switch_to(join);
        out.into_iter().map(Operand::Local).collect()
    }

    /// An array in memory of the layout `e` of the elements of `xs`, which has as many.
    pub(crate) fn listed_in_memory(
        &mut self,
        e: crate::mir::Elements<Repr>,
        xs: &Operand,
        elem: &Ty,
    ) -> Vec<Operand> {
        let (array, pointer) = self.new_array(e);
        let at = Operand::Local(self.loc);
        let mut store = |l: &mut Self, slots: &[Operand], i: Operand| {
            let words = l.list_element(xs.clone(), i, at.clone(), elem);
            l.store_words(&slots[0], words, elem);
        };
        self.each_array_element(&[(pointer, e.element_words())], e.len(), &mut store);
        vec![Operand::Local(array)]
    }

    fn assign_all(&mut self, locals: &[crate::mir::Local], words: Vec<Operand>) {
        for (&l, w) in locals.iter().zip(words) {
            self.b.assign(l, Rvalue::Use(w));
        }
    }

    /// `array.map(f)`: `f` of each element, called in order, whose effects pass through
    /// (effects.closure-parameters).
    fn map_array(
        &mut self,
        array: &[Operand],
        aty: &Ty,
        f: &Operand,
        (ret, row, loc): (&Ty, &Row, Operand),
    ) -> Vec<Operand> {
        let (Some((elem, n)), Some((out, _))) = (self.array_parts(aty), self.array_parts(ret))
        else {
            self.b.met_error();
            return vec![Operand::word(0)];
        };
        let raises = can_raise(row);
        let err = Conv::boxed(error_type(row));
        if let (Some(from), Some(to)) = (self.array_in_memory(aty), self.array_in_memory(ret)) {
            let source = self.in_memory(array.to_vec(), aty);
            let (mapped, target) = self.new_array(to);
            let mut call = |l: &mut Self, at: &[Operand], _| {
                let x = l.load_words(&at[0], &elem);
                let args = x.into_iter().map(Arg::Borrow).collect();
                let callee = MirCallee::Value(f.clone());
                let (ret, err) = (Conv::of(out.clone()), err.clone());
                let y = l.finish_call(callee, args, &[], loc.clone(), raises, &ret, &err);
                l.store_words(&at[1], y, &out);
            };
            let starts = [(source, from.element_words()), (target, to.element_words())];
            self.each_array_element(&starts, from.len(), &mut call);
            return vec![Operand::Local(mapped)];
        }
        // One of the two is held in words, so the arrays have at most `MEMORY_WORDS` elements
        // (`super::held_in_memory`), a call each.
        let k = usize::try_from(n.max(0)).unwrap_or(0);
        let conv = Conv::of(out.clone());
        let mut ys = Vec::new();
        for x in self.elements_of(array, aty, k) {
            let args = x.into_iter().map(Arg::Borrow).collect();
            let callee = MirCallee::Value(f.clone());
            let y = self.finish_call(callee, args, &[], loc.clone(), raises, &conv, &err);
            ys.push((y, out.clone()));
        }
        match self.array_in_memory(ret) {
            Some(to) => self.array_of(to, ys),
            None => ys.into_iter().flat_map(|(y, _)| y).collect(),
        }
    }
}
