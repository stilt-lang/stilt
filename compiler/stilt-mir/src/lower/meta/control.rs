//! Reflection's expressions, and the code that opens fresh types (meta.shape-and-name,
//! meta.fresh-types and meta.fields, and 10): `T.shape()` and `T.name()`, the arms that match a
//! shape's case, the loops over a type's fields and variants, and bound tests. A fresh type is a
//! generic of its arm or its loop's body, held in one word, whose witness and descriptor its thunk
//! gives, with the dictionaries of its descriptor's table.

use stilt_hir::hir::{GenericId, Item};
use stilt_types::tast::{Block, Expr, ExprKind, Pat, Reflection};
use stilt_types::ty::{FnTy, Ty};

use super::describe::kind_number;
use super::{
    A, B, CASE_LEN, DESC_LEN, E_THUNK, E_WITNESS, FIELD_LEN, IDENT, IMPL_ARGS, IMPLS, KIND, NAME,
    WITNESS, desc_ty,
};
use crate::Held;
use crate::lower::Lower;
use crate::mir::{BlockId, Local, NumKind, Operand, Prim, Repr, Runtime, Rvalue};

/// The type `F` of a `meta.Field<T, F>`.
fn field_type(ty: &Ty) -> Option<&Ty> {
    match ty {
        Ty::Con(item, args) if stilt_types::ty::is_meta(item, "Field") => args.get(1),
        _ => None,
    }
}

/// The fresh types a type holds, in the order they first appear.
fn fresh_in(t: &Ty, out: &mut Vec<GenericId>) {
    match t {
        Ty::Param(g) if g.is_fresh() && !out.contains(g) => out.push(g.clone()),
        Ty::Con(_, ts) | Ty::Tuple(ts) => ts.iter().for_each(|t| fresh_in(t, out)),
        _ => {}
    }
}

impl<'a> Lower<'a> {
    /// `T.shape()`, the descriptor of `T`, and `T.name()`, its name (meta.shape-and-name), and a
    /// bound test, whether `T` has the impls (meta.bound-tests).
    pub(crate) fn reflection(&mut self, e: &Expr) -> Vec<Operand> {
        match &e.kind {
            ExprKind::Reflect(what, t) => {
                let desc = self.descriptor(t);
                match what {
                    Reflection::Shape => vec![desc],
                    Reflection::Name => vec![self.read(desc, DESC_LEN, NAME, Repr::Heap)],
                }
            }
            ExprKind::Bound(t, traits) => vec![self.bound_test(t, traits).0],
            _ => unreachable!("not a reflection: {:?}", e.kind),
        }
    }

    /// Brings the fresh type `g` into scope, from the thunk of its descriptor, its witness
    /// being `witness` where the caller has it.
    pub(crate) fn open_fresh(&mut self, g: &GenericId, thunk: Operand, witness: Option<Operand>) {
        let desc = self.force(thunk);
        let w = witness.unwrap_or_else(|| self.read(desc.clone(), DESC_LEN, WITNESS, Repr::Scalar));
        let w = self.b.define(Repr::Scalar, Rvalue::Use(w));
        let traits = self.table_traits();
        let tlen = u32::try_from(traits.len()).expect("under 4G traits");
        let impls = self.read(desc.clone(), DESC_LEN, IMPLS, Repr::Heap);
        let dicts = (0..tlen)
            .zip(traits)
            .map(|(j, t)| (t, self.read(impls.clone(), tlen, j, Repr::Heap)))
            .collect();
        let ty = Ty::Param(g.clone());
        self.push_generic(ty.clone(), w, dicts, Some(&Held::Word));
        self.set_descriptor(&ty, desc);
    }

    /// Matches a shape's case (meta.shapes and meta.fresh-types): the descriptor's kind, then the
    /// payload, the descriptor itself, with the fresh types it holds opened.
    pub(crate) fn match_shape(
        &mut self,
        case: &Item,
        ps: &[Pat],
        v: &[Operand],
        mutable: bool,
        then: crate::lower::patterns::Then<'_, 'a>,
        fail: BlockId,
    ) {
        let desc = crate::lower::words::word(v, 0);
        let kind = self.read(desc.clone(), DESC_LEN, KIND, Repr::Scalar);
        let same = self.word_eq(kind, Operand::word(kind_number(Some(&case.name))));
        let ok = self.b.new_block();
        self.b.branch(same, ok, fail);
        self.b.switch_to(ok);
        let mut fresh = Vec::new();
        for p in ps {
            fresh_in(&p.ty, &mut fresh);
        }
        for (g, field) in fresh.iter().zip([A, B]) {
            let thunk = self.read(desc.clone(), DESC_LEN, field, Repr::Heap);
            self.open_fresh(g, thunk, None);
        }
        let items: Vec<(&Pat, Vec<Operand>)> = ps.iter().map(|p| (p, vec![desc.clone()])).collect();
        self.match_all(&items, mutable, then, fail);
    }

    /// The entries of a `meta.Fields` or a `meta.Cases`, each bound in turn, in order, its
    /// fresh type opened for the loop's body (meta.fields and meta.variant-cases).
    pub(crate) fn for_reflected(&mut self, pattern: &Pat, source: &Expr, block: &Block) {
        let desc = self.expr1(source);
        let entries = self.read(desc.clone(), DESC_LEN, B, Repr::Heap);
        let count = self.read(desc, DESC_LEN, A, Repr::Scalar);
        let i = self.b.temp(Repr::Scalar);
        self.b.assign(i, Rvalue::Use(Operand::word(0)));
        let (head, body, next, exit) = self.loop_blocks();
        self.b.goto(head);
        self.b.switch_to(head);
        let more = self.lt(NumKind::I64, Operand::Local(i), count);
        self.b.branch(more, body, exit);
        self.b.switch_to(body);
        let mark = self.generics.len();
        let at = self.loc_at(source.at);
        let entry = self.list_element(entries, Operand::Local(i), at, &desc_ty());
        let entry = crate::lower::words::word(&entry, 0);
        let mut fresh = Vec::new();
        fresh_in(&pattern.ty, &mut fresh);
        let len = if source.ty.meta_of("Cases").is_some() {
            CASE_LEN
        } else {
            FIELD_LEN
        };
        if let Some(g) = fresh.first() {
            let thunk = self.read(entry.clone(), len, E_THUNK, Repr::Heap);
            let w = self.read(entry.clone(), len, E_WITNESS, Repr::Scalar);
            self.open_fresh(g, thunk, Some(w));
        }
        self.binding(pattern, vec![entry], false, None);
        self.loop_body(block, exit, next);
        self.close_fresh(mark);
        self.b.switch_to(next);
        self.step(i);
        self.b.goto(head);
        self.b.switch_to(exit);
    }

    /// Gives a type parameter of a closure of a polymorphic function type, given for
    /// `fields.build`, the descriptor of the field whose entry its parameter of type
    /// `meta.Field<T, F>` holds, since `F` is that field's type (meta.building).
    pub(crate) fn field_descriptor(&mut self, fty: &FnTy, ty: &Ty, locals: &[Local]) {
        let Some(Ty::Param(g)) = field_type(ty) else {
            return;
        };
        if !fty.generics.iter().any(|(h, _)| h == g) || locals.len() != 1 {
            return;
        }
        let thunk = self.read(Operand::Local(locals[0]), FIELD_LEN, E_THUNK, Repr::Heap);
        let desc = self.force(thunk);
        self.set_descriptor(&Ty::Param(g.clone()), desc);
    }

    /// Takes the fresh types opened from `mark` on out of scope.
    pub(crate) fn close_fresh(&mut self, mark: usize) {
        if self.generics.len() > mark {
            self.generics.truncate(mark);
            self.instances.borrow_mut().clear();
        }
    }

    /// Whether the type that instantiates `t` has an impl of each of `traits`, from its
    /// descriptor's table (meta.bound-tests), and the dictionaries of those it has, 0 for those it
    /// lacks.
    pub(crate) fn bound_test(
        &mut self,
        t: &Ty,
        traits: &[(Item, Vec<Ty>)],
    ) -> (Operand, Vec<(Item, Operand)>) {
        let desc = self.descriptor(t);
        let table = self.table_traits();
        let tlen = u32::try_from(table.len()).expect("under 4G traits");
        let impls = self.read(desc.clone(), DESC_LEN, IMPLS, Repr::Heap);
        let mut all = Operand::word(1);
        let mut dicts = Vec::new();
        for (tr, args) in traits {
            let Some(j) = table.iter().position(|x| x == tr) else {
                all = Operand::word(0);
                continue;
            };
            let j = u32::try_from(j).expect("under 4G traits");
            let d = self.read(impls.clone(), tlen, j, Repr::Heap);
            let none = self.word_eq(d.clone(), Operand::word(0));
            let some = self.not(none);
            all = self.both(all, some);
            // The impl gives the trait the bound's arguments (meta.bound-tests), by their
            // identities.
            if !args.is_empty() {
                let given = self.read(desc.clone(), DESC_LEN, IMPL_ARGS, Repr::Heap);
                let given = self.read(given, tlen, j, Repr::Heap);
                let mut params = Vec::new();
                let pieces = self.ident_pieces(args, &mut params);
                let wanted = self.joined(&pieces, Some(&params), IDENT);
                let equal = Rvalue::Runtime(Runtime::StrEq, vec![given, wanted]);
                let equal = self.b.define_op(Repr::Scalar, equal);
                all = self.both(all, equal);
            }
            dicts.push((tr.clone(), d));
        }
        (all, dicts)
    }

    pub(crate) fn not(&mut self, x: Operand) -> Operand {
        let not = Rvalue::Prim(Prim::BoolNot, vec![x], Operand::word(0));
        self.b.define_op(Repr::Scalar, not)
    }

    pub(crate) fn both(&mut self, a: Operand, b: Operand) -> Operand {
        let and = Rvalue::Prim(Prim::BitAnd, vec![a, b], Operand::word(0));
        self.b.define_op(Repr::Scalar, and)
    }

    /// Lowers the block that a bound test guards, with `t` given the dictionaries of the
    /// traits it names, in addition to its own.
    pub(crate) fn guarded(
        &mut self,
        t: &Ty,
        dicts: Vec<(Item, Operand)>,
        then: &Block,
    ) -> Vec<Operand> {
        let at = self.generics.iter().rposition(|(g, _)| g == t);
        let added = dicts.len();
        if let Some(k) = at {
            self.generics[k].1.dicts.extend(dicts);
            self.instances.borrow_mut().clear();
        }
        let v = self.block(then);
        if let Some(k) = at {
            let len = self.generics[k].1.dicts.len();
            self.generics[k].1.dicts.truncate(len - added);
            self.instances.borrow_mut().clear();
        }
        v
    }
}
