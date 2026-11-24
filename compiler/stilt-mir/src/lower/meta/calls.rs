//! The accessors of `std.meta` (meta.shape-accessors, meta.fields and meta.variant-cases), which
//! compile inline: each reads the descriptor, or the field's or the variant's entry, that its
//! receiver is, and calls the closures of its accessors on values held in one word. A set's and a
//! map's are those of the prelude, called at the fresh types of their elements, whose descriptors
//! give their `Eq` and `Hash`.

use stilt_hir::decls::prelude_item;
use stilt_hir::hir::Name;
use stilt_types::tast::{self, Callee as TCallee, Expr};
use stilt_types::ty::{META, Row, Ty};

use super::{A, B, C, CASE_LEN, D, DESC_LEN, E_GET, E_INDEX, E_MAKE, E_NAME, FIELD_LEN, KIND};
use crate::FnRef;
use crate::lower::calls::{can_raise, error_type};
use crate::lower::words::{operands, word};
use crate::lower::{Conv, Lower};
use crate::mir::{Arg, Callee, NumKind, Operand, Prim, Repr, Runtime, Rvalue};

/// A value with its type.
type Typed = (Vec<Operand>, Ty);

/// The kinds of the shapes whose values convert to lists, a list's and a set's, the others' a
/// map's (`super::describe::kind_number`).
const LIST: u64 = 7;
const SET: u64 = 8;

impl Lower<'_> {
    /// A call of an accessor of `std.meta`, if `callee` names one: its arguments are evaluated
    /// from left to right, then it runs inline.
    pub(crate) fn meta_call(
        &mut self,
        callee: &TCallee,
        targs: &[Ty],
        args: &[tast::Arg],
        row: &Row,
        e: &Expr,
    ) -> Option<Vec<Operand>> {
        let TCallee::Member(owner, name) = callee else {
            return None;
        };
        // The types of macros.tokens-and-code have natives and code of their own.
        let reflected = [
            "Integer", "Convert", "Sized", "Fields", "Field", "Cases", "Case",
        ];
        if &*owner.home != META || !reflected.contains(&&*owner.name) {
            return None;
        }
        let values: Vec<Typed> = args
            .iter()
            .map(|a| (self.expr(&a.value), a.value.ty.clone()))
            .collect();
        let loc = self.loc_at(e.at);
        let this = word(&values[0].0, 0);
        let given = values.get(1).cloned();
        Some(self.accessor((&owner.name, name), targs, (this, given), (&e.ty, row), loc))
    }

    fn accessor(
        &mut self,
        (owner, name): (&str, &str),
        targs: &[Ty],
        (this, given): (Operand, Option<Typed>),
        (ret, row): (&Ty, &Row),
        loc: Operand,
    ) -> Vec<Operand> {
        let given = given.unwrap_or_else(|| (vec![Operand::word(0)], Ty::unit()));
        let entry_len = if owner == "Case" { CASE_LEN } else { FIELD_LEN };
        let t = targs.first().cloned().unwrap_or(Ty::Error);
        match (owner, name) {
            ("Integer", "text") => {
                let kind = self.read(this, DESC_LEN, A, Repr::Scalar);
                let args = vec![kind, word(&given.0, 0)];
                vec![
                    self.b
                        .define_op(Repr::Heap, Rvalue::Runtime(Runtime::ShowInt, args)),
                ]
            }
            ("Integer", "parse") => self.int_parse(this, word(&given.0, 0), ret),
            ("Convert", "get") => self.converted(this, given, (targs, ret), true, loc),
            ("Convert", "make") => self.converted(this, given, (targs, ret), false, loc),
            ("Sized", "get") => self.call_field(this, (DESC_LEN, C), &[given], ret, loc),
            ("Sized", "make") => self.array_from(this, given, (&t, ret), loc),
            ("Sized", "len") => vec![self.read(this, DESC_LEN, B, Repr::Scalar)],
            ("Fields" | "Cases", "len") => vec![self.read(this, DESC_LEN, A, Repr::Scalar)],
            ("Fields", "build") => {
                let closure = self.read(this.clone(), DESC_LEN, C, Repr::Heap);
                let args = vec![Arg::Borrow(this), Arg::Borrow(word(&given.0, 0))];
                let (r, err) = (Conv::boxed(ret.clone()), Conv::boxed(error_type(row)));
                let raises = can_raise(row);
                self.finish_call(Callee::Value(closure), args, &[], loc, raises, &r, &err)
            }
            (_, "name") => vec![self.read(this, entry_len, E_NAME, Repr::Heap)],
            (_, "index") => vec![self.read(this, entry_len, E_INDEX, Repr::Scalar)],
            (_, "get") => self.call_field(this, (entry_len, E_GET), &[given], ret, loc),
            ("Case", "make") => self.call_field(this, (CASE_LEN, E_MAKE), &[given], ret, loc),
            _ => unreachable!("`std.meta` declares no other accessor: {owner}.{name}"),
        }
    }

    /// Calls the accessor's closure that field `index` of `this` holds on values held in one
    /// word, and gives its result's words.
    pub(crate) fn call_field(
        &mut self,
        this: Operand,
        (len, index): (u32, u32),
        values: &[Typed],
        ret: &Ty,
        loc: Operand,
    ) -> Vec<Operand> {
        let closure = self.read(this, len, index, Repr::Heap);
        let args = values
            .iter()
            .map(|(words, ty)| self.lend(words.clone(), ty))
            .collect();
        let (r, err) = (Conv::boxed(ret.clone()), Conv::boxed(Ty::Error));
        self.finish_call(Callee::Value(closure), args, &[], loc, false, &r, &err)
    }

    /// The words of an option of type `option`: `Some` of what `some` gives where `cond` holds,
    /// and `None` otherwise.
    pub(crate) fn option_from(
        &mut self,
        cond: Operand,
        option: &Ty,
        some: impl FnOnce(&mut Self) -> Vec<Operand>,
    ) -> Vec<Operand> {
        self.choose(
            cond,
            option,
            |l| {
                let x = some(l);
                l.build(option, 1, vec![x])
            },
            |l| l.build(option, 0, Vec::new()),
        )
    }

    /// The words of a value of type `ty`: what `yes` gives where `cond` holds, and otherwise
    /// what `no` gives.
    pub(crate) fn choose(
        &mut self,
        cond: Operand,
        ty: &Ty,
        yes: impl FnOnce(&mut Self) -> Vec<Operand>,
        no: impl FnOnce(&mut Self) -> Vec<Operand>,
    ) -> Vec<Operand> {
        let result = self.temps(ty);
        let (then, otherwise, join) = (self.b.new_block(), self.b.new_block(), self.b.new_block());
        self.b.branch(cond, then, otherwise);
        self.b.switch_to(then);
        let v = yes(self);
        self.into(&result, &v, join);
        self.b.switch_to(otherwise);
        let v = no(self);
        self.into(&result, &v, join);
        self.b.switch_to(join);
        operands(&result)
    }

    /// `n.parse(text)`: the integer that `text` writes as `n.text` would, of the kind the
    /// descriptor gives (meta.shape-accessors).
    fn int_parse(&mut self, this: Operand, text: Operand, ret: &Ty) -> Vec<Operand> {
        let kind = self.read(this, DESC_LEN, A, Repr::Scalar);
        let args = vec![kind, text];
        let valid = self.b.define_op(
            Repr::Scalar,
            Rvalue::Runtime(Runtime::IntValid, args.clone()),
        );
        self.option_from(valid, ret, |l| {
            vec![l.b.define_op(Repr::Scalar, Rvalue::Runtime(Runtime::IntParse, args))]
        })
    }

    /// `get` or `make` of a `meta.Convert<T, U>`, by `U`: a float's, which converts an `f32`;
    /// an option's, through its descriptor's closures; and a list's, a set's or a map's, by
    /// the descriptor's kind; and otherwise the value itself.
    fn converted(
        &mut self,
        this: Operand,
        given: Typed,
        (targs, ret): (&[Ty], &Ty),
        get: bool,
        loc: Operand,
    ) -> Vec<Operand> {
        let u = targs.get(1).cloned().unwrap_or(Ty::Error);
        if u.is_prelude("f64") {
            let x = word(&given.0, 0);
            let narrow = self.read(this, DESC_LEN, A, Repr::Scalar);
            let wide = self.word_eq(narrow, Operand::word(1));
            let (from, to) = if get {
                (NumKind::F32, NumKind::F64)
            } else {
                (NumKind::F64, NumKind::F32)
            };
            let float = Ty::f64();
            return self.choose(
                wide,
                &float,
                |_| vec![x.clone()],
                |l| {
                    let prim =
                        Rvalue::Prim(Prim::ToFloat(from, to), vec![x.clone()], Operand::word(0));
                    vec![l.b.define_op(Repr::Scalar, prim)]
                },
            );
        }
        if u.is_prelude("Option") {
            let field = if get { C } else { D };
            return self.call_field(this, (DESC_LEN, field), &[given], ret, loc);
        }
        if u.is_prelude("List") {
            return self.collection(this, word(&given.0, 0), (&u, ret), get, loc);
        }
        given.0
    }

    /// A list's own value, a set's elements or a map's entries as a list, and back.
    fn collection(
        &mut self,
        this: Operand,
        x: Operand,
        (u, ret): (&Ty, &Ty),
        get: bool,
        loc: Operand,
    ) -> Vec<Operand> {
        let kind = self.read(this, DESC_LEN, KIND, Repr::Scalar);
        let elem = match u {
            Ty::Con(_, args) => args.first().cloned().unwrap_or(Ty::Error),
            _ => Ty::Error,
        };
        let is_list = self.word_eq(kind.clone(), Operand::word(LIST));
        let x2 = x.clone();
        self.choose(
            is_list,
            ret,
            |_| vec![x2],
            |l| {
                let pair = match &elem {
                    Ty::Tuple(kv) if kv.len() == 2 => Some(kv.clone()),
                    _ => None,
                };
                let Some(kv) = pair else {
                    return l.prelude_call(
                        "Set",
                        if get { "to_list" } else { "from_list" },
                        &[elem],
                        x,
                        ret,
                        loc,
                    );
                };
                let is_set = l.word_eq(kind, Operand::word(SET));
                let (x3, loc2, elem2) = (x.clone(), loc.clone(), elem.clone());
                l.choose(
                    is_set,
                    ret,
                    |l| {
                        let name = if get { "to_list" } else { "from_list" };
                        l.prelude_call("Set", name, &[elem2], x3, ret, loc2)
                    },
                    |l| {
                        let name = if get { "entries" } else { "from_entries" };
                        l.prelude_call("Map", name, &kv, x, ret, loc)
                    },
                )
            },
        )
    }

    /// A call of a function of an inherent impl of the prelude's `owner` at `targs`, on one
    /// value of one word.
    fn prelude_call(
        &mut self,
        owner: &str,
        name: &str,
        targs: &[Ty],
        x: Operand,
        ret: &Ty,
        loc: Operand,
    ) -> Vec<Operand> {
        let f = FnRef::Member(prelude_item(owner), Name::from(name));
        let target = self.direct(f, targs);
        self.emit_call(
            target,
            vec![Arg::Borrow(x)],
            &[],
            loc,
            false,
            ret,
            &Row::EMPTY,
        )
    }

    /// `s.make(xs)` of an array's `meta.Sized`: `None` unless `xs` has as many elements as the
    /// array's size (meta.shape-accessors).
    fn array_from(
        &mut self,
        this: Operand,
        xs: Typed,
        (t, ret): (&Ty, &Ty),
        loc: Operand,
    ) -> Vec<Operand> {
        let n = self.read(this.clone(), DESC_LEN, B, Repr::Scalar);
        let list = word(&xs.0, 0);
        let len = self
            .b
            .define_op(Repr::Scalar, Rvalue::Runtime(Runtime::ListLen, vec![list]));
        let fits = self.word_eq(len, n);
        let t = t.clone();
        self.option_from(fits, ret, |l| {
            l.call_field(this, (DESC_LEN, D), &[xs], &t, loc)
        })
    }
}
