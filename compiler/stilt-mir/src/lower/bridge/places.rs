//! The places and the maps of a call past the caps (`super`): an `inout` argument goes as a
//! pointer to its value converted into the callee's representation, which is converted back and
//! written to its place when the call returns or raises; and a map whose keys or values convert
//! is rebuilt entry by entry, with its default.

use stilt_hir::decls::prelude_item;
use stilt_hir::hir::Name;
use stilt_types::ty::Ty;

use super::{Dir, Given};
use crate::FnRef;
use crate::lower::Form;
use crate::lower::Lower;
use crate::lower::words::word;
use crate::mir::{Local, Operand, Repr, Runtime, Rvalue, Stmt};

/// An `inout` argument of a call past the caps: where its value is, the locals that hold it
/// converted for the callee, its type outside and past the caps, and which way it converts back.
pub(crate) struct Back {
    pub(crate) at: Given,
    pub(crate) temps: Vec<Local>,
    pub(crate) n: Ty,
    pub(crate) u: Ty,
    pub(crate) dir: Dir,
}

impl Lower<'_> {
    /// A pointer to the value of an `inout` argument of type `n` outside and `u` past the caps,
    /// converted in direction `dir` into locals, and how it converts back.
    pub(crate) fn cross_inout(
        &mut self,
        at: Given,
        (n, u): (&Ty, &Ty),
        dir: Dir,
    ) -> (Operand, Back) {
        let (from, to) = if dir == Dir::In { (n, u) } else { (u, n) };
        let words = match &at {
            Given::Place(p) => self.read_place(p),
            Given::Pointer(pointer) => self.load_words(pointer, from),
            Given::Let(words) => words.clone(),
        };
        let words = self.cross_convert(words, n, u, dir);
        let temps = self.copy_into_temps(words, to);
        self.b.make_slots(&temps);
        let pointer = self.b.define_op(Repr::Scalar, Rvalue::SlotOf(temps[0]));
        let back = if dir == Dir::In { Dir::Out } else { Dir::In };
        let (n, u) = (n.clone(), u.clone());
        (
            pointer,
            Back {
                at,
                temps,
                n,
                u,
                dir: back,
            },
        )
    }

    /// Converts the values of the `inout` arguments of a call past the caps back, and writes
    /// them to their places, from left to right (values.left-to-right).
    pub(crate) fn cross_back(&mut self, backs: &[Back]) {
        for b in backs {
            let to = if b.dir == Dir::In { &b.u } else { &b.n };
            let words: Vec<Operand> = b
                .temps
                .iter()
                .map(|&l| {
                    let repr = self.b.repr_of(l);
                    self.b.define_op(repr, Rvalue::Use(Operand::Local(l)))
                })
                .collect();
            let words = self.cross_convert(words, &b.n, &b.u, b.dir);
            match &b.at {
                Given::Place(p) => self.store_place(p, words),
                Given::Pointer(pointer) => self.store_words(pointer, words, to),
                Given::Let(_) => {}
            }
        }
    }

    /// A new map with no entries, of type `to`, with the default of `map`, if it has one,
    /// converted from a value of type `fv` to one of `tv`, `nv` outside and `uv` past the caps.
    pub(crate) fn map_like(
        &mut self,
        map: &Operand,
        (fv, tv): (&Ty, &Ty),
        (nv, uv): (&Ty, &Ty),
        dir: Dir,
        to: &Ty,
    ) -> Operand {
        let Ty::Con(_, args) = to else {
            return Operand::word(0);
        };
        let out = self.b.temp(Repr::Heap);
        let default = self.b.define_op(
            Repr::Scalar,
            Rvalue::Runtime(Runtime::MapDefault, vec![map.clone()]),
        );
        let none = self.word_eq(default.clone(), Operand::word(0));
        let (plain, with, join) = (self.b.new_block(), self.b.new_block(), self.b.new_block());
        self.b.branch(none, plain, with);
        self.b.switch_to(plain);
        let made = self.map_native("new", args, Vec::new());
        self.b.assign(out, Rvalue::Use(made));
        self.b.goto(join);
        self.b.switch_to(with);
        let d = self.map_words(map, &default, fv, true);
        let d = self.cross_convert(d, nv, uv, dir);
        let d = self.pass(d, tv, Form::Word);
        let made = self.map_native("with_default", args, d);
        self.b.assign(out, Rvalue::Use(made));
        self.b.goto(join);
        self.b.switch_to(join);
        Operand::Local(out)
    }

    /// A call of the native `Map.name` with type arguments `args` and arguments `values`.
    fn map_native(&mut self, name: &str, args: &[Ty], values: Vec<crate::mir::Arg>) -> Operand {
        let target = self.direct(FnRef::Member(prelude_item("Map"), Name::from(name)), args);
        let ty = Ty::Con(prelude_item("Map"), args.to_vec());
        let loc = Operand::Local(self.loc);
        let row = stilt_types::ty::Row::EMPTY;
        let words = self.emit_call(target, values, &[], loc, false, &ty, &row);
        word(&words, 0)
    }

    /// Runs `body` for each entry of a map, in insertion order, with the words of its key and
    /// its value, of types `(k, v)`, borrowed from the map.
    pub(crate) fn each_entry(
        &mut self,
        map: &Operand,
        (k, v): (&Ty, &Ty),
        mut body: impl FnMut(&mut Self, Vec<Operand>, Vec<Operand>),
    ) {
        let position = self.b.temp(Repr::Scalar);
        self.b.assign(position, Rvalue::Use(Operand::word(0)));
        let (head, step, exit) = (self.b.new_block(), self.b.new_block(), self.b.new_block());
        self.b.goto(head);
        self.b.switch_to(head);
        let found = Rvalue::Runtime(
            Runtime::MapNext,
            vec![map.clone(), Operand::Local(position)],
        );
        self.b.assign(position, found);
        let done = self.word_eq(Operand::Local(position), Operand::word(u64::MAX));
        self.b.branch(done, exit, step);
        self.b.switch_to(step);
        let at = |rt| Rvalue::Runtime(rt, vec![map.clone(), Operand::Local(position)]);
        let kp = self.b.define_op(Repr::Scalar, at(Runtime::MapKeyAt));
        let vp = self.b.define_op(Repr::Scalar, at(Runtime::MapValueAt));
        let kw = self.map_words(map, &kp, k, false);
        let vw = self.map_words(map, &vp, v, true);
        body(self, kw, vw);
        self.step(position);
        self.b.goto(head);
        self.b.switch_to(exit);
    }

    /// `m[k] = v` on the map the slot `pointer` points to, of keys and values of types
    /// `(k_ty, v_ty)`, which consumes the words of `v`.
    pub(crate) fn map_store(
        &mut self,
        pointer: &Operand,
        k: Vec<Operand>,
        v: Vec<Operand>,
        (k_ty, v_ty): (&Ty, &Ty),
    ) {
        let k = self.map_word(k, k_ty);
        let v = self.map_word(v, v_ty);
        let (eq, hash) = self.key_dicts(k_ty);
        let loc = Operand::Local(self.loc);
        self.b.emit(Stmt::Effect(
            Runtime::MapStore,
            vec![loc, eq, hash, pointer.clone(), k, v],
        ));
    }
}
