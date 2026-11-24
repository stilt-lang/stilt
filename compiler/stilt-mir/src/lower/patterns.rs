//! Patterns (patterns.pattern-forms): testing a value against a pattern and binding its variables.
//!
//! A pattern is matched in continuation-passing style, as the reference interpreter matches
//! it: the code after a match runs once for each way the value matches, which differ in the
//! alternative each or-pattern takes, from left to right. So a guard that fails sends control
//! to the next alternative that may match, before the next arm (patterns.guards).

use stilt_hir::hir::{ListRest, LocalId};
use stilt_types::tast::{Arm, Expr, Pat, PatKind};
use stilt_types::ty::Ty;

use super::exprs::immediate;
use super::numeric::int_literal;
use super::words::{witness_of, word};
use super::{Lower, Var};
use crate::mir::{
    BlockId, Const, Local, NumKind, Operand, Prim, Repr, Runtime, Rvalue, Terminator,
};

/// What the code after a match does, given where to go if it fails in turn.
pub(crate) type Then<'k, 'a> = &'k mut dyn FnMut(&mut Lower<'a>, BlockId);

impl<'a> Lower<'a> {
    /// Binds the variables of a pattern that a `let` or `var` statement, a `for` loop or a
    /// closure's parameter matches. A value that doesn't match runs the `else` branch of a
    /// let-else (patterns.let-else).
    pub(crate) fn binding(
        &mut self,
        p: &Pat,
        v: Vec<Operand>,
        mutable: bool,
        otherwise: Option<&Expr>,
    ) {
        let (done, failed) = (self.b.new_block(), self.b.new_block());
        self.matches(p, v, mutable, &mut |l, _| l.b.goto(done), failed);
        self.b.switch_to(failed);
        if let Some(x) = otherwise {
            self.expr(x);
        }
        self.b.terminate(Terminator::Unreachable);
        self.b.switch_to(done);
    }

    /// Tests an arm: goes to `body` with its variables bound if the value matches its pattern
    /// and its guard holds, and to `next` otherwise.
    pub(crate) fn arm_test(&mut self, arm: &Arm, v: &[Operand], body: BlockId, next: BlockId) {
        let guard = arm.guard.as_ref();
        self.matches(
            &arm.pattern,
            v.to_vec(),
            false,
            &mut |l, fail| match guard {
                Some(g) => {
                    let holds = l.expr1(g);
                    l.b.branch(holds, body, fail);
                }
                None => l.b.goto(body),
            },
            next,
        );
    }

    /// The locals that hold a variable a pattern binds, one per word, made when it is first
    /// bound.
    pub(super) fn bind_locals(&mut self, id: LocalId, ty: &Ty, mutable: bool) -> Vec<Local> {
        if let Some(Var::Value { locals, .. }) = self.vars.get(&id) {
            return locals.clone();
        }
        let name = self.names.get(id.0 as usize).copied();
        let locals = self.named_locals(name.as_ref(), ty, false);
        for &l in &locals {
            self.b.decl_mut(l).var = mutable;
        }
        self.vars.insert(
            id,
            Var::Value {
                locals: locals.clone(),
                mutable,
            },
        );
        locals
    }

    fn test(&mut self, cond: Operand, fail: BlockId) {
        let ok = self.b.new_block();
        self.b.branch(cond, ok, fail);
        self.b.switch_to(ok);
    }

    pub(crate) fn word_eq(&mut self, a: Operand, b: Operand) -> Operand {
        self.b.define_op(
            Repr::Scalar,
            Rvalue::Prim(Prim::WordEq, vec![a, b], Operand::word(0)),
        )
    }

    /// Whether a value equals a literal or constant pattern (patterns.constants).
    fn literal_test(&mut self, p: &Pat, v: &[Operand]) -> Operand {
        let first = word(v, 0);
        match &p.kind {
            PatKind::Int(text) => {
                let (negative, digits) = match text.strip_prefix('-') {
                    Some(rest) => (true, rest.trim_start()),
                    None => (false, text.as_str()),
                };
                let literal = Operand::word(int_literal(digits, negative, &p.ty));
                self.word_eq(first, literal)
            }
            PatKind::Bool(b) => self.word_eq(first, Operand::word(u64::from(*b))),
            PatKind::Str(s) => {
                let literal = Operand::Const(Const::Str(s.as_str().into()));
                let same = Rvalue::Runtime(Runtime::StrEq, vec![first, literal]);
                self.b.define_op(Repr::Scalar, same)
            }
            PatKind::Const(c) => {
                let constant = self.expr(c);
                self.same(v, &constant, &p.ty)
            }
            _ => unreachable!("a literal or constant pattern"),
        }
    }

    /// Whether two values of type `ty` are the same by structure, word by word, for constant
    /// patterns.
    fn same(&mut self, a: &[Operand], b: &[Operand], ty: &Ty) -> Operand {
        let all = self.b.temp(Repr::Scalar);
        self.b.assign(all, Rvalue::Use(Operand::word(1)));
        for (i, repr) in self.layout(ty).into_iter().enumerate() {
            self.same_word((word(a, i), word(b, i)), repr, all);
        }
        Operand::Local(all)
    }

    /// Clears `all` unless two words of this representation are the same by structure: each
    /// word of each element of an array held in memory, in a loop.
    fn same_word(&mut self, (one, other): (Operand, Operand), repr: Repr, all: crate::mir::Local) {
        let Repr::Array(e) = repr else {
            let args = vec![one, other, witness_of(repr)];
            let same = self
                .b
                .define_op(Repr::Scalar, Rvalue::Runtime(Runtime::Same, args));
            let both = Rvalue::Prim(
                Prim::BitAnd,
                vec![Operand::Local(all), same],
                Operand::word(0),
            );
            return self.b.assign(all, both);
        };
        let starts = [one, other].map(|w| (self.word_in_memory(w, repr), e.element_words()));
        let (at, _) = crate::mir::offsets(e.each().iter().copied());
        let mut each = |l: &mut Self, elements: &[Operand], _| {
            for (&r, &k) in e.each().iter().zip(&at) {
                let words = [0, 1].map(|j| {
                    let p = l.offset(elements[j].clone(), k);
                    l.b.define_op(r, Rvalue::Load(p))
                });
                let [x, y] = words;
                l.same_word((x, y), r, all);
            }
        };
        self.each_array_element(&starts, e.len(), &mut each);
    }

    pub(crate) fn matches(
        &mut self,
        p: &Pat,
        v: Vec<Operand>,
        mutable: bool,
        then: Then<'_, 'a>,
        fail: BlockId,
    ) {
        match &p.kind {
            PatKind::Wild => then(self, fail),
            PatKind::Bind(id) => {
                let locals = self.bind_locals(*id, &p.ty, mutable);
                for (i, l) in locals.into_iter().enumerate() {
                    self.b.assign(l, Rvalue::Use(word(&v, i)));
                }
                then(self, fail);
            }
            PatKind::Int(_) | PatKind::Bool(_) | PatKind::Str(_) | PatKind::Const(_) => {
                let same = self.literal_test(p, &v);
                self.test(same, fail);
                then(self, fail);
            }
            PatKind::Tuple(ps) => {
                let fields = self.fields_of(&p.ty, 0);
                let items = (0..ps.len())
                    .map(|j| (&ps[j], self.field_words(&v, &fields, j)))
                    .collect::<Vec<_>>();
                self.match_all(&items, mutable, then, fail);
            }
            // A shape's case reads the descriptor (meta.shapes).
            PatKind::Variant(item, ps) if stilt_types::ty::is_shape_case(item) => {
                self.match_shape(item, ps, &v, mutable, then, fail);
            }
            PatKind::Variant(item, ps) => {
                self.match_variant(item, ps, &p.ty, &v, mutable, then, fail);
            }
            PatKind::Record(fields) => self.match_record(p, fields, &v, mutable, then, fail),
            // A list pattern on an array fits its size, which checking compared: its elements
            // are matched as a tuple's (generics.array-patterns).
            PatKind::List(ps, _) if p.ty.arrayed().is_some() => {
                let elements = self.elements_of(&v, &p.ty, ps.len());
                let items = ps.iter().zip(elements).collect::<Vec<_>>();
                self.match_all(&items, mutable, then, fail);
            }
            PatKind::List(ps, rest) => self.match_list(p, ps, *rest, &v, mutable, then, fail),
            PatKind::Or(alternatives) => {
                let (last, rest) = alternatives
                    .split_last()
                    .expect("an or-pattern has alternatives");
                for alternative in rest {
                    let next = self.b.new_block();
                    self.matches(alternative, v.clone(), mutable, then, next);
                    self.b.switch_to(next);
                }
                self.matches(last, v, mutable, then, fail);
            }
            // A pattern with an error, whose bindings the code after it may read: the
            // function panics in place of running (program.programs-with-errors).
            PatKind::Error => {
                self.b.met_error();
                self.b.terminate(Terminator::Unreachable);
            }
        }
    }

    /// Matches each pattern against its value, from left to right.
    pub(crate) fn match_all(
        &mut self,
        items: &[(&Pat, Vec<Operand>)],
        mutable: bool,
        then: Then<'_, 'a>,
        fail: BlockId,
    ) {
        match items.split_first() {
            None => then(self, fail),
            Some(((p, v), rest)) => {
                let mut after = |l: &mut Lower<'a>, f: BlockId| l.match_all(rest, mutable, then, f);
                self.matches(p, v.clone(), mutable, &mut after, fail);
            }
        }
    }

    /// Whether a value of type `ty` is variant `index` of it: by its tag word, the immediate of
    /// the index, when it is held inline, and otherwise by its object's tag or its immediate.
    pub(crate) fn is_variant(&mut self, v: &[Operand], ty: &Ty, index: u32) -> Operand {
        if self.only_object(ty, index) {
            // The one variant held in an object: a value is it when its word is a pointer,
            // whose lowest bit is 0, where every other variant's immediate has it set.
            let low = self.b.define_op(
                Repr::Scalar,
                Rvalue::Prim(
                    Prim::BitAnd,
                    vec![word(v, 0), Operand::word(1)],
                    Operand::word(0),
                ),
            );
            return self.word_eq(low, Operand::word(0));
        }
        if self.fields_of(ty, index as usize).object.is_some() {
            let tag = self.b.define_op(Repr::Scalar, Rvalue::Tag(word(v, 0)));
            self.word_eq(tag, Operand::word(u64::from(index)))
        } else {
            self.word_eq(word(v, 0), Operand::word(immediate(index)))
        }
    }

    /// Whether variant `index` of `ty` is the only one of its variants that a value of it holds
    /// in an object, every other being an immediate.
    fn only_object(&self, ty: &Ty, index: u32) -> bool {
        let Ty::Con(item, args) = ty else {
            return false;
        };
        let instance = self.instance_of(item, args);
        instance.heap
            && instance.tagged
            && instance
                .variants
                .iter()
                .enumerate()
                .all(|(k, (words, _))| words.is_empty() != (k == index as usize))
    }

    #[allow(clippy::too_many_arguments)]
    fn match_variant(
        &mut self,
        item: &stilt_hir::hir::Item,
        ps: &[Pat],
        ty: &Ty,
        v: &[Operand],
        mutable: bool,
        then: Then<'_, 'a>,
        fail: BlockId,
    ) {
        let index = self.variant_index(item);
        let same = self.is_variant(v, ty, index);
        self.test(same, fail);
        let fields = self.fields_of(ty, index as usize);
        let items = (0..ps.len())
            .map(|j| (&ps[j], self.field_words(v, &fields, j)))
            .collect::<Vec<_>>();
        self.match_all(&items, mutable, then, fail);
    }

    #[allow(clippy::too_many_arguments)]
    fn match_record(
        &mut self,
        p: &Pat,
        fields: &[(stilt_hir::hir::Name, Pat)],
        v: &[Operand],
        mutable: bool,
        then: Then<'_, 'a>,
        fail: BlockId,
    ) {
        let declared = self.fields_of(&p.ty, 0);
        let items: Vec<(&Pat, Vec<Operand>)> = fields
            .iter()
            .map(|(name, q)| {
                let j = self.field_index(&p.ty, name);
                (q, self.field_words(v, &declared, j))
            })
            .collect();
        self.match_all(&items, mutable, then, fail);
    }

    /// A list pattern: an exact length, or at least the patterns' number with a rest, whose
    /// binding holds the elements after them (patterns.pattern-forms).
    #[allow(clippy::too_many_arguments)]
    fn match_list(
        &mut self,
        p: &Pat,
        ps: &[Pat],
        rest: ListRest,
        v: &[Operand],
        mutable: bool,
        then: Then<'_, 'a>,
        fail: BlockId,
    ) {
        let list = word(v, 0);
        let n = Operand::word(ps.len() as u64);
        let len = self.b.define_op(
            Repr::Scalar,
            Rvalue::Runtime(Runtime::ListLen, vec![list.clone()]),
        );
        let fits = match rest {
            ListRest::Exact => self.word_eq(len.clone(), n.clone()),
            _ => self.le(NumKind::I64, n.clone(), len.clone()),
        };
        self.test(fits, fail);
        let items: Vec<(&Pat, Vec<Operand>)> = ps
            .iter()
            .enumerate()
            .map(|(i, q)| {
                let at = self.loc_at(q.at);
                let i = Operand::word(i as u64);
                (q, self.list_element(list.clone(), i, at, &q.ty))
            })
            .collect();
        let list_ty = p.ty.clone();
        let mut after = |l: &mut Lower<'a>, f: BlockId| {
            if let ListRest::Bind(id) = rest {
                let slice = Rvalue::Runtime(
                    Runtime::ListSlice,
                    vec![list.clone(), n.clone(), len.clone()],
                );
                let tail = l.b.define_op(Repr::Heap, slice);
                let locals = l.bind_locals(id, &list_ty, mutable);
                l.b.assign(locals[0], Rvalue::Use(tail));
            }
            then(l, f);
        };
        self.match_all(&items, mutable, &mut after, fail);
    }
}
