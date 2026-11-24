//! Packs whose length is known at run time only: those of a function's code
//! compiled for every length, which a call whose pack grows within its own cycle of the call
//! graph reaches, as polymorphic recursion does.
//!
//! The code takes the pack's length, its elements' layouts and its dictionaries at run time:
//! a list of the elements' witnesses and, for each of the pack's bounds, a list of their
//! dictionaries, which a generic of the pack holds, the witnesses' list among its
//! dictionaries. A tuple whose type spreads such a pack is a list of its elements, each in a
//! box of one field that holds it in the one word that holds it where a type parameter stands.
//! A spread is a loop over its pack's elements, whose body has a generic of its own for the
//! element, its witness and dictionaries read from the pack's lists.

use stilt_hir::hir::{DeclId, GenericId, Item, LocalId, Name, Owner};
use stilt_types::tast::{Expr, ExprKind, SpreadExpr};
use stilt_types::ty::Ty;

use super::super::{Lower, Var};
use super::local_type;
use crate::Held;
use crate::mir::{Arg, Heapness, NumKind, Operand, Repr, Runtime, Rvalue, Stmt};
use crate::shape;

/// The pseudo-bound under which a dynamic pack's generic holds its list of witnesses.
fn witnesses_item() -> Item {
    Item {
        home: Name::from("#pack"),
        name: Name::from("witnesses"),
    }
}

/// The generic that stands for the element a spread of `of` is at, in its loop.
fn loop_element(of: &GenericId) -> GenericId {
    GenericId {
        owner: Owner {
            decl: DeclId {
                module: format!("#each:{}:{}", of.owner.decl.module, of.owner.decl.index).into(),
                index: of.owner.member.unwrap_or(u32::MAX),
            },
            member: None,
        },
        index: of.index,
    }
}

/// Whether a tuple type spreads a pack that no instance expands, so that its values are lists.
pub(crate) fn is_dynamic_tuple(ty: &Ty) -> bool {
    matches!(ty, Ty::Tuple(ts) if ts.iter().any(|t| t.as_spread().is_some()))
}

/// Where a spread's values go: into a tuple's list of boxes, or a list of their type.
enum Sink {
    Pack(crate::mir::Local),
    List(crate::mir::Local, Ty),
}

/// Whether an expression gives the local `v`, or holds it in the value it builds, so that a
/// spread with it as its body uses each element of the tuple `v` names by value, as building a
/// tuple does (values.passing-values).
fn stores(e: &Expr, v: LocalId) -> bool {
    match &e.kind {
        ExprKind::Local(w) => *w == v,
        ExprKind::Tuple(es) | ExprKind::List(es) | ExprKind::Construct(_, _, es) => {
            es.iter().any(|e| stores(e, v))
        }
        ExprKind::Record(_, _, fields) => fields.iter().any(|(_, e)| stores(e, v)),
        ExprKind::Update(base, fields) => {
            stores(base, v) || fields.iter().any(|(_, e)| stores(e, v))
        }
        _ => false,
    }
}

impl Lower<'_> {
    /// A pack tuple's list, rebound as a `var` binding is, which takes it by value: the code
    /// consumes it, as one that moves a tuple into another does (values.consumed-parameters).
    fn owned(&mut self, list: Operand) -> Operand {
        let local = self.b.temp(Repr::Heap);
        self.b.decl_mut(local).var = true;
        self.b.assign(local, Rvalue::Use(list));
        Operand::Local(local)
    }

    /// Brings the pack `g`, bounded by `traits`, into scope as its length is known at run time
    /// only: its parameters are the list of its elements' witnesses, then a list of their
    /// dictionaries for each bound.
    pub(crate) fn add_dynamic_pack(&mut self, g: &GenericId, traits: &[Item]) {
        let param = |l: &mut Self| l.b.param(Repr::Heap, crate::mir::ParamMode::Borrowed, None);
        let witnesses = param(self);
        let mut lists = Vec::new();
        for t in super::super::records::dict_bounds(traits) {
            lists.push((t, param(self)));
        }
        self.push_dynamic_pack(g, witnesses, lists);
    }

    /// Brings the dynamic pack `g` into scope with its lists: its witnesses', and its
    /// dictionaries' for each bound.
    pub(crate) fn push_dynamic_pack(
        &mut self,
        g: &GenericId,
        witnesses: crate::mir::Local,
        lists: impl IntoIterator<Item = (Item, crate::mir::Local)>,
    ) {
        let mut dicts = vec![(witnesses_item(), Operand::Local(witnesses))];
        dicts.extend(lists.into_iter().map(|(t, l)| (t, Operand::Local(l))));
        let none = self.b.define(Repr::Scalar, Rvalue::Use(Operand::word(0)));
        self.push_generic(Ty::Param(g.clone()), none, dicts, Some(&Held::Word));
    }

    /// The lists of a dynamic pack in scope: its witnesses', and its dictionaries' by bound.
    fn pack_lists(&self, g: &GenericId) -> Option<(Operand, Vec<(Item, Operand)>)> {
        let generic = self.generic(&Ty::Param(g.clone()))?;
        let mut dicts = generic.dicts.clone();
        let at = dicts.iter().position(|(t, _)| *t == witnesses_item())?;
        let (_, witnesses) = dicts.remove(at);
        Some((witnesses, dicts))
    }

    /// The hidden arguments of a pack bounded by `traits`, instantiated with the elements `ty`
    /// holds, for code that takes its length at run time.
    pub(crate) fn dynamic_pack_args(&mut self, traits: &[Item], ty: &Ty) -> Vec<Arg> {
        let ts = match ty {
            Ty::Tuple(ts) => stilt_types::ty::Table::default().elements(ts),
            _ => Vec::new(),
        };
        let (witnesses, dicts) = self.dynamic_lists(&ts, traits);
        std::iter::once(witnesses)
            .chain(dicts)
            .map(Arg::Borrow)
            .collect()
    }

    /// A new list that holds words of one heapness.
    fn new_list(&mut self, heap: bool) -> crate::mir::Local {
        let args = vec![Operand::word(0), Operand::word(shape::word(heap))];
        self.b
            .define(Repr::Heap, Rvalue::Runtime(Runtime::ListNew, args))
    }

    fn push_word(&mut self, list: crate::mir::Local, heap: bool, word: Operand) {
        let args = vec![Operand::Local(list), Operand::word(shape::word(heap)), word];
        self.b.emit(Stmt::Effect(Runtime::ListPush, args));
    }

    /// The list of the witnesses of the elements `ts` of a tuple type, and for each of
    /// `traits` the list of their dictionaries.
    pub(crate) fn dynamic_lists(&mut self, ts: &[Ty], traits: &[Item]) -> (Operand, Vec<Operand>) {
        let witnesses = self.new_list(false);
        let dicts: Vec<_> = traits.iter().map(|_| self.new_list(true)).collect();
        let push = |l: &mut Self, t: &Ty| {
            let w = l.witness(t);
            l.push_word(witnesses, false, w);
            for (tr, list) in traits.iter().zip(&dicts) {
                let d = if l.implements(t, tr) {
                    l.dict(t, tr)
                } else {
                    Operand::word(0)
                };
                l.push_word(*list, true, d);
            }
        };
        for t in ts {
            match t {
                Ty::Spread(s) => {
                    let Ty::Param(p) = self.cons.ty(&s.pack) else {
                        self.b.met_error();
                        continue;
                    };
                    let elem = s.elem.clone();
                    let of = s.of.clone();
                    self.each_element(&p, &of, &mut |l, e| {
                        let t = l.retyped_with(&elem, &of, e.clone());
                        push(l, &t);
                    });
                }
                t => push(self, t),
            }
        }
        let dicts = dicts.into_iter().map(Operand::Local).collect();
        (Operand::Local(witnesses), dicts)
    }

    /// Runs `body` once for each element of the dynamic pack `p`, in a loop, with a generic in
    /// scope for the element, which `of` stands for, its witness and dictionaries read from the
    /// pack's lists. The loop's index is the local `body` is given.
    fn each_loop(
        &mut self,
        p: &GenericId,
        of: &GenericId,
        body: &mut dyn FnMut(&mut Self, &Ty, Operand),
    ) {
        let Some((witnesses, dicts)) = self.pack_lists(p) else {
            self.b.met_error();
            return;
        };
        let len = self.b.define_op(
            Repr::Scalar,
            Rvalue::Runtime(Runtime::ListLen, vec![witnesses.clone()]),
        );
        let i = self.b.temp(Repr::Scalar);
        self.b.assign(i, Rvalue::Use(Operand::word(0)));
        let (head, block, next, exit) = self.loop_blocks();
        self.b.goto(head);
        self.b.switch_to(head);
        let more = self.lt(NumKind::I64, Operand::Local(i), len);
        self.b.branch(more, block, exit);
        self.b.switch_to(block);
        let at = |l: &mut Self, list: &Operand, heap: bool| {
            let args = vec![
                list.clone(),
                Operand::Local(i),
                Operand::word(shape::word(heap)),
                Operand::word(0),
            ];
            let repr = if heap { Repr::Heap } else { Repr::Scalar };
            l.b.define(repr, Rvalue::Runtime(Runtime::ListAt, args))
        };
        let w = at(self, &witnesses, false);
        let element_dicts = dicts
            .iter()
            .map(|(t, list)| (t.clone(), Operand::Local(at(self, list, true))))
            .collect();
        let e = Ty::Param(loop_element(of));
        self.push_generic(e.clone(), w, element_dicts, Some(&Held::Word));
        body(self, &e, Operand::Local(i));
        self.generics.pop();
        self.instances.borrow_mut().clear();
        self.b.goto(next);
        self.b.switch_to(next);
        self.step(i);
        self.b.goto(head);
        self.b.switch_to(exit);
    }

    fn each_element(
        &mut self,
        p: &GenericId,
        of: &GenericId,
        body: &mut dyn FnMut(&mut Self, &Ty),
    ) {
        self.each_loop(p, of, &mut |l, e, _| body(l, e));
    }

    /// A value of type `ty` in a box of one field, as a tuple of a dynamic pack holds it.
    pub(crate) fn cell(&mut self, words: Vec<Operand>, ty: &Ty) -> Operand {
        let word = self.boxed(words, ty);
        let heapness = Heapness::of(self.repr(ty));
        self.alloc(0, vec![(word, heapness)])
    }

    /// The words of the value of type `ty` in a box of a tuple of a dynamic pack, borrowed.
    pub(crate) fn uncell(&mut self, cell: Operand, ty: &Ty) -> Vec<Operand> {
        let repr = self.repr(ty);
        let word = self.b.define_op(
            repr,
            Rvalue::Field {
                base: cell,
                len: 1,
                index: 0,
                variant: None,
            },
        );
        self.unbox(word, ty)
    }

    /// Element `i` of a tuple of a dynamic pack, of type `ty`, borrowed.
    fn element_at(&mut self, list: Operand, i: Operand, ty: &Ty) -> Vec<Operand> {
        let args = vec![list, i, Operand::word(shape::word(true)), Operand::word(0)];
        let cell = self
            .b
            .define_op(Repr::Heap, Rvalue::Runtime(Runtime::ListAt, args));
        self.uncell(cell, ty)
    }

    /// Lowers a spread of a dynamic pack, sending each element's value to `sink`.
    fn dynamic_spread_into(&mut self, s: &SpreadExpr, sink: &Sink) {
        let Ty::Param(p) = self.cons.ty(&s.pack) else {
            self.b.met_error();
            return;
        };
        let mapped: Vec<(LocalId, Ty)> = s
            .mapped
            .iter()
            .filter_map(|v| local_type(&s.body, *v).map(|t| (*v, t)))
            .collect();
        let saved: Vec<(LocalId, Var)> = mapped
            .iter()
            .map(|(v, _)| (*v, self.vars[v].clone()))
            .collect();
        let lists: Vec<Operand> = mapped
            .iter()
            .map(|(v, t)| {
                let whole = Ty::Tuple(vec![Ty::spread(
                    Ty::Param(p.clone()),
                    s.of.clone(),
                    t.clone(),
                )]);
                let list = self.read_var(*v, &whole)[0].clone();
                if stores(&s.body, *v) {
                    self.owned(list)
                } else {
                    list
                }
            })
            .collect();
        self.each_loop(&p, &s.of, &mut |l, e, i| {
            for ((v, t), list) in mapped.iter().zip(&lists) {
                let ty = l.retyped_with(t, &s.of, e.clone());
                let words = l.element_at(list.clone(), i.clone(), &ty);
                let layout = l.layout(&ty);
                let locals = l.locals_of(words, &layout);
                l.vars.insert(
                    *v,
                    Var::Value {
                        locals,
                        mutable: false,
                    },
                );
            }
            let body = l.body_for(s, e.clone());
            l.elements.push((s.of.clone(), e.clone()));
            let words = l.expr(&body);
            l.elements.pop();
            match sink {
                Sink::Pack(list) => {
                    let cell = l.cell(words, &body.ty);
                    l.push_word(*list, true, cell);
                }
                Sink::List(list, elem) => l.push_fresh(*list, words, elem),
            }
        });
        for (v, var) in saved {
            self.vars.insert(v, var);
        }
    }

    /// A tuple of type `ty`, which spreads a dynamic pack: the list of its elements' boxes.
    pub(crate) fn dynamic_tuple(&mut self, es: &[Expr]) -> Vec<Operand> {
        let list = self.new_list(true);
        for e in es {
            if let ExprKind::Spread(s) = &e.kind {
                self.dynamic_spread_into(s, &Sink::Pack(list));
            } else {
                let words = self.expr(e);
                let cell = self.cell(words, &e.ty);
                self.push_word(list, true, cell);
            }
        }
        vec![Operand::Local(list)]
    }

    /// Whether one of the elements of a list or a tuple spreads a dynamic pack.
    pub(crate) fn spreads_dynamic(&self, es: &[Expr]) -> bool {
        es.iter().any(|e| match &e.kind {
            ExprKind::Spread(s) => super::static_elements(&self.cons.ty(&s.pack)).is_none(),
            _ => false,
        })
    }

    /// A list of type `ty` among whose elements is a spread of a dynamic pack.
    pub(crate) fn dynamic_list(&mut self, es: &[Expr], ty: &Ty) -> Operand {
        let element = super::super::lists::element_of(ty);
        let shape = self.witness(&element);
        let args = vec![Operand::word(0), shape];
        let list = self
            .b
            .define(Repr::Heap, Rvalue::Runtime(Runtime::ListNew, args));
        for e in es {
            if let ExprKind::Spread(s) = &e.kind {
                self.dynamic_spread_into(s, &Sink::List(list, element.clone()));
            } else {
                let words = self.expr(e);
                self.push_fresh(list, words, &element);
            }
        }
        Operand::Local(list)
    }

    /// A spread among a call's arguments, in code that takes its pack's length at run time,
    /// which no program runs. Arguments are spread only into a function value whose type spreads
    /// the same pack (variadics.spread-checks), and no value of such a type can be made for a pack
    /// that grows: a closure literal and a function have as many parameters as they are written
    /// with, and a function value of the pack's type is only passed on, at the length it came with.
    /// So a pack whose length is taken at run time, which only growth gives
    /// (`super::is_dynamic_at`), never reaches such a call, and only the code compiled for every
    /// length, which no call with a key reaches for such a pack, holds one: it ends there.
    pub(crate) fn dynamic_spread(&mut self, _s: &SpreadExpr) -> (Vec<Operand>, Ty) {
        self.b.terminate(crate::mir::Terminator::Unreachable);
        (vec![Operand::word(0)], Ty::unit())
    }

    /// The list of boxes of a tuple of the elements `ts`, from its words.
    pub(crate) fn pack_of_words(&mut self, words: &[Operand], ty: &Ty) -> Operand {
        let list = self.new_list(true);
        let fields = self.fields_of(ty, 0);
        for j in 0..fields.all.len() {
            let t = fields.all[j].ty.clone();
            let w = self.field_words(words, &fields, j);
            let cell = self.cell(w, &t);
            self.push_word(list, true, cell);
        }
        Operand::Local(list)
    }

    /// The words of a tuple of type `ty` from the list of boxes of its elements.
    pub(crate) fn words_of_pack(&mut self, list: &Operand, ty: &Ty) -> Vec<Operand> {
        let fields = self.fields_of(ty, 0);
        let values = fields
            .all
            .iter()
            .enumerate()
            .map(|(k, f)| self.element_at(list.clone(), Operand::word(k as u64), &f.ty))
            .collect();
        self.build(ty, 0, values)
    }
}
