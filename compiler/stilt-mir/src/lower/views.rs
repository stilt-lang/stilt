//! Views and iterators in compiled code (views.what-view-is). A view is the word of its source, a
//! string or a list, with a reference of its own that keeps the source's storage alive, and two
//! offsets into it, held inline (views.what-view-is): making one, its length and its
//! parts compile inline, the runtime checking the offsets (views.making-view), and the rest of its
//! functions are natives, as every function of iterators is (`stilt_runtime::iter`). A `for` over
//! a view of a list reads the list's elements in place, and one over an iterator pulls its elements
//! as its body asks for them (views.for-over-view and views.laziness).

use stilt_hir::decls::prelude_item;
use stilt_types::tast::{self, Block, Callee, Expr, Pat};
use stilt_types::ty::{Ty, is_view_type};

use super::Lower;
use super::words::word;
use crate::mir::{NumKind, Operand, Prim, Repr, Runtime, Rvalue, Views};

/// The functions of `View` that compile inline.
fn inline(name: &str) -> bool {
    matches!(name, "of" | "all" | "view" | "len" | "is_empty")
}

impl Lower<'_> {
    /// A call of a function of `View` that compiles inline, if `callee` names one.
    pub(crate) fn view_call(
        &mut self,
        callee: &Callee,
        args: &[tast::Arg],
        e: &Expr,
    ) -> Option<Vec<Operand>> {
        let Callee::Member(owner, name) = callee else {
            return None;
        };
        if !is_view_type(owner, "View") || !inline(name) {
            return None;
        }
        let words: Vec<Operand> = args.iter().flat_map(|a| self.expr(&a.value)).collect();
        let loc = self.loc_at(e.at);
        Some(self.view_native(name, &words, loc))
    }

    /// The function of `View` named `name`, if it compiles inline, on the words of its
    /// arguments, the native's own words, as a function used as a value gives them.
    pub(crate) fn inline_view(
        &mut self,
        f: &crate::FnRef,
        words: &[Operand],
    ) -> Option<Vec<Operand>> {
        let crate::FnRef::Member(owner, name) = f else {
            return None;
        };
        if !is_view_type(owner, "View") || !inline(name) {
            return None;
        }
        let loc = Operand::Local(self.loc);
        Some(self.view_native(name, words, loc))
    }

    /// `View.of`, `View.all`, `v.view`, `v.len()` or `v.is_empty()` on the words of the
    /// arguments, a view's three: the source, its start and its end.
    fn view_native(&mut self, name: &str, words: &[Operand], loc: Operand) -> Vec<Operand> {
        let w = |i: usize| word(words, i);
        let add = |l: &mut Self, a: Operand, b: Operand| {
            let sum = Rvalue::Prim(Prim::AddWrap(NumKind::I64), vec![a, b], Operand::word(0));
            l.b.define_op(Repr::Scalar, sum)
        };
        match name {
            "of" => {
                let source = self.rt(
                    Repr::Heap,
                    Runtime::Views(Views::Of),
                    vec![loc, w(0), w(1), w(2)],
                );
                vec![source, w(1), w(2)]
            }
            "all" => {
                let len = self.rt(Repr::Scalar, Runtime::Views(Views::Len), vec![w(0)]);
                let args = vec![loc, w(0), Operand::word(0), len.clone()];
                let source = self.rt(Repr::Heap, Runtime::Views(Views::Of), args);
                vec![source, Operand::word(0), len]
            }
            "view" => {
                let args = vec![loc, w(0), w(1), w(2), w(3), w(4)];
                let source = self.rt(Repr::Heap, Runtime::Views(Views::Part), args);
                let start = add(self, w(1), w(3));
                let end = add(self, w(1), w(4));
                vec![source, start, end]
            }
            "len" => {
                let len = Rvalue::Prim(Prim::SubWrap(NumKind::I64), vec![w(2), w(1)], loc);
                vec![self.b.define_op(Repr::Scalar, len)]
            }
            _ => {
                let empty = Rvalue::Prim(Prim::Eq(NumKind::I64), vec![w(1), w(2)], loc);
                vec![self.b.define_op(Repr::Scalar, empty)]
            }
        }
    }

    /// `v[i]` on a view of a list, which panics with `bounds` as `xs[i]` does
    /// (views.functions-of-views).
    pub(crate) fn view_index(&mut self, view: &Expr, key: &Expr, e: &Expr) -> Vec<Operand> {
        let words = self.expr(view);
        let i = self.expr1(key);
        let loc = self.loc_at(e.at);
        let args = vec![loc.clone(), word(&words, 1), word(&words, 2), i];
        let at = self.rt(Repr::Scalar, Runtime::Views(Views::Index), args);
        self.list_index(word(&words, 0), at, loc, &e.ty)
    }

    /// A method of `Show`, `Eq`, `Ord` or `Hash` on views of type `ty`, each given by its words
    /// (views.functions-of-views): the viewed parts read in place by the runtime, through the
    /// dictionary of the viewed list's elements, which a view's structural environment holds in
    /// place of the viewed type's (`super::dicts`). Only `show` allocates, the text it gives.
    pub(crate) fn view_trait(&mut self, name: &str, ty: &Ty, values: &[&[Operand]]) -> Operand {
        let viewed = ty.viewed().cloned().unwrap_or(Ty::Error);
        let (method, trait_name, repr) = match name {
            "eq" => (Views::Eq, "Eq", Repr::Scalar),
            "compare" => (Views::Compare, "Ord", Repr::Scalar),
            "hash" => (Views::Hash, "Hash", Repr::Scalar),
            _ => (Views::Show, "Show", Repr::Heap),
        };
        // Inside a view's structural impl the viewed type is its parameter, whose dictionaries
        // are the elements'; a known list type gives its elements' directly.
        let elements = viewed.listed().cloned().unwrap_or(viewed);
        let dict = self.dict(&elements, &prelude_item(trait_name));
        let mut args = vec![Operand::Local(self.loc), dict];
        for v in values {
            args.extend([word(v, 0), word(v, 1), word(v, 2)]);
        }
        if method == Views::Show {
            args.push(Operand::word(u64::from(name == "show_nested")));
        }
        self.rt(repr, Runtime::Views(method), args)
    }

    /// `for p in v { body }` over a view of a list: its elements from its start up to its end,
    /// read in place.
    pub(crate) fn for_view(&mut self, p: &Pat, source: &Expr, b: &Block) {
        let words = self.expr(source);
        let list = self.b.define_op(Repr::Heap, Rvalue::Use(word(&words, 0)));
        let end = word(&words, 2);
        let i = self.b.temp(Repr::Scalar);
        self.b.assign(i, Rvalue::Use(word(&words, 1)));
        let (head, body, next, exit) = self.loop_blocks();
        self.b.goto(head);
        self.b.switch_to(head);
        let more = self.lt(NumKind::I64, Operand::Local(i), end);
        self.b.branch(more, body, exit);
        self.b.switch_to(body);
        let at = self.loc_at(source.at);
        let x = self.list_element(list, Operand::Local(i), at, &p.ty);
        self.binding(p, x, false, None);
        self.loop_body(b, exit, next);
        self.b.switch_to(next);
        self.step(i);
        self.b.goto(head);
        self.b.switch_to(exit);
    }

    /// `for p in it { body }` over an iterator: each element pulled as the body asks for it,
    /// the closures of the iterator's adapters running then, through a state of the loop's own.
    pub(crate) fn for_iter(&mut self, p: &Pat, source: &Expr, b: &Block) {
        let it = self.expr1(source);
        let it = self.b.define_op(Repr::Heap, Rvalue::Use(it));
        let state = self.rt(Repr::Heap, Runtime::Views(Views::State), vec![it.clone()]);
        let (head, body, next, exit) = self.loop_blocks();
        self.b.goto(head);
        self.b.switch_to(head);
        let loc = self.loc_at(source.at);
        let more = self.rt(
            Repr::Scalar,
            Runtime::Views(Views::Next),
            vec![loc, it, state.clone()],
        );
        self.b.branch(more, body, exit);
        self.b.switch_to(body);
        let repr = self.repr(&p.ty);
        let x = self.rt(repr, Runtime::Views(Views::Take), vec![state]);
        let words = self.unbox(x, &p.ty);
        self.binding(p, words, false, None);
        self.loop_body(b, exit, next);
        self.b.switch_to(next);
        self.b.goto(head);
        self.b.switch_to(exit);
    }
}
