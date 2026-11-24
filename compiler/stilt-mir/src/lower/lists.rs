//! Lists (std.lists; facts.allocation; goal inline-values): how a list holds the elements
//! of a type, and reading, appending and building them.
//!
//! A list holds each element in the words of its type's layout, one after the other, and a
//! scalar narrower than a word in its own width, so that reading `xs[i].f` reads one word,
//! `let b = xs[i]` copies the element's words, and `xs[i].f = v` writes one in place, whatever
//! the element's size. Code that names the element type knows where each element's words are, and so does generic
//! code compiled for an element type of several words, which holds its values in the same
//! words. Generic code whose element type is a type parameter held in one word reads and writes
//! an element in that word, which the runtime converts by the list's shape, which the witness of
//! the type parameter gave the list when it was made (`crate::shape`): a narrow scalar widened,
//! or the box of a value of several words, as code past the caps of instances holds it
//! (`super::bridge`).

use stilt_syntax::TextRange;
use stilt_types::tast::{self, Expr, ExprKind};
use stilt_types::ty::Ty;
use stilt_types::verify::Check;

use super::Lower;
use super::calls::Forms;
use super::words::{witness_of, word};
use crate::mir::{Arg, Const, Local, Operand, Repr, Runtime, Rvalue, Stmt};
use crate::repr::num_kind;
use crate::shape;

/// How a list holds the elements of a type, as the code that names the type knows it.
#[derive(Clone, Debug)]
pub(crate) enum Elem {
    /// In the words of the type's layout, or a scalar narrower than a word in its own width, as
    /// the constant `shape` says ([`shape::sized`]). Compiled code reads only its size and
    /// width: the runtime counts an element's heap words by the shape the list was made with
    /// ([`Lower::witness`]).
    Inline { shape: u64 },
    /// A value of a type parameter held in one word, whose witness, this operand, tells its
    /// shape when the code runs.
    Dynamic(Operand),
}

impl Elem {
    /// Whether an element is a scalar narrower than a word.
    pub(crate) fn packed(&self) -> bool {
        matches!(self, Elem::Inline { shape, .. } if shape::size(*shape) < 8)
    }
}

/// The element type of a list type.
pub(crate) fn element_of(list: &Ty) -> Ty {
    match list {
        Ty::Con(_, args) => args.first().cloned().unwrap_or(Ty::Error),
        _ => Ty::Error,
    }
}

/// The shape of a scalar type narrower than a word, which a list packs: a `bool`, an `i8` or
/// a `u8` in a byte, an `i16` or a `u16` in two, and an `i32`, a `u32` or an `f32` in four.
fn packed(ty: &Ty) -> Option<u64> {
    if let Some(kind) = num_kind(ty) {
        let bits = kind.bits();
        return (bits < 64).then(|| shape::packed(u64::from(bits / 8), kind.is_signed()));
    }
    matches!(ty, Ty::Con(item, args) if args.is_empty() && &*item.home == "std.prelude"
        && &*item.name == "bool")
    .then(|| shape::packed(1, false))
}

impl Lower<'_> {
    /// How a list holds the elements of type `ty`.
    pub(crate) fn elem(&mut self, ty: &Ty) -> Elem {
        if matches!(ty, Ty::Param(_) | Ty::SelfTy) && self.one_word(ty) {
            return Elem::Dynamic(self.witness(ty));
        }
        if let Some(shape) = packed(ty) {
            return Elem::Inline { shape };
        }
        Elem::Inline {
            shape: shape::sized(&heap_words(&self.layout(ty))),
        }
    }

    /// The witness of a type: its shape (`crate::shape`), a constant, or for a type parameter
    /// its own witness, or the shape computed from the witnesses of the type parameters whose
    /// words its layout holds, or that the runtime makes for a value of more than
    /// [`shape::MASK_WORDS`] words.
    pub(crate) fn witness(&mut self, ty: &Ty) -> Operand {
        // A value parameter's hidden argument is its value.
        if let Ty::Value(v) = ty {
            return Operand::word(super::values::value_word(v));
        }
        let layout = if matches!(ty, Ty::Param(_) | Ty::SelfTy) {
            match self.generic(ty) {
                None => return Operand::word(shape::word(true)),
                Some(g) => match &g.held {
                    Some(words) if !words.iter().any(|r| matches!(r, Repr::Generic(_))) => {
                        words.clone()
                    }
                    _ => return Operand::Local(g.witness),
                },
            }
        } else if let Some(shape) = packed(ty) {
            return Operand::word(shape);
        } else {
            self.layout(ty)
        };
        let generic = layout.iter().any(|r| !r.witnesses().is_empty());
        if !generic && let Some(shape) = shape::of_words(&heap_words(&layout)) {
            return Operand::word(shape);
        }
        self.shape_of_layout(&layout)
    }

    /// The shape of a value of the words `layout`, which the runtime makes: from the heapness
    /// of each word, or for a layout that holds an array in memory, from its parts, each a
    /// number of values of a shape, so that the code is the same whatever the array's size.
    fn shape_of_layout(&mut self, layout: &[Repr]) -> Operand {
        if !layout.iter().any(|r| matches!(r, Repr::Array(_))) {
            let words = layout.iter().copied().map(witness_of).collect();
            return self
                .b
                .define_op(Repr::Scalar, Rvalue::Runtime(Runtime::Shape, words));
        }
        let mut parts = Vec::new();
        for &r in layout {
            let (count, each) = match r {
                Repr::Array(e) => (u64::from(e.len()), self.shape_of_layout(e.each())),
                _ => (1, self.shape_of_layout(&[r])),
            };
            parts.extend([Operand::word(count), each]);
        }
        self.b
            .define_op(Repr::Scalar, Rvalue::Runtime(Runtime::ShapeParts, parts))
    }

    /// The words of `xs[i]`, borrowed, of type `ty`, or the panic at `loc` when `i` is out of
    /// bounds; for a value of a type parameter, its one word, with references of its own.
    pub(crate) fn list_index(
        &mut self,
        list: Operand,
        i: Operand,
        loc: Operand,
        ty: &Ty,
    ) -> Vec<Operand> {
        self.element_words(list, i, Some(loc), ty)
    }

    /// The words of element `i`, which is in bounds, of a list of elements of type `ty`, as
    /// [`Lower::list_index`] reads them. `at` is a location to report a panic at that can't
    /// happen.
    pub(crate) fn list_element(
        &mut self,
        list: Operand,
        i: Operand,
        at: Operand,
        ty: &Ty,
    ) -> Vec<Operand> {
        if let Elem::Dynamic(_) = self.elem(ty) {
            return self.element_words(list, i, Some(at), ty);
        }
        self.element_words(list, i, None, ty)
    }

    /// The words of an element, checked to be in bounds if `loc` is given, the first word
    /// read by the check.
    fn element_words(
        &mut self,
        list: Operand,
        i: Operand,
        loc: Option<Operand>,
        ty: &Ty,
    ) -> Vec<Operand> {
        match self.elem(ty) {
            Elem::Dynamic(w) => {
                let loc = loc.unwrap_or(Operand::word(0));
                let get = Rvalue::Runtime(Runtime::ListGet, vec![loc, list, i, w]);
                let repr = self.repr(ty);
                vec![self.b.define_op(repr, get)]
            }
            Elem::Inline { shape, .. } => {
                let layout = self.layout(ty);
                let (at, _) = crate::mir::offsets(layout.iter().copied());
                let words = at.into_iter().zip(layout);
                self.words_at((&list, &i), loc, shape, words)
            }
        }
    }

    /// The words at the word offsets given, each with its representation, of element `i` of a
    /// list of elements of the constant shape `shape`, borrowed: the first read by the check
    /// that `i` is in bounds if `loc` is given.
    fn words_at(
        &mut self,
        (list, i): (&Operand, &Operand),
        mut loc: Option<Operand>,
        shape: u64,
        words: impl Iterator<Item = (usize, Repr)>,
    ) -> Vec<Operand> {
        words
            .map(|(at, repr)| {
                let (at, shape) = (Operand::word(at as u64), Operand::word(shape));
                let (list, i) = (list.clone(), i.clone());
                let read = match loc.take() {
                    Some(loc) => Rvalue::Runtime(Runtime::ListIndex, vec![loc, list, i, shape, at]),
                    None => Rvalue::Runtime(Runtime::ListAt, vec![list, i, shape, at]),
                };
                self.b.define_op(repr, read)
            })
            .collect()
    }

    /// The words of the part of a list's element held inline that a path of fields reads, if
    /// `e` reads one, and only those.
    pub(crate) fn read_element_part(&mut self, e: &Expr) -> Option<Vec<Operand>> {
        if matches!(e.kind, ExprKind::Index(..)) {
            return None;
        }
        let part = self.element_part(e)?;
        let list = self.expr1(part.list);
        let key = self.expr(part.key);
        let loc = self.proved_at(part.at, &[Check::Bounds]);
        Some(self.read_part((&list, &word(&key, 0)), loc, &part.part))
    }

    /// The words of a part of `xs[i]`, an element held inline, the first checked to be in
    /// bounds at `loc`.
    pub(crate) fn read_part(
        &mut self,
        (list, i): (&Operand, &Operand),
        loc: Operand,
        part: &Part,
    ) -> Vec<Operand> {
        let layout = self.layout(&part.element);
        let (at, _) = crate::mir::offsets(layout.iter().copied());
        let words = (part.start..part.start + part.len)
            .map(|j| (at.get(j).copied().unwrap_or(j), word_repr(&layout, j)));
        self.words_at((list, i), Some(loc), part.shape, words)
    }

    /// The part of a list's element held inline that `e` reaches, through fields of values held
    /// inline, if it reaches one.
    fn element_part<'e>(&mut self, e: &'e Expr) -> Option<ExprPart<'e>> {
        match &e.kind {
            ExprKind::Index(c, k) if c.ty.is_prelude("List") => {
                let part = self.part_of_element(&e.ty)?;
                Some(ExprPart {
                    list: c,
                    key: k,
                    at: e.at,
                    part,
                })
            }
            ExprKind::Field(b, name) => {
                let j = self.field_index(&b.ty, name);
                let p = self.element_part(b)?;
                let part = self.field_part(p.part, &b.ty, j)?;
                Some(ExprPart { part, ..p })
            }
            ExprKind::TupleField(b, j) => {
                let p = self.element_part(b)?;
                let part = self.field_part(p.part, &b.ty, *j)?;
                Some(ExprPart { part, ..p })
            }
            _ => None,
        }
    }

    /// The whole of an element of type `element`, if a list holds it inline in whole words.
    pub(crate) fn part_of_element(&mut self, element: &Ty) -> Option<Part> {
        match self.elem(element) {
            Elem::Inline { shape, .. } if shape::size(shape) >= 8 => Some(Part {
                element: element.clone(),
                shape,
                start: 0,
                len: self.layout(element).len(),
            }),
            _ => None,
        }
    }

    /// Field `j` of the part `part`, a value of type `ty`, if it is held inline.
    pub(crate) fn field_part(&self, part: Part, ty: &Ty, j: usize) -> Option<Part> {
        let fields = self.fields_of(ty, 0);
        let f = fields.all.get(j)?;
        if fields.object.is_some() {
            return None;
        }
        Some(Part {
            start: part.start + f.at.first()?,
            len: f.at.len(),
            ..part
        })
    }

    /// Appends a value's words, which it consumes, to a list that nothing else references, as
    /// a list of elements of type `ty` holds them.
    pub(crate) fn push_fresh(&mut self, list: Local, words: Vec<Operand>, ty: &Ty) {
        let (shape, words) = self.held_in_list(words, ty);
        let mut args = vec![Operand::Local(list), shape];
        args.extend(words);
        self.b.emit(Stmt::Effect(Runtime::ListPush, args));
    }

    /// The operand of the shape of the elements of type `ty` that code appending them passes,
    /// and the words of a value as the list holds it: its words, or its box.
    fn held_in_list(&mut self, words: Vec<Operand>, ty: &Ty) -> (Operand, Vec<Operand>) {
        match self.elem(ty) {
            Elem::Inline { shape, .. } => (Operand::word(shape), words),
            Elem::Dynamic(w) => (w, vec![self.boxed(words, ty)]),
        }
    }

    /// A list literal of type `ty` (std.lists).
    pub(crate) fn list_literal(&mut self, values: Vec<Vec<Operand>>, ty: &Ty) -> Operand {
        let element = element_of(ty);
        let shape = self.witness(&element);
        let n = Operand::word(values.len() as u64);
        let list = self.b.define(
            Repr::Heap,
            Rvalue::Runtime(Runtime::ListNew, vec![n, shape]),
        );
        for v in values {
            self.push_fresh(list, v, &element);
        }
        Operand::Local(list)
    }

    /// The concatenation of strings, which it consumes: the text of an interpolation or of a
    /// structural `show`. One string is the text itself, up to four are given to the runtime
    /// as they are, and more in a list.
    pub(crate) fn concat(&mut self, mut parts: Vec<Operand>) -> Operand {
        if parts.len() == 1 {
            let part = parts.remove(0);
            return self.b.define_op(Repr::Heap, Rvalue::Use(part));
        }
        let joined = match parts.len() {
            2 => Some(Runtime::Concat2),
            3 => Some(Runtime::Concat3),
            4 => Some(Runtime::Concat4),
            _ => None,
        };
        if let Some(f) = joined {
            return self.b.define_op(Repr::Heap, Rvalue::Runtime(f, parts));
        }
        let n = Operand::word(parts.len() as u64);
        let shape = Operand::word(shape::word(true));
        let list = self.b.define(
            Repr::Heap,
            Rvalue::Runtime(Runtime::ListNew, vec![n, shape.clone()]),
        );
        for p in parts {
            self.b.emit(Stmt::Effect(
                Runtime::ListPush,
                vec![Operand::Local(list), shape.clone(), p],
            ));
        }
        self.b.define_op(
            Repr::Heap,
            Rvalue::Runtime(Runtime::Concat, vec![Operand::Local(list)]),
        )
    }

    /// `xs.push(x)` (std.list-changes), which consumes `x`: on a list whose element type the code
    /// names, the element's words appended inline, with no box; in generic code, whose element
    /// type is a type parameter, the one word that holds the value, which an element of one word
    /// takes inline and the runtime converts for any other.
    pub(crate) fn push(&mut self, args: &[tast::Arg]) -> Option<Vec<Operand>> {
        let [receiver, _] = args else { return None };
        let element = element_of(&receiver.value.ty);
        let (values, writebacks) = self.arguments(args, &Forms::layout());
        let mut values = values.into_iter().flat_map(|a| match a {
            Arg::Borrow(o) | Arg::Own(o) | Arg::Ref(o) => vec![o],
            Arg::Lend(words) => words.into_iter().map(|(o, _)| o).collect(),
        });
        let slot = values.next()?;
        let (shape, words) = self.held_in_list(values.collect(), &element);
        let mut all = vec![slot, shape];
        all.extend(words);
        self.b.emit(Stmt::Effect(Runtime::ListAppend, all));
        self.write_back(&writebacks);
        Some(vec![Operand::Const(Const::Word(0))])
    }
}

/// Some words of a list's element held inline: those from `start`, `len` of them, of an
/// element of type `element` and shape `shape`.
#[derive(Clone, Debug)]
pub(crate) struct Part {
    element: Ty,
    shape: u64,
    pub(crate) start: usize,
    pub(crate) len: usize,
}

/// A part of `list[key]` that an expression reads, the index written at `at`.
struct ExprPart<'e> {
    list: &'e Expr,
    key: &'e Expr,
    at: TextRange,
    part: Part,
}

/// Whether each word of a layout is a heap word, those of an array held in memory each, and
/// a word of a type parameter's not.
pub(crate) fn heap_words(layout: &[Repr]) -> Vec<bool> {
    let mut out = Vec::new();
    for &r in layout {
        match r {
            Repr::Array(e) => {
                let each = heap_words(e.each());
                for _ in 0..e.len() {
                    out.extend_from_slice(&each);
                }
            }
            _ => out.push(r == Repr::Heap),
        }
    }
    out
}

/// The representation of word `j` of a layout.
fn word_repr(layout: &[Repr], j: usize) -> Repr {
    layout.get(j).copied().unwrap_or(Repr::Heap)
}
