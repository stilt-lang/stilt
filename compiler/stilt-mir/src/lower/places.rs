//! Places (expressions.assignment and expressions.places; values.inout-arguments,
//! values.assignment-order and values.compound-assignment-order): assigning to a variable or a part
//! of one, and passing one `inout`.
//!
//! A place's words are a variable's own locals while its path holds only fields of values
//! held inline, and those locals are assigned directly. Any other path is reached through a
//! pointer to its words, each object on the way made unique first, so that it is changed in
//! place, as copy-on-write allows: the variable's locals then live in memory, one after the
//! other. A field of an inline value adds an offset to the pointer; a field of a recursive
//! type's object and a list's element go into the object. Nothing a program can observe happens on such a path but a panic,
//! when an index is out of bounds, so this behaves as the reference interpreter's copy-in,
//! copy-out (Lean model, `InPlaceAgreement`). A path through a map's index calls the key type's
//! `hash` and `eq`, so there the place is read and written back exactly as the interpreter
//! does, once each; a list's element held in fewer bytes than its words, or that generic code
//! holds by its shape, is stored by the width or the shape (`indexed`).

use stilt_hir::hir::BinaryOp;
use stilt_syntax::TextRange;
use stilt_types::tast::{Expr, ExprKind};
use stilt_types::ty::Ty;
use stilt_types::verify::Check;

use super::lists::Elem;
use super::words::word;
use super::{Lower, Var, projections};
use crate::mir::{Const, Local, Operand, Repr, Runtime, Rvalue};
use crate::shape;

mod indexed;

pub(crate) use indexed::key_ty;

/// Where a place starts: a variable's locals, or an `inout` parameter's pointer.
#[derive(Clone, Debug)]
pub(crate) enum Root {
    Locals(Vec<Local>),
    Pointer(Local),
}

/// A step of a place's path.
#[derive(Clone, Debug)]
pub(crate) enum Step {
    /// `len` words from `offset` of a value held inline, the first `words` words into it in
    /// memory: a field or a tuple's element.
    Inline {
        offset: usize,
        len: usize,
        words: usize,
    },
    /// Field `field`, from word `offset`, of the object of `object` words that a value of a
    /// recursive type points to.
    Object {
        object: u32,
        field: usize,
        offset: usize,
    },
    /// Element `index` of an array of `size` elements of `width` words each, held inline, with its
    /// index evaluated: in bounds, or a panic with `bounds` at `loc` (generics.array-elements).
    Element {
        index: Operand,
        loc: Operand,
        size: i128,
        width: usize,
    },
    /// An index into a list or a map, of the container's type, with the key evaluated.
    Index {
        container: Box<Ty>,
        key: Vec<Operand>,
        loc: Operand,
    },
}

impl Step {
    fn through_map(&self) -> bool {
        matches!(self, Step::Index { container, .. } if container.is_prelude("Map"))
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Place {
    pub(crate) root: Root,
    pub(crate) steps: Vec<Step>,
    /// The type of the value at the end of each step, the root's first.
    types: Vec<Ty>,
}

/// What to do when a call that takes a copy of a place returns or raises: store the value the
/// callee left in `temps` back into the place.
#[derive(Clone, Debug)]
pub(crate) struct Writeback {
    place: Place,
    temps: Vec<Local>,
}

impl Place {
    fn through_map(&self) -> bool {
        self.steps.iter().any(Step::through_map)
    }

    fn ty(&self) -> &Ty {
        self.types.last().expect("a place has a type")
    }

    /// The type of the value before the last step: the container an index at the end indexes.
    pub(super) fn ty_before_end(&self) -> &Ty {
        let n = self.types.len();
        &self.types[n.saturating_sub(2)]
    }

    /// Whether the place's words are reached through a pointer, rather than being a run of
    /// its variable's own locals.
    fn needs_pointer(&self) -> bool {
        matches!(self.root, Root::Pointer(_))
            || self.steps.iter().any(|s| !matches!(s, Step::Inline { .. }))
    }

    /// The locals of a place that are its variable's own.
    fn own_locals(&self) -> Vec<Local> {
        let Root::Locals(locals) = &self.root else {
            return Vec::new();
        };
        let (mut start, mut len) = (0, locals.len());
        for s in &self.steps {
            if let Step::Inline { offset, len: n, .. } = s {
                start += offset;
                len = *n;
            }
        }
        locals.iter().skip(start).take(len).copied().collect()
    }
}

impl Lower<'_> {
    /// A place, with the index expressions of its path evaluated, from left to right.
    pub(crate) fn place(&mut self, e: &Expr) -> Place {
        let mut place = match &e.kind {
            // A root whose pointer a construct with projections recorded, or a projection's call
            // opened as a pointer to its yielded place (projections.call-is-place; `projections`).
            ExprKind::Local(_) | ExprKind::Project(..)
                if let Some(pointer) = self
                    .roots
                    .get(&projections::node(e))
                    .or_else(|| self.opened.get(&projections::node(e))) =>
            {
                return Place {
                    root: Root::Pointer(*pointer),
                    steps: Vec::new(),
                    types: vec![e.ty.clone()],
                };
            }
            ExprKind::Local(id) => {
                let root = match self.var(*id, &e.ty) {
                    Var::Ref(pointer) => Root::Pointer(pointer),
                    Var::Value { locals, .. } => Root::Locals(locals),
                };
                return Place {
                    root,
                    steps: Vec::new(),
                    types: vec![e.ty.clone()],
                };
            }
            ExprKind::Field(base, _) | ExprKind::TupleField(base, _) | ExprKind::Index(base, _) => {
                self.place(base)
            }
            // A place with an error, which may be anything (errors.error-type): the function
            // can't run, and a panic stands in for it (program.programs-with-errors).
            ExprKind::Error => {
                self.b.met_error();
                let word = self.b.temp(Repr::Scalar);
                return Place {
                    root: Root::Locals(vec![word]),
                    steps: Vec::new(),
                    types: vec![e.ty.clone()],
                };
            }
            _ => unreachable!("an assignment or inout argument whose target isn't a place"),
        };
        let step = self.step_of(e, place.ty().clone());
        place.steps.push(step);
        place.types.push(e.ty.clone());
        place
    }

    /// The step of a place that `e` takes from a value of type `base_ty`, its index evaluated.
    fn step_of(&mut self, e: &Expr, base_ty: Ty) -> Step {
        match &e.kind {
            ExprKind::Field(_, name) => {
                let j = self.field_index(&base_ty, name);
                self.field_step(&base_ty, j)
            }
            ExprKind::TupleField(_, i) => self.field_step(&base_ty, *i),
            ExprKind::Index(_, key) if let Some((elem, size)) = self.array_parts(&base_ty) => {
                Step::Element {
                    index: self.expr1(key),
                    loc: self.proved_at(e.at, &[Check::Bounds]),
                    size,
                    width: self.element_width(&elem),
                }
            }
            ExprKind::Index(_, key) => {
                let key = self.expr(key);
                let loc = if base_ty.is_prelude("List") {
                    self.proved_at(e.at, &[Check::Bounds])
                } else {
                    self.loc_at(e.at)
                };
                Step::Index {
                    container: Box::new(base_ty),
                    key,
                    loc,
                }
            }
            _ => unreachable!("a step of a place"),
        }
    }

    fn field_step(&self, ty: &Ty, j: usize) -> Step {
        let fields = self.fields_of(ty, 0);
        let Some(f) = fields.all.get(j) else {
            return Step::Inline {
                offset: 0,
                len: 1,
                words: 0,
            };
        };
        let (offset, len) = (f.at.first().copied().unwrap_or(0), f.at.len());
        match fields.object {
            None => {
                let (at, _) = crate::mir::offsets(self.layout(ty));
                let words = at.get(offset).copied().unwrap_or(0);
                Step::Inline { offset, len, words }
            }
            Some(object) => {
                let (at, words) = crate::mir::offsets(object.iter().copied());
                Step::Object {
                    object: u32::try_from(words).expect("under 4G words"),
                    field: j,
                    offset: at.get(offset).copied().unwrap_or(0),
                }
            }
        }
    }

    /// A pointer to the words of the place's root.
    pub(crate) fn root_slot(&mut self, root: &Root) -> Operand {
        match root {
            Root::Pointer(p) => Operand::Local(*p),
            Root::Locals(locals) => {
                self.b.make_slots(locals);
                let first = locals.first().copied().expect("a value has words");
                self.b.define_op(Repr::Scalar, Rvalue::SlotOf(first))
            }
        }
    }

    /// A pointer to the words at the end of a path of fields and list indexes, from the
    /// pointer `slot`, each object made unique on the way.
    fn walk(&mut self, mut slot: Operand, place: &Place, steps: usize) -> Operand {
        for (k, step) in place.steps.iter().take(steps).enumerate() {
            slot = match step {
                Step::Inline { words, .. } => self.offset(slot, *words),
                Step::Element {
                    index,
                    loc,
                    size,
                    width,
                } => self.element_slot(slot, (index.clone(), loc.clone()), (*size, *width)),
                Step::Object { object, offset, .. } => self.b.define_op(
                    Repr::Scalar,
                    Rvalue::FieldSlot {
                        slot,
                        len: *object,
                        index: u32::try_from(*offset).expect("under 4G fields"),
                    },
                ),
                // An element of a view is reached in the view's source, whose count isn't
                // checked (projections.places-through-views; `super::windows`).
                step @ Step::Index { container, .. } if container.is_view() => {
                    self.view_slot(slot, step, &place.types[k + 1])
                }
                Step::Index { key, loc, .. } => {
                    let shape = match self.elem(&place.types[k + 1]) {
                        Elem::Inline { shape, .. } => shape,
                        Elem::Dynamic(_) => shape::word(true),
                    };
                    let args = vec![loc.clone(), slot, word(key, 0), Operand::word(shape)];
                    self.b
                        .define_op(Repr::Scalar, Rvalue::Runtime(Runtime::ListSlot, args))
                }
            };
        }
        slot
    }

    /// The value at a place, as the interpreter reads it.
    pub(crate) fn read_place(&mut self, place: &Place) -> Vec<Operand> {
        if !place.needs_pointer() {
            return self.read_locals(&place.own_locals());
        }
        // The root is read through the pointer that a store to the place goes through, so
        // that what is read on the way is borrowed, uncounted.
        let mut value: Result<Vec<Operand>, Operand> = Err(self.root_slot(&place.root));
        for (k, step) in place.steps.iter().enumerate() {
            match self.read_list_part(place, k, value) {
                Ok(words) => return words,
                Err(before) => {
                    value = Ok(self.read_step(step, before, &place.types[k], &place.types[k + 1]));
                }
            }
        }
        match value {
            Ok(words) => words,
            Err(pointer) => self.load_words(&pointer, place.ty()),
        }
    }

    /// Copies of the words that locals hold.
    fn read_locals(&mut self, locals: &[Local]) -> Vec<Operand> {
        locals
            .iter()
            .map(|&l| {
                let repr = self.b.repr_of(l);
                self.b.define_op(repr, Rvalue::Use(Operand::Local(l)))
            })
            .collect()
    }

    /// The words of the value at the end of a step, from the value before it: its words, or
    /// a pointer to them that nothing has read yet.
    fn read_step(
        &mut self,
        step: &Step,
        before: Result<Vec<Operand>, Operand>,
        base: &Ty,
        ty: &Ty,
    ) -> Vec<Operand> {
        match (step, before) {
            (Step::Index { container, .. }, before) if container.is_view() => {
                self.read_view_step(before, step, ty)
            }
            (Step::Inline { offset, len, .. }, Ok(v)) => {
                (*offset..offset + len).map(|i| word(&v, i)).collect()
            }
            (Step::Inline { words, .. }, Err(p)) => {
                let at = self.offset(p, *words);
                self.load_words(&at, ty)
            }
            (
                Step::Element {
                    index,
                    loc,
                    size,
                    width,
                },
                before,
            ) => {
                let slot = match before {
                    Ok(v) => self.in_memory(v, base),
                    Err(p) => p,
                };
                let at = self.element_slot(slot, (index.clone(), loc.clone()), (*size, *width));
                self.load_words(&at, ty)
            }
            (step, before) => {
                let object = match before {
                    Ok(v) => word(&v, 0),
                    Err(p) => self.b.define_op(self.repr(base), Rvalue::Load(p)),
                };
                self.read_in(step, object, base, ty)
            }
        }
    }

    /// The words at the end of a step into an object: a field of a recursive type's object, or
    /// an element of a list or a map.
    fn read_in(&mut self, step: &Step, object: Operand, base: &Ty, ty: &Ty) -> Vec<Operand> {
        match step {
            Step::Object { field, .. } => {
                let fields = self.fields_of(base, 0);
                self.field_words(&[object], &fields, *field)
            }
            Step::Index {
                container,
                key,
                loc,
                ..
            } => self.index_value(container, object, key.clone(), loc.clone(), ty),
            Step::Inline { .. } | Step::Element { .. } => unreachable!("a step into an object"),
        }
    }

    /// Stores `value`, which it consumes, at a place, as the interpreter stores it: through a
    /// map's index, by reading the value there, changing it, and inserting it back.
    pub(crate) fn store_place(&mut self, place: &Place, value: Vec<Operand>) {
        if let Some(at) = place.steps.iter().position(Step::through_map) {
            return self.store_through_map(place, at, value);
        }
        if self.store_list_end(place, &value) {
            return;
        }
        if !place.needs_pointer() {
            for (i, l) in place.own_locals().into_iter().enumerate() {
                self.b.assign(l, Rvalue::Use(word(&value, i)));
            }
            return;
        }
        let root = self.root_slot(&place.root);
        let slot = self.walk(root, place, place.steps.len());
        self.store_words(&slot, value, place.ty());
    }

    /// The pointer to its words that an `inout` argument passes, read when the call starts, and
    /// what to write back when it ends.
    pub(crate) fn inout(&mut self, place: Place) -> (Operand, Option<Writeback>) {
        if !place.through_map() && self.whole_words_at_end(&place) {
            let root = self.root_slot(&place.root);
            let n = place.steps.len();
            return (self.walk(root, &place, n), None);
        }
        let value = self.read_place(&place);
        let temps = self.copy_into_temps(value, place.ty());
        self.b.make_slots(&temps);
        let pointer = self.b.define_op(Repr::Scalar, Rvalue::SlotOf(temps[0]));
        (pointer, Some(Writeback { place, temps }))
    }

    /// Writes back the places of `inout` arguments, from left to right (values.left-to-right).
    pub(crate) fn write_back(&mut self, writebacks: &[Writeback]) {
        for w in writebacks {
            let words = self.read_locals(&w.temps);
            self.store_place(&w.place, words);
        }
    }

    /// A pointer to the words of a value of type `ty`, from a pointer to the words that hold
    /// it: for a type parameter held in one word, which is the box of a value of several words,
    /// a pointer into the box, made unique ([`Runtime::InoutWords`]).
    pub(crate) fn words_pointer(&mut self, pointer: Operand, ty: &Ty) -> Operand {
        if !matches!(ty, Ty::Param(_) | Ty::SelfTy) || !self.one_word(ty) {
            return pointer;
        }
        let witness = self.witness(ty);
        if matches!(witness, Operand::Const(Const::Word(s)) if shape::size(s) <= 8) {
            return pointer;
        }
        let args = vec![pointer, witness];
        self.b
            .define_op(Repr::Scalar, Rvalue::Runtime(Runtime::InoutWords, args))
    }

    /// `place = e` and `place op= e` (values.assignment-order and
    /// values.compound-assignment-order).
    pub(crate) fn assign(
        &mut self,
        op: Option<BinaryOp>,
        place: &Expr,
        value: &Expr,
        at: TextRange,
    ) {
        let target = self.place(place);
        let v = self.expr(value);
        let new = match op {
            None => v,
            Some(op) => {
                let current = self.read_place(&target);
                let loc = self.proved_at(at, &[Check::DivideByZero, Check::Overflow]);
                vec![self.binary_values(op, &place.ty, current, v, loc)]
            }
        };
        self.store_place(&target, new);
    }
}
