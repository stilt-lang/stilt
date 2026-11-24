//! Arrays (generics.arrays, generics.array-elements and generics.large-arrays). A value of
//! `Array<T, n>` holds its `n` elements inline, one after the other, each in the words that hold a
//! `T` where a type parameter stands, as a record holds its fields, so making, copying, reading and
//! writing one allocates nothing (generics.array-effects). Its size is known wherever code holds
//! one: a value argument, or a value parameter of type `i64`, which keys the instance
//! (`super::values`).
//!
//! An array of at most [`MEMORY_WORDS`] words is held in a local per word, as a record is. A
//! larger one is held in memory, one local of the frame ([`Repr::Array`]), so that making,
//! copying, passing, returning and counting it are copies and loops over that memory rather
//! than code per element, whatever its size (generics.large-arrays; `memory`).
//!
//! An element at an index that the program computes is reached through a pointer to the
//! array's words in memory, once the index is checked against the size: out of bounds, the
//! read or the write panics with `bounds`, as a list's index does (generics.array-elements).

mod memory;
mod natives;

pub(crate) use natives::array_native;

use stilt_types::tast::{Block, Expr, ExprKind, Pat};
use stilt_types::ty::Ty;
use stilt_types::verify::Check;

use super::Lower;
use super::words::{Field, Fields};
use crate::mir::{Elements, MEMORY_WORDS, NumKind, Operand, Prim, Repr, Rvalue};

/// The most words an array's layout holds, unless generics.large-arrays asks for it.
const MOST_WORDS: i128 = 1 << 22;

/// The most elements, those of nested arrays counted, that generics.large-arrays asks every array
/// to hold.
const MOST_ELEMENTS: i128 = 65_536;

/// The elements of a type, those of the arrays it holds as elements counted: for an array, its
/// size times its element type's, and for any other type, 1. `size` gives a size where it is
/// known, and one that isn't counts as 1.
fn elements(ty: &Ty, size: &dyn Fn(&Ty) -> Option<i128>) -> i128 {
    match ty.arrayed() {
        Some((elem, n)) => size(n)
            .unwrap_or(1)
            .max(1)
            .saturating_mul(elements(elem, size)),
        None => 1,
    }
}

/// Whether an array of `k` elements, each held in `width` words, is held in memory, rather than
/// in a local per word.
pub(crate) fn held_in_memory(k: i128, width: usize) -> bool {
    k.saturating_mul(width as i128) > MEMORY_WORDS as i128
}

/// Whether an array of `k` elements of type `elem`, each held in `width` words, is past what
/// compiled code holds: past [`MOST_WORDS`] words, and past the elements that generics.large-arrays
/// asks for. Code that would hold one ends the run as running out of memory does, which
/// generics.large-arrays allows.
pub(crate) fn too_large(
    elem: &Ty,
    k: i128,
    width: usize,
    size: &dyn Fn(&Ty) -> Option<i128>,
) -> bool {
    k.saturating_mul(width as i128) > MOST_WORDS
        && k.saturating_mul(elements(elem, size)) > MOST_ELEMENTS
}

/// The panic kind `bounds` (`stilt_runtime`'s numbering).
const BOUNDS: u64 = 2;

/// `k` copies of the words of an element, one after the other, or for an array of no
/// elements, one word, `empty`, which holds nothing, as `()`'s does.
pub(crate) fn repeated<T: Clone>(each: &[T], k: usize, empty: T) -> Vec<T> {
    if k == 0 || each.is_empty() {
        return vec![empty];
    }
    each.iter().cloned().cycle().take(k * each.len()).collect()
}

/// Whether an expression is a place that `Lower::place` reads without evaluating it whole: a
/// variable, or a part of one.
fn is_place(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Local(_) => true,
        ExprKind::Field(base, _) | ExprKind::TupleField(base, _) | ExprKind::Index(base, _) => {
            is_place(base)
        }
        _ => false,
    }
}

impl Lower<'_> {
    /// The element type and the size of an array type whose size is known here.
    pub(crate) fn array_parts(&self, ty: &Ty) -> Option<(Ty, i128)> {
        let (elem, size) = ty.arrayed()?;
        let k = self.value_of(size)?;
        if too_large(elem, k, self.words_of(elem), &|t| self.value_of(t)) {
            self.b.met_too_large();
            return None;
        }
        Some((elem.clone(), k))
    }

    /// The layout of the elements of an array type held in memory, if `ty` is one.
    pub(crate) fn array_in_memory(&self, ty: &Ty) -> Option<Elements<Repr>> {
        ty.arrayed()?;
        match self.layout(ty).as_slice() {
            [Repr::Array(e)] => Some(*e),
            _ => None,
        }
    }

    /// The words of an array of `size` elements of type `elem`: each element's, one after the
    /// other, in a local each, or in memory past [`MEMORY_WORDS`] words.
    pub(crate) fn array_layout(&self, elem: &Ty, size: &Ty) -> Vec<Repr> {
        let held = self.layout(elem);
        let width = crate::mir::offsets(held.iter().copied()).1;
        match self.value_of(size) {
            Some(k) if !too_large(elem, k, width, &|t| self.value_of(t)) => {
                if held_in_memory(k, width) {
                    let k = u32::try_from(k).expect("an array of under 2^22 words");
                    return vec![Repr::Array(Elements::new(k, held))];
                }
                let k = usize::try_from(k.max(0)).unwrap_or(0);
                repeated(&held, k, Repr::Scalar)
            }
            Some(_) => {
                self.b.met_too_large();
                vec![Repr::Heap]
            }
            None => {
                self.b.met_error();
                vec![Repr::Heap]
            }
        }
    }

    /// Where the elements of an array held in words are: one field for each, of the element
    /// type. An array held in memory has no field among its words, whose elements code reads
    /// through a pointer (`memory`).
    pub(crate) fn array_fields(&self, elem: &Ty, size: &Ty) -> Fields {
        let width = self.layout(elem).len();
        let mut k = self.value_of(size).unwrap_or(0).max(0);
        if too_large(elem, k, self.words_of(elem), &|t| self.value_of(t)) {
            self.b.met_too_large();
            k = 0;
        }
        if held_in_memory(k, self.words_of(elem)) {
            k = 0;
        }
        let all = (0..usize::try_from(k).unwrap_or(0))
            .map(|i| Field {
                ty: elem.clone(),
                at: (i * width..(i + 1) * width).collect(),
            })
            .collect();
        Fields {
            tagged: false,
            object: None,
            all,
            tag: None,
        }
    }

    /// The number of words of each element of an array of elements of type `elem`, in memory.
    pub(crate) fn element_width(&self, elem: &Ty) -> usize {
        self.words_of(elem)
    }

    /// A list literal that makes an array of type `ty`: its elements' words, one after the
    /// other, which it consumes (generics.array-literals), in memory for an array held there.
    pub(crate) fn array_literal(&mut self, es: &[Expr], ty: &Ty) -> Vec<Operand> {
        let values = self.element_values(es);
        if let Some(e) = self.array_in_memory(ty) {
            return self.array_of(e, values);
        }
        let words: Vec<Operand> = values.into_iter().flat_map(|(v, _)| v).collect();
        if words.is_empty() {
            return vec![Operand::word(0)];
        }
        words
    }

    /// A pointer to element `index` of an array of `size` elements of `width` words each, whose
    /// words start where `slot` points, once the index is in bounds, or the panic with `bounds`
    /// at `loc` (generics.array-elements).
    pub(crate) fn element_slot(
        &mut self,
        slot: Operand,
        (index, loc): (Operand, Operand),
        (size, width): (i128, usize),
    ) -> Operand {
        let n = u64::try_from(size.max(0)).unwrap_or(0);
        // A negative index is a large unsigned one.
        let inside = self.lt(NumKind::U64, index.clone(), Operand::word(n));
        let (ok, out) = (self.b.new_block(), self.b.new_block());
        self.b.branch(inside, ok, out);
        self.b.switch_to(out);
        self.panic(BOUNDS, None, loc);
        self.b.switch_to(ok);
        self.array_element_at(slot, index, width)
    }

    /// A pointer to element `index`, in bounds, of `width` words each, from where `slot` points.
    pub(crate) fn array_element_at(
        &mut self,
        slot: Operand,
        index: Operand,
        width: usize,
    ) -> Operand {
        let bytes = 8 * u64::try_from(width).unwrap_or(0);
        let rvalue = |p, args| Rvalue::Prim(p, args, Operand::word(0));
        let offset = self.b.define_op(
            Repr::Scalar,
            rvalue(
                Prim::MulWrap(NumKind::I64),
                vec![index, Operand::word(bytes)],
            ),
        );
        self.b.define_op(
            Repr::Scalar,
            rvalue(Prim::AddWrap(NumKind::I64), vec![slot, offset]),
        )
    }

    /// A pointer to a copy of an array's words in memory, which the function's slots hold
    /// until it ends.
    pub(crate) fn in_memory(&mut self, words: Vec<Operand>, ty: &Ty) -> Operand {
        let temps = self.copy_into_temps(words, ty);
        match temps.first() {
            Some(&first) => {
                self.b.make_slots(&temps);
                self.b.define_op(Repr::Scalar, Rvalue::SlotOf(first))
            }
            None => Operand::word(0),
        }
    }

    /// `a[i]` of an array, read where the array is when it is a place, so that reading one
    /// element copies no other (generics.array-elements).
    pub(crate) fn array_index(&mut self, container: &Expr, key: &Expr, e: &Expr) -> Vec<Operand> {
        if is_place(container) {
            let place = self.place(e);
            return self.read_place(&place);
        }
        let words = self.expr(container);
        let index = self.expr1(key);
        let loc = self.proved_at(e.at, &[Check::Bounds]);
        let Some((elem, size)) = self.array_parts(&container.ty) else {
            self.b.met_error();
            return vec![Operand::word(0)];
        };
        let slot = self.in_memory(words, &container.ty);
        let width = self.element_width(&elem);
        let at = self.element_slot(slot, (index, loc), (size, width));
        self.load_words(&at, &e.ty)
    }

    /// Each element of the array, as it was when the loop started (generics.array-iteration;
    /// expressions.for-iterables).
    pub(crate) fn for_array(&mut self, pattern: &Pat, source: &Expr, body_block: &Block) {
        let words = self.expr(source);
        let Some((elem, size)) = self.array_parts(&source.ty) else {
            self.b.met_error();
            return;
        };
        let slot = self.in_memory(words, &source.ty);
        let width = self.element_width(&elem);
        let index = self.b.temp(Repr::Scalar);
        self.b.assign(index, Rvalue::Use(Operand::word(0)));
        let (head, body, next, exit) = self.loop_blocks();
        self.b.goto(head);
        self.b.switch_to(head);
        let count = u64::try_from(size.max(0)).unwrap_or(0);
        let more = self.lt(NumKind::I64, Operand::Local(index), Operand::word(count));
        self.b.branch(more, body, exit);
        self.b.switch_to(body);
        let at = self.array_element_at(slot, Operand::Local(index), width);
        let element = self.load_words(&at, &pattern.ty);
        self.binding(pattern, element, false, None);
        self.loop_body(body_block, exit, next);
        self.b.switch_to(next);
        self.step(index);
        self.b.goto(head);
        self.b.switch_to(exit);
    }
}
