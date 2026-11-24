//! The facts that a push forgets. Lowering pushes only onto a list it is building, for a list
//! literal, an interpolation or a structural `show`, which nothing else references: the push
//! forgets the length of that list, through each holder of it, and every other list keeps its
//! own, so a loop that prints with an interpolation keeps the bounds of the list it indexes
//! (goal debug-speed).

use super::writes::{inout_loop, slot, slot_at, store};
use super::{SHAPE, assign, at, decl, function, index, op, optimized, ret};
use crate::mir::{
    Const, Function, Local, NumKind, Operand, ParamMode, Repr, Runtime, Rvalue, Stmt,
};
use crate::opt::facts::{Fact, Facts, Holder, Place, Term};
use crate::opt::ranges::Cx;

/// The shape of a list's elements that are strings.
const STRS: Operand = Operand::word(crate::shape::word(true));

/// `"{x}!"`: the text of the integer `_x` in `_shown`, and the text of the interpolation in
/// `_text`, the concatenation of the list `_parts`.
fn interpolation(x: u32, shown: u32, parts: u32, text: u32) -> Vec<Stmt> {
    let push = |part| Stmt::Effect(Runtime::ListPush, vec![op(parts), STRS, part]);
    let kind = Operand::word(NumKind::I64.code());
    vec![
        assign(shown, Rvalue::Runtime(Runtime::ShowInt, vec![kind, op(x)])),
        assign(
            parts,
            Rvalue::Runtime(Runtime::ListNew, vec![Operand::word(2), STRS]),
        ),
        push(op(shown)),
        push(Operand::Const(Const::Str("!".into()))),
        assign(text, Rvalue::Runtime(Runtime::Concat, vec![op(parts)])),
    ]
}

/// The facts that hold after a push onto `_list` in `f`, where `before` held.
fn after_push(f: &Function, before: &[Fact], list: u32) -> Vec<Fact> {
    let mut facts = Facts::default();
    for fact in before {
        facts.insert(*fact);
    }
    let push = Stmt::Effect(Runtime::ListPush, vec![op(list), SHAPE, Operand::word(0)]);
    Cx::new(f).stmt(&mut facts, &push);
    facts.iter().collect()
}

/// `kept`, in the order of a set of facts.
fn sorted(kept: &[Fact]) -> Vec<Fact> {
    let mut kept = kept.to_vec();
    kept.sort();
    kept
}

#[test]
fn an_interpolation_in_the_loop_keeps_the_bounds_of_the_list_indexed() {
    // `for i in 0..xs.len() { let s = "{xs[i]}!"; xs[i] = 0 }` on `*_1`, read into `_8`.
    let mut body = vec![assign(8, Rvalue::Load(op(1))), assign(9, index(8, op(4)))];
    body.extend(interpolation(9, 10, 11, 12));
    body.extend([assign(13, slot(1, op(4))), store(13)]);
    let mut f = inout_loop(body, 6);
    for l in [8, 10, 11, 12] {
        f.locals[l] = decl(Repr::Heap, false);
    }
    assert_eq!(optimized(f.clone(), 9), [at(8, op(4))]);
    assert_eq!(optimized(f, 13), [slot_at(1, op(4))]);
}

#[test]
fn a_push_forgets_the_length_of_its_list_through_each_holder_and_no_other() {
    // `_7` and `_8` were read from `*_1`, and `_9` holds another list: a push onto `_8` grows
    // what `*_1` and `_7` hold too, each of which still holds it, and leaves `_9` as it was.
    let f = function(&[ParamMode::Ref], 8, &[1, 7, 8, 9], vec![ret(Vec::new())]);
    let xs = Place::Param(Local(1), 0);
    let (counter, len, other) = (Term::Local(Local(4)), Local(5), Local(6));
    let local = |l| Holder::Local(Local(l));
    let kept = [
        Fact::Holds(Local(7), xs),
        Fact::Holds(Local(8), xs),
        Fact::Len(other, local(9)),
        Fact::InBounds(counter, local(9)),
    ];
    let lost = [
        Fact::Len(len, Holder::Place(xs)),
        Fact::Len(len, local(7)),
        Fact::InBounds(counter, local(8)),
    ];
    let before = [kept.as_slice(), &lost].concat();
    assert_eq!(after_push(&f, &before, 8), sorted(&kept));
}

#[test]
fn a_push_onto_a_local_in_memory_forgets_the_length_of_what_its_slot_holds() {
    // `_8` was read from the slot of `_7`, and `_9` holds another list.
    let mut f = function(&[], 9, &[8, 9], vec![ret(Vec::new())]);
    f.locals[7] = decl(Repr::Heap, true);
    let xs = Place::Slot(Local(7));
    let (counter, len, other) = (Term::Local(Local(4)), Local(5), Local(6));
    let local = |l| Holder::Local(Local(l));
    let kept = [Fact::Holds(Local(8), xs), Fact::Len(other, local(9))];
    let lost = [
        Fact::Len(len, Holder::Place(xs)),
        Fact::Len(len, local(8)),
        Fact::InBounds(counter, local(7)),
    ];
    let before = [kept.as_slice(), &lost].concat();
    assert_eq!(after_push(&f, &before, 7), sorted(&kept));
}
