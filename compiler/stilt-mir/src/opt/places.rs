//! Where each pointer of a function points: to a place, a word of the function's own slots or
//! of what an `inout` parameter points to, or into an object on the heap.
//!
//! An `inout` parameter's memory is reached only through that parameter: two `inout` arguments
//! of one call never overlap, and a `let` argument is read before the call starts, as a value of
//! its own (modes.durations and modes.overlapping-inout). A pointer into an object, to a field or
//! an element, so never reaches a place, and a write through it leaves every place as it was.

use crate::mir::{Function, Local, ParamMode, Runtime, Rvalue, Stmt, Terminator};
use crate::opt::facts::Place;

/// Where a pointer points.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Ptr {
    Place(Place),
    /// Into an object on the heap.
    Interior,
    Unknown,
}

/// Where each local of `f` points, if it holds a pointer that one definition gives it.
pub(crate) fn pointers(f: &Function) -> Vec<Ptr> {
    let mut defs = vec![0u32; f.locals.len()];
    for p in &f.params {
        defs[p.local.0 as usize] += 1;
    }
    for block in &f.blocks {
        for stmt in &block.stmts {
            if let Stmt::Assign(d, _) = stmt {
                defs[d.0 as usize] += 1;
            }
        }
        if let Terminator::Call { dest, raised, .. } = &block.term {
            for d in dest.iter().chain(raised.iter().flat_map(|(e, _)| e)) {
                defs[d.0 as usize] += 1;
            }
        }
    }
    let mut ptrs = vec![Ptr::Unknown; f.locals.len()];
    for p in &f.params {
        if p.mode == ParamMode::Ref {
            ptrs[p.local.0 as usize] = Ptr::Place(Place::Param(p.local, 0));
        }
    }
    // A pointer is defined before it is used, so a pass per level of derivation finds them all;
    // lowering derives a pointer from another at most a few times.
    for _ in 0..4 {
        for stmt in f.blocks.iter().flat_map(|b| &b.stmts) {
            let Stmt::Assign(d, r) = stmt else { continue };
            if defs[d.0 as usize] == 1 {
                ptrs[d.0 as usize] = derived(f, &ptrs, r);
            }
        }
    }
    ptrs
}

/// Where the pointer that `r` computes points.
fn derived(f: &Function, ptrs: &[Ptr], r: &Rvalue) -> Ptr {
    let of = |o: &crate::mir::Operand| o.local().map_or(Ptr::Unknown, |l| ptrs[l.0 as usize]);
    match r {
        Rvalue::SlotOf(l) => Ptr::Place(Place::Slot(*l)),
        Rvalue::Use(o) => of(o),
        Rvalue::Offset(o, words) => match of(o) {
            Ptr::Place(Place::Param(p, at)) => Ptr::Place(Place::Param(p, at + words)),
            Ptr::Place(Place::Slot(l)) => later_slot(f, l, *words),
            other => other,
        },
        Rvalue::FieldSlot { .. }
        | Rvalue::Runtime(
            Runtime::ListSlot | Runtime::ListSlotAt | Runtime::ListElement | Runtime::ListElementAt,
            _,
        ) => Ptr::Interior,
        _ => Ptr::Unknown,
    }
}

/// The slot `words` words past the slot of `l`, which is the slot of a later local when the
/// locals between are the words of one value, grouped in memory.
fn later_slot(f: &Function, l: Local, words: u32) -> Ptr {
    let at = l.0 + words;
    let grouped = (l.0 + 1..=at).all(|i| f.locals.get(i as usize).is_some_and(|d| d.grouped));
    if grouped {
        Ptr::Place(Place::Slot(Local(at)))
    } else {
        Ptr::Unknown
    }
}
