//! What a function's code says of its lists before it is emitted: which places and locals
//! hold lists, and which local always points to which place.

use stilt_mir::mir::{
    Arg, Callee, Function, Operand, ParamMode, Runtime, Rvalue, Stmt, Terminator,
};

use super::list_member;

/// Whether each local is named as a list: a place that a list operation reaches through a
/// pointer to it or reads, or a local that one reads, directly or as a copy of a place's value.
pub(super) fn named_lists(f: &Function, origin: &[Option<usize>], slot: &[bool]) -> Vec<bool> {
    let mut lists = vec![false; f.locals.len()];
    let mut mark = |o: &Operand, through: bool| {
        let Some(l) = o.local().map(|l| l.0 as usize) else {
            return;
        };
        match (through, origin[l]) {
            (true, Some(p)) => lists[p] = true,
            (true, None) => {}
            (false, _) => lists[l] = true,
        }
    };
    for s in f.blocks.iter().flat_map(|b| &b.stmts) {
        match s {
            Stmt::Assign(_, Rvalue::Runtime(f, args)) | Stmt::Effect(f, args) => match f {
                Runtime::ListIndex | Runtime::ListGet => mark(&args[1], false),
                Runtime::ListAt | Runtime::ListLen | Runtime::ListPush => mark(&args[0], false),
                Runtime::ListSlot | Runtime::ListElement => mark(&args[1], true),
                Runtime::ListSlotAt | Runtime::ListElementAt | Runtime::ListAppend => {
                    mark(&args[0], true);
                }
                _ => {}
            },
            _ => {}
        }
    }
    for t in f.blocks.iter().map(|b| &b.term) {
        if let Terminator::Call {
            callee: Callee::Direct(f),
            args,
            ..
        } = t
            && let Some(Arg::Borrow(o) | Arg::Ref(o)) = args.get(2)
            && list_member(f, &["len", "is_empty", "pop"])
        {
            let through = matches!(args.get(2), Some(Arg::Ref(_)));
            mark(o, through);
        }
    }
    // A place whose value a local named as a list reads holds lists too.
    for s in f.blocks.iter().flat_map(|b| &b.stmts) {
        let Stmt::Assign(d, r) = s else { continue };
        let read = match r {
            Rvalue::Use(Operand::Local(p)) if slot[p.0 as usize] => Some(p.0 as usize),
            Rvalue::Load(pointer) => pointer.local().and_then(|l| origin[l.0 as usize]),
            _ => None,
        };
        if let Some(p) = read
            && lists[d.0 as usize]
        {
            lists[p] = true;
        }
    }
    lists
}

/// The place each local points to, for each that is assigned only the pointer to one place.
/// An `inout` parameter points to its caller's slot, which is a place of its own, named by the
/// parameter: no other argument overlaps it (modes.overlapping-inout) and closures capture by
/// copy (expressions.capture), so while the call runs nothing reaches the slot but through the
/// parameter. A parameter whose pointer is copied, or given another value, is no place.
pub(super) fn origins(f: &Function) -> Vec<Option<usize>> {
    let mut origin: Vec<Option<Option<usize>>> = vec![None; f.locals.len()];
    for p in &f.params {
        let l = p.local.0 as usize;
        origin[l] = Some((p.mode == ParamMode::Ref).then_some(l));
    }
    for s in f.blocks.iter().flat_map(|b| &b.stmts) {
        if let Stmt::Assign(
            _,
            Rvalue::Use(Operand::Local(l)) | Rvalue::Offset(Operand::Local(l), _),
        ) = s
            && let Some(Some(p)) = origin[l.0 as usize]
            && p == l.0 as usize
        {
            origin[p] = Some(None);
        }
    }
    for s in f.blocks.iter().flat_map(|b| &b.stmts) {
        let Stmt::Assign(d, r) = s else { continue };
        let to = match r {
            Rvalue::SlotOf(l) => Some(l.0 as usize),
            _ => None,
        };
        let slot = &mut origin[d.0 as usize];
        if f.params.iter().any(|p| p.local == *d) {
            *slot = Some(None);
            continue;
        }
        *slot = match *slot {
            None => Some(to),
            Some(before) if before == to => Some(to),
            Some(_) => Some(None),
        };
    }
    for t in f.blocks.iter().map(|b| &b.term) {
        if let Terminator::Call { dest, raised, .. } = t {
            for d in dest.iter().chain(raised.iter().flat_map(|(e, _)| e)) {
                origin[d.0 as usize] = Some(None);
            }
        }
    }
    origin.into_iter().map(Option::flatten).collect()
}
