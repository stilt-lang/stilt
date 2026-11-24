//! The promise of an in-place `let` parameter at run time (facts.in-place-promise): a direct call
//! makes the storage of the argument it gives such a parameter unique, once the counting has given
//! the call its reference, so the callee's writes copy nothing. A caller that gives its last use of
//! storage that no other value shares makes it unique at no cost; one that keeps the value, which
//! the counting copies for the call, a lost reuse (values.consumed-parameters), copies the storage
//! there, in its own code, as the copy at the call that facts.copy-at-call counts. An `inout`
//! argument is made unique by lowering, where the call reads its place.

use stilt_hir::hir::Name;

use stilt_db::{Db, Program};
use stilt_mir::mir::{
    Arg, Function, Local, LocalDecl, Operand, Repr, Runtime, Rvalue, Stmt, Terminator,
};
use stilt_mir::{Code, FnRef, code_of};
use stilt_types::promises::{Key, in_place_params};

use crate::queries::source_name;

/// The item of a function with a body whose parameters may be in place.
fn key_of(f: &FnRef) -> Option<Key> {
    match f.generic() {
        FnRef::Function(item) => Some(Key::Function(item.clone())),
        FnRef::Member(owner, name) => Some(Key::Member(owner.clone(), *name)),
        FnRef::ImplMethod(t, owner, name) => Some(Key::ImplMethod(t.clone(), owner.clone(), *name)),
        FnRef::DefaultMethod(t, name) => Some(Key::DefaultMethod(t.clone(), *name)),
        _ => None,
    }
}

/// The positions among the parameters of the code of `g` of the words of its in-place `let`
/// parameters, which hold lists, each in one word (facts.in-place-parameters).
pub(crate) fn unique_words(db: &dyn Db, program: Program, g: &FnRef) -> Vec<usize> {
    let Some(key) = key_of(g) else {
        return Vec::new();
    };
    let Some(params) = in_place_params(db, program).get(&key) else {
        return Vec::new();
    };
    let Some(Code::Body(file, index)) = code_of(db, program, g.generic().clone()) else {
        return Vec::new();
    };
    let body = stilt_hir::module_body(db, program, file, index);
    let names: Vec<Name> = params
        .iter()
        .filter_map(|&p| body.params.get(p))
        .map(|v| body.locals[v.0 as usize].name)
        .collect();
    let functions = stilt_mir::functions(db, program, g.clone());
    let Some(code) = functions.iter().find(|x| x.name == *g) else {
        return Vec::new();
    };
    (0..code.params.len())
        .filter(|&i| source_name(code, i).is_some_and(|n| names.contains(&n)))
        .filter(|&i| code.locals[code.params[i].local.0 as usize].repr == Repr::Heap)
        .collect()
}

/// Makes unique, before each direct call of a function in `unique`, the storage of each word
/// it gives one of the function's in-place `let` parameters, by the positions there: the word
/// goes to a slot, which is made unique, and the call takes the word back from it.
pub(crate) fn make_unique(f: &mut Function, unique: &[(FnRef, Vec<usize>)]) {
    for b in 0..f.blocks.len() {
        let Terminator::Call {
            callee: stilt_mir::mir::Callee::Direct(g),
            args,
            ..
        } = &f.blocks[b].term
        else {
            continue;
        };
        let Some((_, positions)) = unique.iter().find(|(h, _)| h == g) else {
            continue;
        };
        let given: Vec<(usize, Local)> = positions
            .iter()
            .filter_map(|&i| match args.get(i) {
                Some(Arg::Own(Operand::Local(l)) | Arg::Borrow(Operand::Local(l))) => Some((i, *l)),
                _ => None,
            })
            .collect();
        for (i, l) in given {
            let taken = through_slot(f, b, l);
            if let Terminator::Call { args, .. } = &mut f.blocks[b].term
                && let Some(Arg::Own(o) | Arg::Borrow(o)) = args.get_mut(i)
            {
                *o = Operand::Local(taken);
            }
        }
    }
}

/// A new local of the function.
fn local(f: &mut Function, repr: Repr, slot: bool) -> Local {
    let l = Local(u32::try_from(f.locals.len()).expect("under 4G locals"));
    f.locals.push(LocalDecl {
        repr,
        slot,
        grouped: false,
        borrowed: false,
        var: false,
        name: None,
        shown: None,
    });
    l
}

/// Puts the word of `l` in a slot at the end of block `b`, makes its storage unique there, and
/// gives the local that holds it again.
fn through_slot(f: &mut Function, b: usize, l: Local) -> Local {
    let slot = local(f, Repr::Heap, true);
    let pointer = local(f, Repr::Scalar, false);
    let taken = local(f, Repr::Heap, false);
    f.blocks[b].stmts.extend([
        Stmt::Assign(slot, Rvalue::Use(Operand::Local(l))),
        Stmt::Assign(pointer, Rvalue::SlotOf(slot)),
        Stmt::Effect(Runtime::Unique, vec![Operand::Local(pointer)]),
        Stmt::Assign(taken, Rvalue::Use(Operand::Local(slot))),
    ]);
    taken
}
