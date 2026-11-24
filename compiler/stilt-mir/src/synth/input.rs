//! An input of the REPL, compiled into the session's image (repl.running-inputs): its body, as a
//! function whose parameters are the session's bindings, and its entry, which the REPL runs on
//! a thread of its own.
//!
//! The entry takes one word, which points to the session's frame: the words of each binding, in
//! order, then room for the words of the values that a `let` binds. It reads each binding's
//! words, which the frame keeps, and lends them to the body. An expression's entry gives the
//! text of its value, as `show_nested` shows it, or the empty string for a value whose type has
//! no `Show`; a `let`'s writes the words of the values it binds after the bindings', which the
//! frame then owns, and gives the empty string: those of its value, the one value it binds or a
//! tuple of them, but for the word of `()`, the value of a `let` that binds no name. Each raises the text of what the body raises,
//! as its `Show` impl shows it.

use std::sync::Arc;

use stilt_db::{Db, Program};
use stilt_diag::LineIndex;
use stilt_hir::decls::prelude_item;
use stilt_types::input::Checked;
use stilt_types::tast::Definition;
use stilt_types::ty::Ty;

use crate::FnRef;
use crate::lower::words::operands;
use crate::lower::{Conv, Cx, Lower, Origin};
use crate::mir::{Arg, Callee, Const, Function, Local, Operand, Repr, Rvalue, Stmt, Terminator};

/// An input, as its lowering needs it.
#[derive(Clone, Copy, Debug)]
pub struct Input<'a> {
    /// Its number in the session, which names its functions.
    pub number: u32,
    /// The index of the file its locations name: past the program's files, so that a panic it
    /// locates is reported without its place (repl.running-inputs).
    pub file: u32,
    /// Its text, as written.
    pub text: &'a str,
    /// The types of the session's bindings, which its parameters take, in order.
    pub params: &'a [Ty],
    /// Its typed body.
    pub checked: &'a Checked,
    /// For a `let`, the types of the values it binds, in order, which its entry writes to the
    /// frame.
    pub bound: Option<&'a [Ty]>,
}

/// The functions of an input without errors: its body's, its closures', and its entry's,
/// [`FnRef::InputEntry`] of its number.
#[must_use]
pub fn lower_input(db: &dyn Db, program: Program, input: &Input<'_>) -> Vec<Function> {
    let cx = Cx { db, program };
    let Some(mut functions) = body(&cx, input) else {
        return Vec::new();
    };
    functions.push(entry(&cx, input));
    functions
}

/// Whether each word of a value of each type is a heap word, for the values that the frame
/// holds.
#[must_use]
pub fn layouts_of(db: &dyn Db, program: Program, tys: &[Ty]) -> Vec<Vec<bool>> {
    let cx = Cx { db, program };
    let l = Lower::new(&cx, FnRef::Main, false);
    tys.iter()
        .map(|t| crate::lower::lists::heap_words(&l.layout(t)))
        .collect()
}

/// The error type an input's body raises.
fn error_type(input: &Input<'_>) -> Ty {
    input
        .checked
        .body
        .tested
        .as_ref()
        .map_or_else(Ty::never, |t| t.error.clone())
}

/// The functions of the input's body: its own, and its closures'.
fn body(cx: &Cx<'_>, input: &Input<'_>) -> Option<Vec<Function>> {
    let typed = &input.checked.body;
    let Definition::Code(code) = &typed.code else {
        return None;
    };
    let mut l = Lower::new(cx, FnRef::Input(input.number), false);
    let text: Arc<str> = Arc::from(input.text);
    l.origin = Some(Origin {
        file: input.file,
        start: 0.into(),
        lines: Arc::new(LineIndex::new(&text)),
        text,
        // An input of the REPL runs in a debug build, which drops no check.
        proofs: Arc::default(),
    });
    l.names.clone_from(&typed.locals);
    l.ret = Conv::of(input.checked.ty.clone());
    l.err = Conv::of(error_type(input));
    for (&(mode, id), ty) in typed.params.iter().zip(input.params) {
        let name = l.names[id.0 as usize];
        let var = l.param_var(mode, Some(name), ty);
        l.vars.insert(id, var);
    }
    l.body(code);
    Some(l.finish())
}

/// A pointer `at` words into the frame.
fn word_of(l: &mut Lower<'_>, frame: Local, at: u32) -> Operand {
    let rvalue = Rvalue::Offset(Operand::Local(frame), at);
    Operand::Local(l.b.define(Repr::Scalar, rvalue))
}

/// The input's entry.
fn entry(cx: &Cx<'_>, input: &Input<'_>) -> Function {
    let mut l = Lower::new(cx, FnRef::InputEntry(input.number), false);
    l.ret = Conv::of(Ty::str());
    l.err = Conv::of(Ty::str());
    let frame = l.loc;
    let loc = Operand::word(0);
    let mut args = vec![Arg::Borrow(loc.clone())];
    let mut at = 0;
    for ty in input.params {
        for repr in l.layout(ty) {
            let pointer = word_of(&mut l, frame, at);
            let word = l.b.temp(repr);
            l.b.decl_mut(word).borrowed = true;
            l.b.assign(word, Rvalue::Load(pointer));
            args.push(Arg::Borrow(Operand::Local(word)));
            at += u32::try_from(repr.words()).expect("under 4G words");
        }
    }
    let ty = input.checked.ty.clone();
    let error = error_type(input);
    let dest = l.temps(&ty);
    let next = l.b.new_block();
    let raised = (error != Ty::never()).then(|| (l.temps(&error), l.b.new_block()));
    l.b.terminate(Terminator::Call {
        callee: Callee::Direct(FnRef::Input(input.number)),
        args,
        dest: dest.clone(),
        next,
        raised: raised.clone(),
    });
    if let Some((words, block)) = raised {
        l.b.switch_to(block);
        let shown = l.trait_call("Show", "show", &error, vec![operands(&words)], loc.clone());
        l.b.terminate(Terminator::Raise(vec![shown]));
    }
    l.b.switch_to(next);
    let empty = Operand::Const(Const::Str(Arc::from("")));
    let shown = if let Some(bound) = input.bound {
        let words: usize = bound.iter().map(|t| l.layout(t).len()).sum();
        let mut k = at;
        for &word in &dest[..words] {
            let slot = word_of(&mut l, frame, k);
            let repr = l.b.repr_of(word);
            let value = Operand::Local(word);
            l.b.emit(Stmt::Store { slot, value, repr });
            k += u32::try_from(repr.words()).expect("under 4G words");
        }
        empty
    } else if ty != Ty::never() && l.implements(&ty, &prelude_item("Show")) {
        l.trait_call("Show", "show_nested", &ty, vec![operands(&dest)], loc)
    } else {
        empty
    };
    l.b.terminate(Terminator::Return(vec![shown]));
    l.into_function()
}
