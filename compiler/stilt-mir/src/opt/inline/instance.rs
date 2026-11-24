//! A generic function of the standard library where a call gives each of its witnesses a
//! constant, as concrete code does: the shapes of the type arguments are then
//! known, so the words that hold values of a type parameter are known to be heap words or not,
//! and the function reads and appends the elements of its lists as code that names their type
//! does. A function that holds a value of a type parameter in one word is compiled for
//! arguments of one word (`crate::items::Held`), so each such element is one word: a scalar, a
//! heap word, a narrow scalar, or the box of a value of several words, as code past the caps of
//! instances holds it (`crate::lower::bridge`).

use crate::mir::{Function, Heapness, Local, Operand, Repr, Runtime, Rvalue, Stmt};
use crate::shape::{HEAP, size};

/// Rewrites `g` for the constant shape of each witness among `shapes`, by its local.
pub(crate) fn instantiate(g: &mut Function, shapes: &[(Local, u64)]) {
    let shape_of = |o: &Operand| match o {
        Operand::Local(l) => shapes.iter().find(|(w, _)| w == l).map(|&(_, s)| s),
        Operand::Const(_) => None,
    };
    let known = |w: Local| Some(shape_of(&Operand::Local(w)).map_or(Repr::Generic(w), held));
    for d in &mut g.locals {
        d.repr = d.repr.map_witnesses(&known).unwrap_or(d.repr);
    }
    for b in 0..g.blocks.len() {
        let stmts = std::mem::take(&mut g.blocks[b].stmts);
        let mut out = Vec::with_capacity(stmts.len());
        for s in stmts {
            instantiate_stmt(s, &shape_of, &mut out);
        }
        g.blocks[b].stmts = out;
    }
}

/// How a word that holds a value where a type parameter of shape `s` stands is counted.
fn held(s: u64) -> Repr {
    if s & HEAP == 0 {
        Repr::Scalar
    } else {
        Repr::Heap
    }
}

/// Whether a list holds a value of shape `s` in one word: a scalar, a heap word, a narrow
/// scalar, or a boxed value.
fn one_word(s: u64) -> bool {
    size(s) <= 8
}

fn instantiate_stmt(s: Stmt, shape_of: &impl Fn(&Operand) -> Option<u64>, out: &mut Vec<Stmt>) {
    match s {
        Stmt::Assign(d, Rvalue::Alloc(tag, mut fields)) => {
            for (_, h) in &mut fields {
                match *h {
                    Heapness::Witness(w) if let Some(s) = shape_of(&Operand::Local(w)) => {
                        *h = Heapness::Static(s & HEAP != 0);
                    }
                    Heapness::Array(e) => {
                        let known = |w: Local| {
                            Some(shape_of(&Operand::Local(w)).map_or(Repr::Generic(w), held))
                        };
                        if let Some(Repr::Array(e)) = Repr::Array(e).map_witnesses(&known) {
                            *h = Heapness::Array(e);
                        }
                    }
                    _ => {}
                }
            }
            out.push(Stmt::Assign(d, Rvalue::Alloc(tag, fields)));
        }
        Stmt::Store { slot, value, repr } => {
            let known =
                |w: Local| Some(shape_of(&Operand::Local(w)).map_or(Repr::Generic(w), held));
            let repr = repr.map_witnesses(&known).unwrap_or(repr);
            out.push(Stmt::Store { slot, value, repr });
        }
        Stmt::Assign(d, Rvalue::Runtime(Runtime::ListGet, args)) => match args.as_slice() {
            // `(loc, xs, i, shape)`: an element read in place, borrowed, as code that names its
            // type reads it.
            [at @ .., shape] if at.len() == 3 && shape_of(shape).is_some_and(one_word) => {
                let shape = shape_of(shape).unwrap_or_default();
                let mut args = at.to_vec();
                args.extend([Operand::word(shape), Operand::word(0)]);
                out.push(Stmt::Assign(d, Rvalue::Runtime(Runtime::ListIndex, args)));
            }
            _ => out.push(Stmt::Assign(d, Rvalue::Runtime(Runtime::ListGet, args))),
        },
        Stmt::Effect(f @ (Runtime::ListPush | Runtime::ListAppend), args) => {
            match args.as_slice() {
                // `(xs, shape, x)`: an element appended in its word, its shape named.
                [target, shape, value] if shape_of(shape).is_some_and(one_word) => {
                    let shape = shape_of(shape).unwrap_or_default();
                    let args = vec![target.clone(), Operand::word(shape), value.clone()];
                    out.push(Stmt::Effect(f, args));
                }
                _ => out.push(Stmt::Effect(f, args)),
            }
        }
        s => out.push(s),
    }
}
