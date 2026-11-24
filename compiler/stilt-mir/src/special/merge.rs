//! Folding the instantiations whose code is the same into one function (builds.specialization): two
//! instantiations of one function for types that its code holds alike, as `i64` and `u64` are
//! held where nothing but their words is read, compile to one function, and the callers of
//! each call it. Folding renames calls, which can make more functions the same, so it goes on
//! until no two are, within a bounded number of rounds.

use std::collections::HashMap;

use crate::FnRef;
use crate::mir::{Callee, Const, Function, Operand, Stmt, Terminator};

/// The most rounds of folding, each of which follows the last one's renaming one call deeper.
const ROUNDS: usize = 16;

/// Folds each instantiation into the first function before it whose code is the same, and
/// gives each name folded, with the name it was folded into.
pub(crate) fn merge(functions: &mut Vec<Function>) -> HashMap<FnRef, FnRef> {
    let mut folded: HashMap<FnRef, FnRef> = HashMap::new();
    for _ in 0..ROUNDS {
        let mut seen: HashMap<String, FnRef> = HashMap::new();
        let mut round: HashMap<FnRef, FnRef> = HashMap::new();
        for f in functions.iter() {
            let code = code_of(f);
            match seen.get(&code) {
                Some(first) if matches!(f.name, FnRef::Specialized(..)) => {
                    round.insert(f.name.clone(), first.clone());
                }
                Some(_) => {}
                None => {
                    seen.insert(code, f.name.clone());
                }
            }
        }
        if round.is_empty() {
            break;
        }
        functions.retain(|f| !round.contains_key(&f.name));
        for f in functions.iter_mut() {
            rename(f, &round);
        }
        for to in folded.values_mut() {
            if let Some(next) = round.get(to) {
                *to = next.clone();
            }
        }
        folded.extend(round);
    }
    folded
}

/// The code of a function, which two functions share when everything but their names is the
/// same.
fn code_of(f: &Function) -> String {
    format!(
        "{:?}{:?}{}{}{}{:?}",
        f.params, f.locals, f.hidden, f.results, f.broken, f.blocks
    )
}

/// `f` with each function it names that `renamed` holds named as `renamed` says.
fn rename(f: &mut Function, renamed: &HashMap<FnRef, FnRef>) {
    let mut operand = |o: &mut Operand| {
        if let Operand::Const(c) = o
            && let Some(r) = renamed_const(c, renamed)
        {
            *c = r;
        }
    };
    for b in &mut f.blocks {
        for s in &mut b.stmts {
            super::visit::stmt_operands(s, &mut operand);
            if let Stmt::Assign(_, crate::mir::Rvalue::Constant(g, ..)) = s
                && let Some(r) = renamed.get(g)
            {
                *g = r.clone();
            }
        }
        super::visit::term_operands(&mut b.term, &mut operand);
        if let Terminator::Call {
            callee: Callee::Direct(g),
            ..
        } = &mut b.term
            && let Some(r) = renamed.get(g)
        {
            *g = r.clone();
        }
    }
}

/// A constant with each code it holds that `renamed` holds renamed, or `None` if it holds none.
fn renamed_const(c: &Const, renamed: &HashMap<FnRef, FnRef>) -> Option<Const> {
    match c {
        Const::Code(g) => renamed.get(g).map(|r| Const::Code(r.clone())),
        Const::Data(tag, fields) => {
            let mut changed = false;
            let fields = fields
                .iter()
                .map(|(field, heap)| match renamed_const(field, renamed) {
                    Some(r) => {
                        changed = true;
                        (r, *heap)
                    }
                    None => (field.clone(), *heap),
                })
                .collect();
            changed.then_some(Const::Data(*tag, fields))
        }
        Const::Word(_) | Const::Str(_) => None,
    }
}
