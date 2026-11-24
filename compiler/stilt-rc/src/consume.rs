//! Which parameters a function consumes (values.consumed-parameters), as far as its own MIR tells,
//! and the calling convention that follows from it.
//!
//! Lowering passes every `let` parameter borrowed. A parameter is consumed when the body returns
//! it or raises it, stores it in a value, rebinds it with `var`, or passes it to a parameter that
//! its callee consumes: each of those needs a reference of its own, which a borrowed parameter
//! would have to copy. A variable that a `let` binds once to a parameter stands for it, so
//! reading the variable doesn't consume the parameter, while returning it does.
//! The callee owns a parameter it consumes, so a caller that passes its last use of a value gives
//! the value up, and copy-on-write can then change it in place. A parameter that the body takes
//! apart to build in its place is consumed too, which only the typed body tells ([`apart`]).

use stilt_mir::FnRef;
use stilt_mir::mir::{
    Arg, Block, Callee, Function, Local, Operand, ParamMode, Rvalue, Stmt, Terminator,
};

pub(crate) use stilt_mir::opt::definitions;

pub(crate) mod apart;

use crate::uses::{Use, stmt_uses, term_uses};

/// What a function's MIR does with its parameters, before its callees' conventions are known.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Summary {
    /// The parameters, by position, that the body consumes itself.
    pub consumed: Vec<usize>,
    /// Each parameter, by position, passed to a direct call: the callee, and the position of
    /// the callee's parameter it is passed to.
    pub passed: Vec<(usize, FnRef, usize)>,
}

/// The parameter each local stands for: a parameter passed borrowed whose references are
/// counted, or a local that is defined once, by a copy of one that stands for a parameter, and
/// doesn't live in memory. A local of a `var` binding stands for none, even one the code never
/// changes: rebinding a parameter with `var` consumes it (values.consumed-parameters).
fn standing(f: &Function) -> Vec<Option<usize>> {
    let mut of: Vec<Option<usize>> = vec![None; f.locals.len()];
    for (i, p) in f.params.iter().enumerate() {
        if p.mode == ParamMode::Borrowed && f.locals[p.local.0 as usize].repr.counted() {
            of[p.local.0 as usize] = Some(i);
        }
    }
    let defs = definitions(f);
    let mut changed = true;
    while changed {
        changed = false;
        for (d, s) in copies(f) {
            let i = d.0 as usize;
            let local = &f.locals[i];
            if of[i].is_none()
                && defs[i] == 1
                && !local.slot
                && !local.var
                && of[s.0 as usize].is_some()
            {
                of[i] = of[s.0 as usize];
                changed = true;
            }
        }
    }
    of
}

/// Each local defined by a copy of another, with the local it copies.
pub(crate) fn copies(f: &Function) -> impl Iterator<Item = (Local, Local)> + '_ {
    f.blocks
        .iter()
        .flat_map(|b| &b.stmts)
        .filter_map(|s| match s {
            Stmt::Assign(d, Rvalue::Use(Operand::Local(s))) => Some((*d, *s)),
            _ => None,
        })
}

/// What a function's MIR, as lowering gives it, does with its parameters.
#[must_use]
pub fn summary(f: &Function) -> Summary {
    let mut consumed = Vec::new();
    let mut passed = Vec::new();
    for u in param_uses(f) {
        match u.call {
            None => consumed.push(u.param),
            Some((g, i)) => passed.push((u.param, g, i)),
        }
    }
    consumed.sort_unstable();
    consumed.dedup();
    Summary { consumed, passed }
}

/// A use of a parameter that may consume it, in a function's MIR as lowering gives it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParamUse {
    /// The parameter, by position.
    pub param: usize,
    /// `None` for a use that consumes the parameter itself, and for a direct call that it is
    /// passed to, the callee and the position of the callee's parameter it is passed to.
    pub call: Option<(FnRef, usize)>,
    /// The location word of the code that uses it, as [`Stmt::At`] marks it, or 0 when no
    /// marker comes before it.
    pub at: u64,
}

/// Each use of a parameter that may consume it, in the order of the function's blocks.
#[must_use]
pub fn param_uses(f: &Function) -> Vec<ParamUse> {
    let of = standing(f);
    let param = |l: Local| of[l.0 as usize];
    let mut found = Vec::new();
    for block in &f.blocks {
        let mut at = 0;
        let own = |param: usize, at: u64| ParamUse {
            param,
            call: None,
            at,
        };
        for stmt in &block.stmts {
            match stmt {
                Stmt::At(word) => at = *word,
                // A local that stands for a parameter takes no reference from it.
                Stmt::Assign(d, Rvalue::Use(_)) if param(*d).is_some() => {}
                _ => {
                    let (uses, _) = stmt_uses(stmt);
                    found.extend(consuming(&uses).filter_map(param).map(|p| own(p, at)));
                }
            }
        }
        found.extend(
            consuming(&term_uses(&block.term))
                .filter_map(param)
                .map(|p| own(p, at)),
        );
        found.extend(direct_args(block).filter_map(|(g, i, l)| {
            Some(ParamUse {
                param: param(l)?,
                call: Some((g.clone(), i)),
                at,
            })
        }));
    }
    found
}

/// The location word of the code that first reads what the parameter at `param` holds, a field
/// of its object, as taking it apart does, or 0 when nothing reads one or no marker comes before.
#[must_use]
pub fn first_read(f: &Function, param: usize) -> u64 {
    let of = standing(f);
    for block in &f.blocks {
        let mut at = 0;
        for stmt in &block.stmts {
            match stmt {
                Stmt::At(word) => at = *word,
                Stmt::Assign(
                    _,
                    Rvalue::Field {
                        base: Operand::Local(l),
                        ..
                    },
                ) if of[l.0 as usize] == Some(param) => {
                    return at;
                }
                _ => {}
            }
        }
    }
    0
}

/// The locals that uses consume.
fn consuming(uses: &[(Local, Use)]) -> impl Iterator<Item = Local> + '_ {
    uses.iter()
        .filter(|(_, how)| *how == Use::Consume)
        .map(|(l, _)| *l)
}

/// Each local a block's terminator passes borrowed to a direct call, with the callee and the
/// position of the argument.
fn direct_args(block: &Block) -> impl Iterator<Item = (&FnRef, usize, Local)> + '_ {
    let call = match &block.term {
        Terminator::Call {
            callee: Callee::Direct(g),
            args,
            ..
        } => Some((g, args)),
        _ => None,
    };
    call.into_iter().flat_map(|(g, args)| {
        args.iter().enumerate().filter_map(move |(i, a)| match a {
            Arg::Borrow(Operand::Local(l)) => Some((g, i, *l)),
            _ => None,
        })
    })
}

/// The conventions a function's code follows: the parameters it consumes itself, and for each
/// direct call, in the order of its blocks, the parameters that the callee consumes. Each is a
/// list of positions. With them, each callee with in-place `let` parameters, and their
/// positions, whose arguments the call makes unique (facts.in-place-promise).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Conventions {
    /// The positions of the parameters the function consumes itself.
    pub owned: Vec<usize>,
    /// For each direct call, the positions of the parameters the callee consumes.
    pub calls: Vec<Vec<usize>>,
    /// Each callee with in-place `let` parameters, and their positions.
    pub unique: Vec<(FnRef, Vec<usize>)>,
}

/// The direct calls of a function, in the order of its blocks.
pub fn direct_callees(f: &Function) -> impl Iterator<Item = &FnRef> + '_ {
    f.blocks.iter().filter_map(|b| match &b.term {
        Terminator::Call {
            callee: Callee::Direct(g),
            ..
        } => Some(g),
        _ => None,
    })
}

/// Gives a function the conventions that consumption calls for: each parameter it consumes is
/// owned, and each argument of a direct call to a parameter that the callee consumes is given
/// to it.
pub fn apply(f: &mut Function, conventions: &Conventions) {
    for &i in &conventions.owned {
        if let Some(p) = f.params.get_mut(i)
            && p.mode == ParamMode::Borrowed
        {
            p.mode = ParamMode::Owned;
        }
    }
    let calls = f.blocks.iter_mut().filter_map(|b| match &mut b.term {
        Terminator::Call {
            callee: Callee::Direct(_),
            args,
            ..
        } => Some(args),
        _ => None,
    });
    for (args, owned) in calls.zip(&conventions.calls) {
        for &i in owned {
            if let Some(a) = args.get_mut(i)
                && let Arg::Borrow(o) = a
            {
                *a = Arg::Own(o.clone());
            }
        }
    }
}

#[cfg(test)]
mod tests;
