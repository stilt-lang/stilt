//! Splicing a callee's body in place of a call. The callee's blocks are appended to the caller's
//! and its locals become the caller's own, but for each parameter that its argument can stand
//! for, which it then does. A return assigns the words of the result to the call's locals and
//! goes on where the call would, and a raise assigns the error's and goes where the call's
//! raised edge does.
//!
//! The ownership of every word stays as the call had it: the caller lends each argument, and
//! the body's code, lowered to borrow each parameter, reads the argument in its place, copying
//! it where a use takes a reference, as reference counting then decides for the caller.

use crate::mir::{BlockId, Function, Local, LocalDecl, Operand, Rvalue, Stmt, Terminator};
use crate::opt::defs::definitions;
use crate::opt::inline::rename::Renaming;

/// A function to splice in place of a call, and the operands its parameters take, in order.
pub(crate) struct Body<'a> {
    pub(crate) function: &'a Function,
    pub(crate) args: Vec<Operand>,
    /// Whether the function is the standard library's, whose locals have no names that a
    /// debugger shows in the caller.
    pub(crate) std: bool,
}

/// Where a call goes on: the locals of its result, the block after it, and its raised edge.
struct Exit {
    dest: Vec<Local>,
    next: BlockId,
    raised: Option<(Vec<Local>, BlockId)>,
}

/// Splices `body` in place of the call that ends block `at` of `f`, and returns whether it did:
/// it doesn't when the call defines a local that is also an argument, or when the body returns
/// or raises more words than the call takes.
pub(crate) fn splice(f: &mut Function, at: BlockId, body: &Body<'_>) -> bool {
    let Terminator::Call {
        dest, next, raised, ..
    } = &f.blocks[at.0 as usize].term
    else {
        return false;
    };
    let exit = Exit {
        dest: dest.clone(),
        next: *next,
        raised: raised.clone(),
    };
    let defined = exit
        .dest
        .iter()
        .chain(exit.raised.iter().flat_map(|(e, _)| e));
    if body.args.len() != body.function.params.len()
        || defined
            .into_iter()
            .any(|l| body.args.contains(&Operand::Local(*l)))
    {
        return false;
    }
    let (renaming, decls, copies) = bind(f, body);
    let call_at = location(&f.blocks[at.0 as usize].stmts);
    let Some(blocks) = blocks(body, &renaming, &exit, call_at) else {
        return false;
    };
    let Some(decls) = decls
        .into_iter()
        .map(|d| {
            Some(LocalDecl {
                repr: renaming.repr(d.repr)?,
                ..d
            })
        })
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    f.locals.extend(decls);
    let call = &mut f.blocks[at.0 as usize];
    call.stmts.extend(copies);
    call.term = Terminator::Goto(BlockId(renaming.blocks));
    f.blocks.extend(blocks);
    true
}

/// What each of the body's locals becomes in `f`: the argument of each parameter it can stand
/// for, and a new local for every other, whose declaration is returned with the copy of each
/// argument into the new local of its parameter.
fn bind(f: &Function, body: &Body<'_>) -> (Renaming, Vec<LocalDecl>, Vec<Stmt>) {
    let g = body.function;
    let defs = definitions(g);
    let pinned = pinned(g);
    let mut stands: Vec<Option<Operand>> = vec![None; g.locals.len()];
    for (p, arg) in g.params.iter().zip(&body.args) {
        let l = p.local.0 as usize;
        let stands_for = match arg {
            Operand::Const(_) => !pinned[l],
            Operand::Local(a) => !f.locals[a.0 as usize].slot,
        };
        if stands_for && !g.locals[l].slot && defs[l] == 1 {
            stands[l] = Some(arg.clone());
        }
    }
    let first = f.locals.len();
    let mut decls = Vec::new();
    let locals = stands
        .into_iter()
        .zip(&g.locals)
        .map(|(stands, decl)| {
            stands.unwrap_or_else(|| {
                let l = Local(u32::try_from(first + decls.len()).expect("under 4G locals"));
                decls.push(caller_decl(decl, body.std));
                Operand::Local(l)
            })
        })
        .collect();
    let renaming = Renaming {
        locals,
        blocks: u32::try_from(f.blocks.len()).expect("under 4G blocks"),
    };
    let copies = g
        .params
        .iter()
        .zip(&body.args)
        .filter_map(|(p, arg)| {
            let l = renaming.local(p.local)?;
            (renaming.locals[p.local.0 as usize] != *arg)
                .then(|| Stmt::Assign(l, Rvalue::Use(arg.clone())))
        })
        .collect();
    (renaming, decls, copies)
}

/// The declaration in the caller of a local of the body: owning its value, since what it
/// borrowed from outlived the body's call and may not outlive the body in the caller, and
/// without the name and type a debugger shows if it is the standard library's.
fn caller_decl(decl: &LocalDecl, std: bool) -> LocalDecl {
    let mut d = decl.clone();
    d.borrowed = false;
    if std {
        d.name = None;
        d.shown = None;
    }
    d
}

/// Which locals of `g` only a local can stand for: the witnesses of representations, and the
/// locals whose slots are taken.
fn pinned(g: &Function) -> Vec<bool> {
    let mut pinned = vec![false; g.locals.len()];
    let mut locals: Vec<Local> = g.locals.iter().flat_map(|d| d.repr.witnesses()).collect();
    for s in g.blocks.iter().flat_map(|b| &b.stmts) {
        match s {
            Stmt::Store { repr, .. } => locals.extend(repr.witnesses()),
            Stmt::Assign(_, Rvalue::Alloc(_, fields)) => {
                locals.extend(fields.iter().flat_map(|(_, h)| h.witnesses()));
            }
            Stmt::Assign(_, Rvalue::SlotOf(l)) => locals.push(*l),
            _ => {}
        }
    }
    for l in locals {
        pinned[l.0 as usize] = true;
    }
    pinned
}

/// The location the code of a block's terminator comes from: its last marker's, or 0.
fn location(stmts: &[Stmt]) -> u64 {
    stmts
        .iter()
        .rev()
        .find_map(|s| match s {
            Stmt::At(word) => Some(*word),
            _ => None,
        })
        .unwrap_or(0)
}

/// The body's blocks as the caller's: renamed, each return and raise leaving through `exit`,
/// and each block that no marker starts marked with the call's location, so that a debugger's
/// line table puts the body's code on the line of the call (goal debuggable-builds).
fn blocks(
    body: &Body<'_>,
    renaming: &Renaming,
    exit: &Exit,
    call_at: u64,
) -> Option<Vec<crate::mir::Block>> {
    let released = released(body.function, renaming)?;
    body.function
        .blocks
        .iter()
        .map(|b| {
            let mut stmts: Vec<Stmt> = Vec::with_capacity(b.stmts.len() + 1);
            if call_at != 0 && !matches!(b.stmts.first(), Some(Stmt::At(_))) {
                stmts.push(Stmt::At(call_at));
            }
            for s in &b.stmts {
                stmts.push(renaming.stmt(s)?);
            }
            let term = match &b.term {
                Terminator::Return(os) => {
                    stmts.extend(assigned(&exit.dest, os, renaming)?);
                    stmts.extend(released.iter().cloned());
                    Terminator::Goto(exit.next)
                }
                Terminator::Raise(os) => match &exit.raised {
                    Some((error, to)) => {
                        stmts.extend(assigned(error, os, renaming)?);
                        stmts.extend(released.iter().cloned());
                        Terminator::Goto(*to)
                    }
                    // The call can't raise, so neither can the body where the caller calls it.
                    None => Terminator::Unreachable,
                },
                t => renaming.term(t)?,
            };
            Some(crate::mir::Block { stmts, term })
        })
        .collect()
}

/// What releases, as the body leaves, what its locals in memory hold, as its return would:
/// each is given 0, which reference counting releases what it held for, and which releases
/// nothing when the caller returns. A list that the body builds in memory and returns is then
/// unique in the caller, as it was after the call.
fn released(g: &Function, renaming: &Renaming) -> Option<Vec<Stmt>> {
    g.locals
        .iter()
        .enumerate()
        .filter(|(_, d)| d.slot && d.repr.counted())
        .map(|(l, _)| {
            let l = renaming.local(Local(u32::try_from(l).expect("under 4G locals")))?;
            Some(Stmt::Assign(l, Rvalue::Use(Operand::word(0))))
        })
        .collect()
}

/// The assignments of the words `os` to the locals `into`, those it lacks being 0, as a call
/// gives the words its callee doesn't return.
fn assigned(into: &[Local], os: &[Operand], renaming: &Renaming) -> Option<Vec<Stmt>> {
    if os.len() > into.len() {
        return None;
    }
    Some(
        into.iter()
            .enumerate()
            .map(|(i, &l)| {
                let word = os.get(i).map_or(Operand::word(0), |o| renaming.operand(o));
                Stmt::Assign(l, Rvalue::Use(word))
            })
            .collect(),
    )
}
