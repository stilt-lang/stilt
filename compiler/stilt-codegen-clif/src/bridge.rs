//! Bridges between the calling conventions of one function, for hot patching. An edit that
//! changes which parameters a function consumes changes how its callers pass them (`stilt-rc`),
//! and the patch compiles those callers again, but code already running in one of their frames
//! still passes its arguments the old way. So the slot of each earlier convention gets a bridge:
//! code that takes the arguments as that convention passes them, copies those that the new
//! version takes over and the old one only borrowed, calls the new version, and releases those
//! that the old convention gave and the new version only borrows. Every call then reaches the
//! latest code, whichever convention its caller was compiled with.

use stilt_mir::mir::{
    Arg, Block, BlockId, Callee, Elements, Function, Local, LocalDecl, MEMORY_WORDS, Operand,
    Param, ParamMode, Repr, Stmt, Terminator,
};

/// The bridge to `target` from the convention that owns the parameters at `owned`.
pub(crate) fn bridge(target: &Function, owned: &[usize]) -> Function {
    let n = target.params.len();
    let mut locals = param_decls(target);
    let mut params = Vec::with_capacity(n);
    let mut args = Vec::with_capacity(n);
    let (mut copies, mut releases) = (Vec::new(), Vec::new());
    for (i, p) in target.params.iter().enumerate() {
        let here = local(i);
        let mode = match p.mode {
            ParamMode::Ref => ParamMode::Ref,
            _ if owned.contains(&i) => ParamMode::Owned,
            _ => ParamMode::Borrowed,
        };
        if locals[i].repr.counted() {
            match (mode, p.mode) {
                (ParamMode::Borrowed, ParamMode::Owned) => copies.push(Stmt::Dup(here)),
                (ParamMode::Owned, ParamMode::Borrowed) => releases.push(Stmt::Drop(here)),
                _ => {}
            }
        }
        args.push(match p.mode {
            ParamMode::Ref => Arg::Ref(Operand::Local(here)),
            ParamMode::Owned => Arg::Own(Operand::Local(here)),
            ParamMode::Borrowed => Arg::Borrow(Operand::Local(here)),
        });
        params.push(Param { local: here, mode });
    }
    // The words of the result and of the error, which the bridge only passes on: words it
    // doesn't count, as the count passes with them, many of them in memory, as an array of
    // scalars is held there.
    let words = passed(target.results);
    let dest: Vec<Local> = (n..n + words.len()).map(local).collect();
    let error: Vec<Local> = (n + words.len()..n + 2 * words.len()).map(local).collect();
    locals.extend(words.iter().chain(&words).map(|&r| decl(r)));
    let call = Terminator::Call {
        callee: Callee::Direct(target.name.clone()),
        args,
        dest: dest.clone(),
        next: BlockId(1),
        raised: Some((error.clone(), BlockId(2))),
    };
    let blocks = vec![
        Block {
            stmts: copies,
            term: call,
        },
        Block {
            stmts: releases.clone(),
            term: Terminator::Return(dest.into_iter().map(Operand::Local).collect()),
        },
        Block {
            stmts: releases,
            term: Terminator::Raise(error.into_iter().map(Operand::Local).collect()),
        },
    ];
    Function {
        name: target.name.clone(),
        params,
        hidden: target.hidden,
        results: target.results,
        locals,
        blocks,
        broken: false,
    }
}

/// The locals that hold a bridge's parameters, in order, each held as `target` holds its own.
fn param_decls(target: &Function) -> Vec<LocalDecl> {
    let position = |l: Local| target.params.iter().position(|p| p.local == l);
    target
        .params
        .iter()
        .map(|p| {
            let repr = target.locals[p.local.0 as usize].repr;
            let at = |w| Some(position(w).map_or(Repr::Heap, |i| Repr::Generic(local(i))));
            decl(repr.map_witnesses(&at).unwrap_or(Repr::Heap))
        })
        .collect()
}

/// The locals of `results` words that a bridge passes on uncounted: a word each, or past
/// [`MEMORY_WORDS`] words, one that holds them all in memory.
fn passed(results: u32) -> Vec<Repr> {
    if results as usize > MEMORY_WORDS {
        vec![Repr::Array(Elements::new(results, vec![Repr::Scalar]))]
    } else {
        vec![Repr::Scalar; results as usize]
    }
}

fn decl(repr: Repr) -> LocalDecl {
    LocalDecl {
        repr,
        slot: false,
        grouped: false,
        borrowed: false,
        var: false,
        name: None,
        shown: None,
    }
}

fn local(i: usize) -> Local {
    Local(u32::try_from(i).expect("under 4G parameters"))
}
