//! The operations of a body that may share values between threads, whose reference counts are
//! then updated atomically, which `stilt show` prints at their lines (par.atomic-sites; goal
//! atomic-counts-where-shared): the calls of `std.par`'s functions, of `Shared.new`, the `when`s,
//! and the calls of `spawn` and `task.scope` whose function may reach a task's handle, a closure
//! literal's included.

use stilt_db::{Db, Program, SourceFile};
use stilt_hir::body_starts;
use stilt_syntax::TextRange;

use crate::analyses::demands::{captures, holds, is_scope};
use crate::queries::infer_body;
use crate::tast::walk::{iter, iter_block};
use crate::tast::{Arg, Callee, Code, Definition, Expr, ExprKind};
use crate::ty::{Ty, is_shared};

/// Whether a type holds a task's handle, or a function, which may capture one.
fn may_reach_a_task(ty: &Ty) -> bool {
    holds(ty, &|t| match t {
        Ty::Con(item, _) => (&*item.home, &*item.name) == ("std.task", "Task"),
        Ty::Fn(_) => true,
        _ => false,
    })
}

/// Whether the function that a `spawn` or a `task.scope` runs may reach a task's handle, which
/// the call then marks shared, with the task's value (): a
/// closure literal that captures a value of a type that holds one or a function, and any other
/// function value.
fn spawns_handles(f: Option<&Arg>) -> bool {
    match f.map(|a| &a.value) {
        Some(
            e @ Expr {
                kind: ExprKind::Closure(..),
                ..
            },
        ) => captures(e).iter().any(|(_, x)| may_reach_a_task(&x.ty)),
        Some(_) => true,
        None => false,
    }
}

/// What a `spawn` whose function may reach a task's handle shares.
const SPAWN: &str = "`spawn` makes the counts of the task handles its function reaches atomic";

/// What a `task.scope` whose function may reach a task's handle shares.
const SCOPE: &str = "`task.scope` makes the counts of the task handles its function reaches atomic";

/// What the operation `e` shares between threads, if it may share anything (par.atomic-sites).
fn shares(e: &Expr, names: &dyn Fn(&Expr) -> Option<String>) -> Option<String> {
    match &e.kind {
        ExprKind::Call(Callee::Function(item), ..) if &*item.home == "std.par" => {
            Some(match &*item.name {
                "both" => "`par.both` makes the counts of its second closure atomic".to_owned(),
                name => format!(
                    "`par.{name}` makes the counts of its closure and of its list's shared \
                     elements atomic"
                ),
            })
        }
        ExprKind::Call(Callee::Member(owner, name), ..) if is_shared(owner) && &**name == "new" => {
            Some("`Shared.new` makes the counts of its value atomic".to_owned())
        }
        ExprKind::Call(Callee::Function(item), _, args, _)
            if &*item.home == "std.task"
                && matches!(&*item.name, "spawn" | "scope")
                && spawns_handles(args.first()) =>
        {
            Some(if &*item.name == "scope" { SCOPE } else { SPAWN }.to_owned())
        }
        ExprKind::Call(Callee::Member(owner, name), _, args, _)
            if is_scope(owner) && &**name == "spawn" && spawns_handles(args.get(1)) =>
        {
            Some(SPAWN.to_owned())
        }
        ExprKind::When(held, _) => {
            let held: Vec<String> = held.iter().filter_map(|(h, _)| names(h)).collect();
            Some(format!(
                "this `when` makes the counts of what it leaves in {} atomic",
                held.join(" and ")
            ))
        }
        _ => None,
    }
}

/// The operations of the body `index` of a file's module that may share values between
/// threads, each with where it is in its file and what it shares, in the order of the body. A
/// body with an error has none.
#[must_use]
pub fn atomic_causes(
    db: &dyn Db,
    program: Program,
    file: SourceFile,
    index: u32,
) -> Vec<(TextRange, String)> {
    let typed = &infer_body(db, program, file, index).body;
    let Definition::Code(code) = &typed.code else {
        return Vec::new();
    };
    let start = body_starts(db, program, file)[index as usize];
    let names = |h: &Expr| match h.kind {
        ExprKind::Local(v) => typed.locals.get(v.0 as usize).map(|n| format!("`{n}`")),
        _ => None,
    };
    let mut found = Vec::new();
    let mut each = |e: &Expr| {
        if let Some(says) = shares(e, &names) {
            found.push((e.at + start, says));
        }
    };
    match code {
        Code::Block(b) => iter_block(b, &mut |_| {}, &mut each),
        Code::Expr(e) => iter(e, &mut |_| {}, &mut each),
    }
    found
}
