//! One instantiation of a function: its code with what its key knows of its hidden parameters
//! put in their place, and simplified (builds.specialization).
//!
//! What the key knows flows through the locals that are assigned once from what is known: a
//! witness's bits, a dictionary's fields, a descriptor's parts, a value parameter's number,
//! and the static data that an allocation of known parts is. A local whose value is known is
//! counted no more, since a constant is static data or a scalar; a word whose witness is known
//! is a scalar or a heap word; a call through a dictionary or a closure whose code is known
//! calls that code directly, compiled for what it knows; a call of a generic function passes
//! what it knows to an instantiation of its own; and a branch on a known condition is a jump.

use std::sync::Arc;

use super::known::{Facts, Key, Known};
use crate::FnRef;
use crate::mir::{Arg, Callee, Const, Function, Heapness, Operand, Rvalue, Stmt, Terminator};

/// What specializing one function asks of the build.
pub(crate) trait Instances {
    /// The name of the code of `f` for what `key` knows, which the build will compile.
    fn request(&mut self, f: &FnRef, key: Key) -> FnRef;
    /// The number of hidden parameters of `f`, if the build compiles it.
    fn hidden(&self, f: &FnRef) -> Option<u32>;
    /// A constant whose objects' code is compiled for each object (`super::Specializer`).
    fn rewrite(&mut self, c: &Const) -> Const;
}

/// Specializes `f` for what `key` knows of its hidden parameters after the location.
pub(crate) fn specialize(f: &mut Function, key: &Key, cx: &mut dyn Instances) {
    let facts = learn(f, key, cx);
    apply(f, &facts, cx);
    crate::prune::keep_reachable(f);
    for g in crate::walk::referenced(f) {
        if cx.hidden(&g).is_some() {
            cx.request(&g, Vec::new());
        }
    }
}

/// What the function knows of its locals.
fn learn(f: &Function, key: &Key, cx: &mut dyn Instances) -> Facts {
    let mut facts = Facts::new(f.locals.len());
    for (p, k) in f.params.iter().skip(1).zip(key) {
        let at = p.local.0 as usize;
        match k {
            Known::Const(c) => facts.values[at] = Some(cx.rewrite(c)),
            Known::Fields(fields) => {
                let fields = fields.iter().map(|c| c.as_ref().map(|c| cx.rewrite(c)));
                facts.objects[at] = Some(fields.collect());
            }
            Known::Unknown => {}
        }
    }
    let once = assigned_once(f);
    // Each round learns at least one more value, or ends.
    for _ in 0..=f.locals.len() {
        let mut learned = false;
        for s in f.blocks.iter().flat_map(|b| &b.stmts) {
            if let Stmt::Assign(d, r) = s
                && once[d.0 as usize]
                && facts.values[d.0 as usize].is_none()
                && let Some(c) = facts.fold(r)
            {
                facts.values[d.0 as usize] = Some(cx.rewrite(&c));
                learned = true;
            }
        }
        if !learned {
            break;
        }
    }
    for s in f.blocks.iter().flat_map(|b| &b.stmts) {
        if let Stmt::Assign(d, Rvalue::Alloc(_, fields)) = s
            && once[d.0 as usize]
            && facts.values[d.0 as usize].is_none()
        {
            facts.objects[d.0 as usize] = Some(object(&facts, fields, cx));
        }
    }
    facts
}

/// Whether each local is assigned exactly once and lives outside memory, so that its value
/// where it is read is the one its assignment gives.
fn assigned_once(f: &Function) -> Vec<bool> {
    let mut defs = vec![0u32; f.locals.len()];
    for p in &f.params {
        defs[p.local.0 as usize] += 1;
    }
    for b in &f.blocks {
        for s in &b.stmts {
            if let Stmt::Assign(d, _) = s {
                defs[d.0 as usize] += 1;
            }
        }
        if let Terminator::Call { dest, raised, .. } = &b.term {
            let error = raised.iter().flat_map(|(e, _)| e);
            for l in dest.iter().chain(error) {
                defs[l.0 as usize] += 1;
            }
        }
    }
    (defs.iter().zip(&f.locals))
        .map(|(&n, decl)| n == 1 && !decl.slot)
        .collect()
}

/// The fields of an object the code makes, with the code it holds compiled for what is known
/// of its other fields.
fn object(
    facts: &Facts,
    fields: &[(Operand, Heapness)],
    cx: &mut dyn Instances,
) -> Arc<[Option<Const>]> {
    let known = facts.object(fields);
    let more = known
        .iter()
        .any(|c| matches!(c, Some(c) if !matches!(c, Const::Code(_))));
    let key = if more {
        Known::Fields(Arc::clone(&known))
    } else {
        Known::Unknown
    };
    known
        .iter()
        .map(|c| match c {
            Some(Const::Code(g)) if super::object_code(g) && cx.hidden(g).is_some() => {
                Some(Const::Code(cx.request(g, vec![key.clone()])))
            }
            other => other.clone(),
        })
        .collect()
}

/// Puts what the function knows in its code.
fn apply(f: &mut Function, facts: &Facts, cx: &mut dyn Instances) {
    for decl in &mut f.locals {
        decl.repr = facts.repr(decl.repr);
    }
    let heap = |h: Heapness| match facts.heap(h) {
        Some(heap) => Heapness::Static(heap),
        None => h,
    };
    for b in &mut f.blocks {
        let stmts = std::mem::take(&mut b.stmts);
        for mut s in stmts {
            if counts_known(&s, facts) {
                continue;
            }
            super::visit::stmt_operands(&mut s, &mut |o| known(o, facts, cx));
            super::visit::stmt_heapnesses(&mut s, &heap);
            super::visit::stmt_reprs(&mut s, &|r| facts.repr(r));
            stmt(&mut s, facts);
            b.stmts.push(s);
        }
        super::visit::term_operands(&mut b.term, &mut |o| known(o, facts, cx));
        super::visit::term_heapnesses(&mut b.term, &heap);
        term(&mut b.term, facts, cx);
    }
}

/// Whether a statement counts the references of a local whose value is known, a constant,
/// which has none to count.
fn counts_known(s: &Stmt, facts: &Facts) -> bool {
    matches!(s, Stmt::Dup(l) | Stmt::Drop(l) if facts.values[l.0 as usize].is_some())
}

/// An operand with the constant it is known to hold, whose objects' code is compiled for
/// them.
fn known(o: &mut Operand, facts: &Facts, cx: &mut dyn Instances) {
    if let Operand::Local(l) = o
        && let Some(c) = &facts.values[l.0 as usize]
    {
        *o = Operand::Const(c.clone());
    }
    if let Operand::Const(c) = o {
        *o = Operand::Const(cx.rewrite(c));
    }
}

/// A statement with what is known in place: a known value assigned as the constant, and an
/// object the code makes holding the code compiled for it.
fn stmt(s: &mut Stmt, facts: &Facts) {
    let Stmt::Assign(d, r) = s else {
        return;
    };
    let at = d.0 as usize;
    if let Some(c) = &facts.values[at] {
        *r = Rvalue::Use(Operand::Const(c.clone()));
        return;
    }
    if let Rvalue::Alloc(_, fields) = r
        && let Some(object) = &facts.objects[at]
    {
        for ((o, _), c) in fields.iter_mut().zip(object.iter()) {
            if let Some(code @ Const::Code(_)) = c {
                *o = Operand::Const(code.clone());
            }
        }
    }
}

/// A terminator with what is known in place: a call through known code made directly, a call
/// of a generic function made to its instantiation, and a branch on a known value a jump.
fn term(t: &mut Terminator, facts: &Facts, cx: &mut dyn Instances) {
    match t {
        Terminator::Branch {
            cond: Operand::Const(Const::Word(c)),
            then,
            otherwise,
        } => *t = Terminator::Goto(if *c == 0 { *otherwise } else { *then }),
        Terminator::Switch {
            value: Operand::Const(Const::Word(v)),
            cases,
            otherwise,
        } => {
            let to = cases
                .iter()
                .find(|(c, _)| c == v)
                .map_or(*otherwise, |c| c.1);
            *t = Terminator::Goto(to);
        }
        Terminator::Call { callee, args, .. } => call(callee, args, facts, cx),
        _ => {}
    }
}

/// A call with what is known of its callee and arguments in place: a call through an object
/// whose code is known calls the code directly, passing it the object, as the call through it
/// would, and a direct call of compiled code calls its instantiation for what is known of its
/// hidden arguments.
fn call(callee: &mut Callee, args: &mut Vec<Arg>, facts: &Facts, cx: &mut dyn Instances) {
    let through = match &*callee {
        Callee::Value(o) => Some((o.clone(), 0)),
        Callee::Method(o, i) => Some((o.clone(), *i)),
        Callee::Direct(_) => None,
    };
    if let Some((object, index)) = through {
        let Some(Const::Code(g)) = facts.field(&object, index) else {
            return;
        };
        args.insert(1.min(args.len()), Arg::Borrow(object));
        *callee = Callee::Direct(g);
    }
    let Callee::Direct(g) = callee else {
        return;
    };
    let Some(hidden) = cx.hidden(g) else {
        return;
    };
    let key: Key = (1..hidden as usize)
        .map(|i| args.get(i).map_or(Known::Unknown, |a| arg_known(a, facts)))
        .collect();
    *callee = Callee::Direct(cx.request(g, key));
}

/// What is known of an argument a call passes to a hidden parameter.
fn arg_known(a: &Arg, facts: &Facts) -> Known {
    match a {
        Arg::Borrow(Operand::Const(c)) | Arg::Own(Operand::Const(c)) => Known::Const(c.clone()),
        Arg::Borrow(Operand::Local(l)) | Arg::Own(Operand::Local(l)) => facts.objects[l.0 as usize]
            .as_ref()
            .filter(|o| {
                o.iter()
                    .any(|c| matches!(c, Some(c) if !matches!(c, Const::Code(_))))
            })
            .map_or(Known::Unknown, |o| Known::Fields(Arc::clone(o))),
        _ => Known::Unknown,
    }
}
