//! Calls and closure literals in the walk.

use stilt_hir::hir::Mode;
use stilt_mir::FnRef;
use stilt_types::tast::{Arg, Callee, Expr, Pat};
use stilt_types::ty::Ty;

use stilt_hir::hir::LocalId;

use super::super::places::{self, binders, captures, indexes};
use super::super::{Copy, Holder, How, Into, Kind, Modification, Write};
use super::Walk;

impl Walk<'_> {
    /// A call by name, whose callee consumes some of its parameters (values.consumed-parameters).
    pub(super) fn call(&mut self, e: &Expr, callee: &Callee, args: &[Arg], into: &Into<'_>) {
        let g = self.calls.callee(callee);
        let consumed = g
            .as_ref()
            .map(|g| self.calls.consumed(g))
            .unwrap_or_default();
        self.args(e, args, &consumed, g.as_ref(), into);
        if let (Callee::Member(owner, name), [a]) = (callee, args)
            && stilt_types::ty::is_shared(owner)
            && &**name == "new"
            && let Some((binding, path)) = places::place(&a.value)
        {
            // modes.handles: the handle shares the value, where later `when`s may write it.
            let tick = self.tick(e.at.end());
            self.flow.handed.push(Write {
                binding,
                path,
                at: e.at,
                tick,
                replaces: false,
                how: Modification::NewHandle,
            });
        }
    }

    /// The arguments of a call, from left to right, of which `g`, the function called by name,
    /// consumes those at `consumed`. A binding passed to a consumed parameter escapes
    /// (modes.escaping), and one passed to a parameter that the call may store doesn't
    /// (modes.call-stores). The call copies either, or, at its last use, passes on the copies it
    /// holds, as a copy of it would: these last as the call's result does, and as each binding
    /// that an `inout` argument is a part of (modes.copies). An `inout` argument doesn't escape
    /// (modes.not-escaping): it is modified from the start of the call, and read after all those
    /// modifications until the call returns (modes.durations and modes.shared-holders), a read
    /// that counts for those modifications, since a later one is shared itself.
    pub(super) fn args(
        &mut self,
        e: &Expr,
        args: &[Arg],
        consumed: &[usize],
        g: Option<&FnRef>,
        into: &Into<'_>,
    ) {
        let start = self.passed.len();
        let copies = self.flow.copies.len();
        let result = into.keeper();
        let read = Into::read(e.at.end());
        let targets: Vec<Ty> = std::iter::once(e.ty.clone())
            .chain(
                args.iter()
                    .filter(|a| a.mode == Mode::Inout)
                    .map(|a| a.value.ty.clone()),
            )
            .collect();
        for (i, a) in args.iter().enumerate() {
            match g {
                _ if a.mode == Mode::Inout => {
                    for x in indexes(&a.value) {
                        self.expr(x, &read);
                    }
                }
                Some(g) if consumed.contains(&i) => {
                    let into = Into {
                        leaves: Some(How::Consumed(g.clone())),
                        result: Some(result.clone()),
                        at: None,
                        ..Into::read(e.at.end())
                    };
                    self.expr(&a.value, &into);
                }
                _ if self.calls.may_store(&a.value.ty, &targets) => {
                    let into = Into {
                        result: Some(result.clone()),
                        at: None,
                        ..Into::read(e.at.end())
                    };
                    self.expr(&a.value, &into);
                }
                _ => self.expr(&a.value, &read),
            }
        }
        for (binding, path, made, holder) in self.passed.split_off(start) {
            self.copy(binding, path, made, holder, true, None);
        }
        self.stored_in_inouts(args, copies, &result);
        let first = self.here() + 1;
        for a in args.iter().filter(|a| a.mode == Mode::Inout) {
            self.write(&a.value, a.value.at, e.at.end(), false);
        }
        let read = self.tick(e.at.end());
        let roots = args
            .iter()
            .filter(|a| a.mode == Mode::Inout)
            .filter_map(|a| places::place(&a.value));
        let reads = roots.map(|(root, _)| (root, first, read));
        self.flow.inout_reads.extend(reads);
    }

    /// The copies from the `copies`th on, those that the arguments made, held by the call's
    /// result, held as well by each binding that an `inout` argument is a part of, at no known
    /// place in it (modes.copies).
    fn stored_in_inouts(&mut self, args: &[Arg], copies: usize, result: &Holder) {
        let roots: Vec<LocalId> = args
            .iter()
            .filter(|a| a.mode == Mode::Inout)
            .filter_map(|a| places::place(&a.value).map(|(root, _)| root))
            .collect();
        let made: Vec<Copy> = self.flow.copies[copies..]
            .iter()
            .filter(|c| c.holder == *result)
            .cloned()
            .collect();
        for c in made {
            for &root in &roots {
                self.flow.copies.push(Copy {
                    holder: Holder::Place(root),
                    stored: true,
                    at: None,
                    ..c.clone()
                });
            }
        }
    }

    /// A closure literal copies the bindings it captures, and what holds the closure holds the
    /// copies (modes.copies). It escapes, with what it captures, where it leaves the function, and
    /// where what holds it does (modes.escaping and modes.not-escaping). Its body is a function of
    /// its own.
    pub(super) fn closure(&mut self, e: &Expr, params: &[Pat], body: &Expr, into: &Into<'_>) {
        let at = e.at.start();
        let made = (at, self.tick(at));
        let keeper = into.keeper();
        let mut held = Vec::new();
        for (v, ty) in captures(params, body) {
            let Some(decl) = self.own(v) else { continue };
            if !self.calls.cow(&ty) {
                continue;
            }
            self.copy(v, Vec::new(), made, keeper.clone(), true, None);
            if matches!(decl.kind, Kind::Param(_)) {
                continue;
            }
            match &into.leaves {
                Some(_) => self.flow.escapes.push((v, at, How::Captured)),
                None => held.push(v),
            }
        }
        if let (Holder::Bound(holders, _), false) = (&keeper, held.is_empty()) {
            self.flow.held.push((holders.clone(), at, held));
        }
        self.inside(e, params, body);
    }

    /// The body of a closure literal: its parameters, with the modes its type gives them, last
    /// until it ends, its value is returned, and lowering marks none of it until a statement of
    /// its own starts. The paths of the function around it go through the body, as if a call ran
    /// it where it is written, and around it (modes.shared-writes).
    fn inside(&mut self, e: &Expr, params: &[Pat], body: &Expr) {
        let outer = (self.frame, std::mem::take(&mut self.targets));
        self.frames += 1;
        self.frame = self.frames;
        let modes: Vec<Mode> = match &e.ty {
            Ty::Fn(f) if f.params.len() == params.len() => {
                f.params.iter().map(|(mode, _)| *mode).collect()
            }
            _ => vec![Mode::Let; params.len()],
        };
        for (p, mode) in params.iter().zip(modes) {
            for v in binders(p) {
                self.declare(v, Kind::Param(mode), body.at);
            }
        }
        let before = self.here();
        self.meet(body.at.start(), &[before], &[]);
        self.expr(body, &Into::leaving(How::Returned));
        let end = self.here();
        self.meet(e.at.end(), &[before, end], &[]);
        (self.frame, self.targets) = outer;
    }
}
