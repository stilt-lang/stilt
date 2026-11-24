//! The walk of a body's code in the order it is written, which records what the rules read
//! (facts.rules-of-acceptance): the writes of each body's own code, the tests that guard each
//! operation, the loops and the statement that hold it, and the `for` loops over ranges around it.
//!
//! Each closure literal's body is a body of its own, with a number: the tests, loops and
//! statements around it don't reach its code, and its writes are its own copies'.

use std::collections::{BTreeSet, HashMap};

use stilt_hir::hir::{BinaryOp, Mode};
use stilt_syntax::TextRange;

use super::Context;
use super::code::{Atom, Reader, ends_block, is_map, is_map_method};
use super::walked::{
    Declared, Frame, Looped, Op, Pending, Range, Span, Walked, Write, WriteKind, path,
};
use crate::tast::walk::{Part, parts};
use crate::tast::{
    Arg, Binding, Block, Callee, Code, Expr, ExprKind, Iterable, Pat, PatKind, Stmt, StmtKind,
};
use crate::verify::Check;

/// The walk.
pub(super) struct Walk<'a, 'c> {
    cx: &'c Context<'c>,
    out: Walked<'a>,
    active: Vec<usize>,
    loops: Vec<(u32, usize)>,
    stmts: Vec<usize>,
    ranges: Vec<usize>,
    stores: Vec<&'a Expr>,
    body: u32,
    bodies: u32,
    ids: u32,
}

impl<'a, 'c> Walk<'a, 'c> {
    pub(super) fn run(cx: &'c Context<'c>, code: &'a Code) -> Walked<'a> {
        let mut w = Walk {
            cx,
            out: Walked {
                log: Vec::new(),
                spans: Vec::new(),
                frames: Vec::new(),
                ranges: Vec::new(),
                pending: Vec::new(),
                loops: Vec::new(),
                decls: HashMap::new(),
                whens: BTreeSet::new(),
            },
            active: Vec::new(),
            loops: Vec::new(),
            stmts: Vec::new(),
            ranges: Vec::new(),
            stores: Vec::new(),
            body: 0,
            bodies: 1,
            ids: 0,
        };
        match code {
            Code::Block(b) => w.block(b),
            Code::Expr(e) => w.expr(e),
        }
        w.out
    }

    fn reader(&self) -> Reader<'_> {
        Reader {
            cx: self.cx,
            whens: &self.out.whens,
        }
    }

    fn id(&mut self) -> u32 {
        self.ids += 1;
        self.ids
    }

    /// Opens a span at the log's end.
    fn open(&mut self) -> usize {
        let at = self.out.log.len();
        self.out.spans.push(Span { start: at, end: at });
        self.out.spans.len() - 1
    }

    fn close(&mut self, span: usize) {
        self.out.spans[span].end = self.out.log.len();
    }

    /// Makes `atoms`, which hold since the log stood at `start`, guard the code walked next.
    fn guard(&mut self, atoms: Vec<Atom>, start: usize) {
        if atoms.is_empty() {
            return;
        }
        let id = self.id();
        self.out.frames.push(Frame { atoms, start, id });
        self.active.push(self.out.frames.len() - 1);
    }

    fn pend(&mut self, op: Op<'a>, at: TextRange, check: Option<Check>) {
        self.out.pending.push(Pending {
            op,
            at,
            check,
            body: self.body,
            log_at: self.out.log.len(),
            frames: self.active.clone(),
            loops: self.loops.clone(),
            stmt: self.stmts.last().copied(),
            ranges: self.ranges.clone(),
        });
    }

    /// Logs a write of `place`, if a binding roots it.
    fn write(&mut self, place: &'a Expr, kind: WriteKind, value: Option<&'a Expr>) {
        let Some((root, fields, indexed)) = path(place) else {
            return;
        };
        self.out.log.push(Write {
            body: self.body,
            root,
            fields,
            indexed,
            kind,
            value,
            at: place.at.start(),
        });
    }

    fn block(&mut self, b: &'a Block) {
        let depth = self.active.len();
        for s in b {
            self.stmt(s);
        }
        self.active.truncate(depth);
    }

    fn stmt(&mut self, s: &'a Stmt) {
        let span = self.open();
        self.stmts.push(span);
        match &s.kind {
            StmtKind::Assign(op, place, value) => self.assign(s, *op, place, value),
            StmtKind::Let(b) => self.binding(b, false),
            StmtKind::Var(b) => self.binding(b, true),
            StmtKind::Yield(place) => {
                self.expr(place);
                self.write(place, WriteKind::Yield, None);
            }
            StmtKind::Assert(e) | StmtKind::Expr(e) => self.expr(e),
        }
        self.stmts.pop();
        self.close(span);
        self.after(s, self.out.spans[span].start);
    }

    /// The facts a statement gives the code after it in its block: an `if` whose then-branch
    /// can't complete gives its condition's negation, and a store of a key gives it present.
    fn after(&mut self, s: &'a Stmt, start: usize) {
        let mut atoms = Vec::new();
        if let StmtKind::Expr(e) = &s.kind
            && let ExprKind::If(c, then, _) = &e.kind
            && ends_block(then)
        {
            self.reader().gives(c, false, &mut atoms);
        }
        let reader = self.reader();
        if let Some((m, k)) = reader.stored(s).or_else(|| reader.stored_if_missing(s)) {
            atoms.push(Atom::Contains(m, k));
        }
        self.guard(atoms, start);
    }

    fn assign(&mut self, s: &'a Stmt, op: Option<BinaryOp>, place: &'a Expr, value: &'a Expr) {
        match (&place.kind, op) {
            (ExprKind::Index(m, _), None) if is_map(&m.ty) => self.stores.push(place),
            (_, Some(BinaryOp::Div | BinaryOp::Rem)) if divides(place, value) => {
                self.pend(Op::Division(value), s.at, Some(Check::DivideByZero));
            }
            _ => {}
        }
        self.expr(place);
        self.expr(value);
        self.write(place, WriteKind::Assign(op), Some(value));
    }

    fn binding(&mut self, b: &'a Binding, var: bool) {
        self.expr(&b.value);
        if let Some(otherwise) = &b.otherwise {
            self.expr(otherwise);
        }
        if let PatKind::Bind(v) = b.pattern.kind {
            let declared = if var {
                Declared::Var(&b.value)
            } else {
                Declared::Let(&b.value)
            };
            self.out.decls.insert(v, (self.body, declared));
        }
    }

    fn parts(&mut self, e: &'a Expr) {
        for part in parts(e) {
            match part {
                Part::Expr(x) => self.expr(x),
                Part::Block(b) => self.block(b),
            }
        }
    }

    fn expr(&mut self, e: &'a Expr) {
        match &e.kind {
            ExprKind::Closure(_, body) => self.closure(body),
            ExprKind::If(c, then, alt) => self.if_(c, then, alt.as_deref()),
            ExprKind::While(c, b) => self.looped(e, Some(c), b),
            ExprKind::Loop(b) => self.looped(e, None, b),
            ExprKind::For(p, iterable, b) => self.for_(p, iterable, b),
            ExprKind::Index(base, key) => {
                if !self.stores.iter().any(|s| std::ptr::eq(*s, e)) {
                    let check = if is_map(&base.ty) {
                        Check::MissingKey
                    } else {
                        Check::Bounds
                    };
                    self.pend(Op::Index(base, key), e.at, Some(check));
                }
                self.parts(e);
            }
            ExprKind::Binary(op @ (BinaryOp::And | BinaryOp::Or), a, b) => {
                self.operands(*op == BinaryOp::And, a, b);
            }
            ExprKind::Binary(BinaryOp::Div | BinaryOp::Rem, a, b) if divides(a, b) => {
                self.pend(Op::Division(b), e.at, Some(Check::DivideByZero));
                self.parts(e);
            }
            ExprKind::Call(c, _, args, _) | ExprKind::Project(c, _, args, _) => {
                self.call(e, Some(c), args);
            }
            ExprKind::CallValue(_, args) => self.call(e, None, args),
            ExprKind::When(held, _) => {
                self.out.whens.extend(held.iter().map(|(_, v)| *v));
                self.parts(e);
            }
            _ => self.parts(e),
        }
    }

    fn call(&mut self, e: &'a Expr, c: Option<&Callee>, args: &'a [Arg]) {
        let own = self.cx.key;
        if let Some(c) = c
            && own.is_some()
            && crate::analyses::implicit::callee_key(self.cx.decls, c).as_ref() == own
        {
            self.pend(Op::SelfCall(args), e.at, None);
        }
        self.parts(e);
        for (i, a) in args.iter().enumerate() {
            if a.mode == Mode::Inout {
                let insert = i == 0 && c.is_some_and(|c| is_map_method(c, "insert"));
                let kind = if insert {
                    WriteKind::Insert
                } else {
                    WriteKind::Inout
                };
                self.write(&a.value, kind, None);
            }
        }
    }

    /// A closure literal's body, a body of its own.
    fn closure(&mut self, body: &'a Expr) {
        let outer = self.body;
        self.body = self.bodies;
        self.bodies += 1;
        let active = std::mem::take(&mut self.active);
        let loops = std::mem::take(&mut self.loops);
        let stmts = std::mem::take(&mut self.stmts);
        self.expr(body);
        self.active = active;
        self.loops = loops;
        self.stmts = stmts;
        self.body = outer;
    }

    /// The condition of an `if` or a `while`, a statement of its own (facts.guarding-tests).
    fn condition(&mut self, c: &'a Expr) {
        let span = self.open();
        self.stmts.push(span);
        self.expr(c);
        self.stmts.pop();
        self.close(span);
    }

    fn if_(&mut self, c: &'a Expr, then: &'a Block, alt: Option<&'a Expr>) {
        let start = self.out.log.len();
        self.condition(c);
        let depth = self.active.len();
        let (mut yes, mut no) = (Vec::new(), Vec::new());
        self.reader().gives(c, true, &mut yes);
        self.reader().gives(c, false, &mut no);
        self.guard(yes, start);
        self.block(then);
        self.active.truncate(depth);
        if let Some(alt) = alt {
            self.guard(no, start);
            self.expr(alt);
            self.active.truncate(depth);
        }
    }

    /// The operands of `&&`, when `and`, or of `||`: the left one guards the right one, with
    /// its facts where it holds for `&&`, and where it fails for `||` (facts.guarding-tests).
    fn operands(&mut self, and: bool, a: &'a Expr, b: &'a Expr) {
        let start = self.out.log.len();
        self.expr(a);
        let depth = self.active.len();
        let mut atoms = Vec::new();
        self.reader().gives(a, and, &mut atoms);
        self.guard(atoms, start);
        self.expr(b);
        self.active.truncate(depth);
    }

    /// A `while`, whose condition guards its body, or a `loop`.
    fn looped(&mut self, e: &'a Expr, c: Option<&'a Expr>, b: &'a Block) {
        let span = self.open();
        let id = self.id();
        self.loops.push((id, span));
        let start = self.out.log.len();
        let depth = self.active.len();
        if let Some(c) = c {
            self.condition(c);
            let mut atoms = Vec::new();
            self.reader().gives(c, true, &mut atoms);
            self.guard(atoms, start);
        }
        self.block(b);
        self.active.truncate(depth);
        self.loops.pop();
        self.close(span);
        self.out.loops.push(Looped {
            at: e.at,
            body: self.body,
            cond: c,
            block: b,
            span,
        });
    }

    fn for_(&mut self, p: &'a Pat, iterable: &'a Iterable, b: &'a Block) {
        match iterable {
            Iterable::Iter(source) => self.expr(source),
            Iterable::Range(a, z, _) => {
                self.expr(a);
                self.expr(z);
            }
        }
        let span = self.open();
        let id = self.id();
        self.loops.push((id, span));
        let n = self.ranges.len();
        if let (PatKind::Bind(v), Iterable::Range(a, z, inclusive)) = (&p.kind, iterable) {
            self.out.decls.insert(*v, (self.body, Declared::Range(a)));
            self.out.ranges.push(Range {
                body: self.body,
                var: *v,
                start: a,
                end: z,
                inclusive: *inclusive,
                span,
            });
            self.ranges.push(self.out.ranges.len() - 1);
        }
        self.block(b);
        self.ranges.truncate(n);
        self.loops.pop();
        self.close(span);
    }
}

/// Whether dividing `a` by `b` can panic: an integer division whose divisor may be zero, as
/// the sites of effects.panicking-operations count it.
pub(super) fn divides(a: &Expr, b: &Expr) -> bool {
    crate::analyses::implicit::divides(a, b)
}
