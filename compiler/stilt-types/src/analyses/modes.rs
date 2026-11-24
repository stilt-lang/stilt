//! Modes and exclusivity (modes.law and modes.overlap): the errors of a body. Rule numbers in
//! comments refer to the Reference's modes chapter, unless they name another record. The reads that
//! views make join those of `for` loops (views.reads-that-last and views.change-while-viewed;
//! `viewing`), and the writes of writable bindings, which no access may reach
//! (projections.what-view-writes and projections.reaching-written-source). A projection's call is a
//! place that holds every place its `inout` arguments hold, for the whole access
//! (projections.call-is-place and projections.when-projection-runs).

pub(super) mod places;
mod viewing;

use std::collections::{HashMap, HashSet};

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_hir::hir::{LocalId, Mode, Name};
use stilt_syntax::{TextRange, TextSize};

use self::places::{
    Aliases, Place, expr_let_bindings, expr_var_bindings, inout_params, let_bindings, overlap,
    place, place_parts, projection_root, var_bindings,
};
use self::viewing::Viewing;
use super::views::Sources;
use crate::tast::walk::{self, Part};
use crate::tast::{Arg, Block, Expr, ExprKind, Iterable, Pat, PatKind, Stmt, StmtKind};
use crate::ty::Ty;

/// What the exclusivity of a body reads beside its code: the sources of its views, where its
/// block ends, and its text from its start, which a fix may need.
pub(crate) struct Body<'a> {
    pub(crate) locals: &'a [Name],
    pub(crate) params: &'a [(Mode, LocalId)],
    pub(crate) sources: &'a Sources,
    pub(crate) end: TextSize,
    pub(crate) text: &'a dyn Fn() -> Option<String>,
}

/// modes.law, modes.durations, modes.overlapping-inout, modes.change-while-iterating,
/// modes.closures and modes.what-can-be-modified, and expressions.capture and
/// expressions.inout-closure-parameters: a body's modifications of what it can't modify,
/// overlapping `inout` arguments, modifications of a place that a `for` loop or a view reads
/// (views.change-while-viewed), and accesses to a place that a writable binding writes
/// (projections.reaching-written-source). A modification of what can't be modified is reported as
/// that alone, and takes no part in modes.overlapping-inout.
pub(crate) fn errors<'a>(body: &Body<'a>, block: &'a Block) -> Vec<Diagnostic> {
    let mut errors = Errors {
        locals: body.locals,
        modifiable: inout_params(body.params)
            .chain(var_bindings(block))
            .collect(),
        lets: let_bindings(block).into_iter().collect(),
        iterating: Vec::new(),
        viewing: Viewing {
            sources: body.sources,
            aliases: Aliases::of(block),
            reads: Vec::new(),
            text: body.text,
        },
        stmt: None,
        found: Vec::new(),
    };
    errors.block(block, body.end);
    errors.found
}

/// The `inout` parameters of a closure, which its type gives
/// (expressions.inout-closure-parameters).
fn closure_inouts<'e>(e: &'e Expr, params: &'e [Pat]) -> impl Iterator<Item = LocalId> + 'e {
    let modes: &[(Mode, Ty)] = match &e.ty {
        Ty::Fn(f) if f.params.len() == params.len() => &f.params,
        _ => &[],
    };
    modes
        .iter()
        .zip(params)
        .filter_map(|((mode, _), p)| match (mode, &p.kind) {
            (Mode::Inout, PatKind::Bind(id)) => Some(*id),
            _ => None,
        })
}

/// The errors found so far, and what the code being checked may do.
struct Errors<'a> {
    locals: &'a [Name],
    /// The variables the code may modify.
    modifiable: HashSet<LocalId>,
    /// The variables that `let` statements declare where the code may modify `var` bindings,
    /// at the start of each statement.
    lets: HashMap<LocalId, TextSize>,
    /// The places the enclosing `for` loops read.
    iterating: Vec<Place>,
    /// The sources that views read.
    viewing: Viewing<'a>,
    /// The statement being checked.
    stmt: Option<&'a Stmt>,
    found: Vec<Diagnostic>,
}

/// Where the block directly inside an expression ends, its reads with it: after its closing
/// brace, or for the block of an `if` with an `else`, where the `else` starts.
fn block_end(e: &Expr) -> TextSize {
    match &e.kind {
        ExprKind::If(_, _, Some(alt)) | ExprKind::IfLet(_, _, _, Some(alt)) => alt.at.start(),
        _ => e.at.end(),
    }
}

impl<'a> Errors<'a> {
    /// A modification of `e`, which is a place, if it is allowed at all, and the places it
    /// holds: the place itself, or for a place rooted in a projection's call, every place its
    /// `inout` arguments hold, for the whole access (projections.when-projection-runs).
    fn modify(&mut self, e: &'a Expr) -> Vec<Place> {
        match projection_root(e) {
            Some(args) => self.call(None, args),
            None => self.modify_place(e).into_iter().collect(),
        }
    }

    /// A modification of `e`, which names a place, if it is allowed at all.
    fn modify_place(&mut self, e: &Expr) -> Option<Place> {
        let p = place(e)?;
        let name = p.name(self.locals);
        if !self.modifiable.contains(&p.root) {
            let d = Diagnostic::new(
                codes::E0403,
                e.at,
                format!(
                    "`{name}` can't be modified here; only `var` bindings and `inout` \
                     parameters of this body can"
                ),
            );
            let declared = self.lets.get(&p.root).map(|&at| {
                let keyword = TextRange::at(at, TextSize::of("let"));
                let root = &self.locals[p.root.0 as usize];
                Fix::new(
                    format!("declare `{root}` with `var`"),
                    vec![Edit::replace(keyword, "var")],
                )
            });
            self.found
                .push(declared.into_iter().fold(d, Diagnostic::with_fix));
            return None;
        }
        let aliases = &self.viewing.aliases;
        if let Some(q) = self.iterating.iter().find(|q| overlap(&p, q, aliases)) {
            let message = if q.root == p.root {
                format!("`{name}` is being read by a `for` loop around this change")
            } else {
                format!(
                    "`{name}` may reach the value of `{}`, which a `for` loop around this change \
                     reads",
                    q.name(self.locals)
                )
            };
            self.found
                .push(Diagnostic::new(codes::E0404, e.at, message));
        } else if let Some(d) = self.viewing.conflict(&p, e.at, true, self.locals) {
            self.found.push(d);
        }
        Some(p)
    }

    /// A read of the place `e` (modes.kinds-of-access), which no write through a view may be in
    /// progress on (projections.what-view-writes).
    fn read(&mut self, e: &Expr) {
        if let Some(p) = place(e)
            && let Some(d) = self.viewing.conflict(&p, e.at, false, self.locals)
        {
            self.found.push(d);
        }
    }

    /// Checks an expression and the code inside it, then starts the reads of the view it makes,
    /// if it makes one, until the end of its statement (views.reads-that-last).
    fn expr(&mut self, e: &'a Expr) {
        self.code(e);
        if let Some(s) = self.stmt {
            self.viewing.unbound(e, s.at.end());
        }
    }

    fn code(&mut self, e: &'a Expr) {
        match &e.kind {
            // A read of a projection's call holds its place for the read
            // (projections.when-projection-runs).
            ExprKind::Call(_, _, args, _) | ExprKind::Project(_, _, args, _) => {
                self.call(Some(e), args);
            }
            ExprKind::CallValue(f, args) => {
                self.expr(f);
                self.call(Some(e), args);
            }
            ExprKind::Closure(params, body) => {
                // A closure can't modify what it captures, only its `inout` parameters and the
                // `var` bindings it declares (modes.closures; expressions.capture and
                // expressions.inout-closure-parameters).
                let inner = closure_inouts(e, params)
                    .chain(expr_var_bindings(body))
                    .collect();
                let outer = std::mem::replace(&mut self.modifiable, inner);
                let lets = expr_let_bindings(body).into_iter().collect();
                let outer_lets = std::mem::replace(&mut self.lets, lets);
                self.expr(body);
                self.modifiable = outer;
                self.lets = outer_lets;
            }
            ExprKind::For(_, iterable, b) => match &**iterable {
                Iterable::Iter(source) => self.for_iter(source, b, e.at.end()),
                Iterable::Range(..) => self.parts(e),
            },
            _ if place(e).is_some() => {
                self.read(e);
                for x in place_parts(e) {
                    self.expr(x);
                }
            }
            _ => self.parts(e),
        }
    }

    /// A `for` loop over a place reads it while its body runs.
    fn for_iter(&mut self, source: &'a Expr, b: &'a Block, end: TextSize) {
        self.expr(source);
        let read = place(source);
        let reads = read.is_some();
        self.iterating.extend(read);
        self.block(b, end);
        if reads {
            self.iterating.pop();
        }
    }

    /// Checks the expressions and blocks directly inside an expression.
    fn parts(&mut self, e: &'a Expr) {
        for part in walk::parts(e) {
            match part {
                Part::Expr(x) => self.expr(x),
                Part::Block(b) => self.block(b, block_end(e)),
            }
        }
    }

    /// Arguments are evaluated first; the `inout` ones are modified from the start of the call,
    /// all together (modes.durations and modes.overlapping-inout). The view that the call `made`
    /// returns, if it returns one, reads the sources that each argument gives it from where the
    /// argument is evaluated (views.reads-that-last). The places modified.
    fn call(&mut self, made: Option<&Expr>, args: &'a [Arg]) -> Vec<Place> {
        for (i, a) in args.iter().enumerate() {
            if a.mode == Mode::Inout {
                for e in place_parts(&a.value) {
                    self.expr(e);
                }
            } else {
                self.expr(&a.value);
            }
            if let (Some(e), Some(s)) = (made, self.stmt) {
                self.viewing.operand(e, i, s.at.end());
            }
        }
        let mut modified: Vec<(Place, TextRange)> = Vec::new();
        for a in args.iter().filter(|a| a.mode == Mode::Inout) {
            let held = self.modify(&a.value);
            modified.extend(held.into_iter().map(|p| (p, a.value.at)));
        }
        for (i, (p, at)) in modified.iter().enumerate() {
            let aliases = &self.viewing.aliases;
            if let Some((q, _)) = modified[..i].iter().find(|(q, _)| overlap(p, q, aliases)) {
                let name = p.name(self.locals);
                let message = if q.root == p.root {
                    format!("`{name}` is already modified by this call")
                } else {
                    format!(
                        "`{name}` may reach the value of `{}`, which this call already modifies",
                        q.name(self.locals)
                    )
                };
                self.found.push(Diagnostic::new(codes::E0402, *at, message));
            }
        }
        modified.into_iter().map(|(p, _)| p).collect()
    }

    /// Checks a block's statements in order, which ends at `end`, where the reads of the views
    /// its statements bind end.
    fn block(&mut self, b: &'a Block, end: TextSize) {
        let depth = self.viewing.reads.len();
        for (i, s) in b.iter().enumerate() {
            let outer = self.stmt.replace(s);
            let mark = self.viewing.reads.len();
            self.stmt_code(s);
            self.viewing.reads.truncate(mark);
            self.viewing.bound(b, i, end);
            self.stmt = outer;
        }
        self.viewing.reads.truncate(depth);
    }

    fn stmt_code(&mut self, s: &'a Stmt) {
        match &s.kind {
            StmtKind::Assign(_, p, v) => {
                for e in place_parts(p) {
                    self.expr(e);
                }
                self.expr(v);
                self.modify(p);
            }
            // The place is handed to the caller, who may modify it (projections.yield).
            StmtKind::Yield(p) if place(p).is_some() || p.rooted_in_projection() => {
                for e in place_parts(p) {
                    self.expr(e);
                }
                self.modify(p);
            }
            StmtKind::Let(_)
            | StmtKind::Var(_)
            | StmtKind::Assert(_)
            | StmtKind::Yield(_)
            | StmtKind::Expr(_) => {
                for e in walk::stmt_exprs(s) {
                    self.expr(e);
                }
            }
        }
    }
}
