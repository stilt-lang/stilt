//! Views that outlive their sources (views.escaping; modes.escaping): a view leaves a function
//! only through its result, and only when every source it has is a `let` parameter of viewable type
//! or a view parameter, which it reads, or an `inout` parameter, which it writes
//! (projections.results-that-write). Any other way out is E0422, at the expression that leaves,
//! naming the source: a result that views a local, a view raised or assigned into a place that
//! outlives it, and a closure that captures a view and leaves the function, in its result, raised,
//! or passed to an `escaping` parameter; a result that reads an `inout` parameter is E0428 instead.
//! A closure's own body may give back what it captures, which only matters if the closure leaves.

use stilt_diag::{Diagnostic, codes};
use stilt_hir::hir::{LocalId, Mode, Name};

use super::super::signature::SigInfo;
use super::Sources;
use super::sources::{self, Source};
use crate::tast::walk::{self, Part};
use crate::tast::{Block, Expr, ExprKind, Pat, StmtKind, TypedBody};
use crate::ty::Ty;

/// How a view leaves the function.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Way {
    Returned,
    Raised,
    Assigned,
    Passed,
}

struct Escapes<'a> {
    found: &'a Sources,
    locals: &'a [Name],
    params: &'a [(Mode, LocalId)],
    raise_broken: bool,
    errors: Vec<Diagnostic>,
}

/// The errors of views.escaping in a function's body.
pub(super) fn errors(
    sig: &SigInfo<'_>,
    body: &TypedBody,
    block: &Block,
    found: &Sources,
) -> Vec<Diagnostic> {
    let mut e = Escapes {
        found,
        locals: &body.locals,
        params: &body.params,
        raise_broken: sig.raise_broken,
        errors: Vec::new(),
    };
    e.block(block, true);
    e.errors
}

impl Escapes<'_> {
    /// Checks a block's statements, the last one's value leaving as the function's result if
    /// `result`. A view yielded must write its sources instead (projections.writable-bindings;
    /// `writes`).
    fn block(&mut self, b: &Block, result: bool) {
        for (i, s) in b.iter().enumerate() {
            for e in walk::stmt_exprs(s) {
                self.expr(e);
            }
            match &s.kind {
                StmtKind::Expr(e) if result && i + 1 == b.len() => self.leaves(e, Way::Returned),
                StmtKind::Assign(_, target, value) if !self.whole_local(target) => {
                    self.leaves(value, Way::Assigned);
                }
                _ => {}
            }
        }
    }

    /// Whether an assignment's target is the whole of a local of the function, other than an
    /// `inout` parameter, which a view may be copied into.
    fn whole_local(&self, target: &Expr) -> bool {
        match target.kind {
            ExprKind::Local(v) => !self.params.contains(&(Mode::Inout, v)),
            _ => false,
        }
    }

    /// Checks the code inside an expression, outside the closures in it, whose own results and
    /// raises are theirs.
    fn expr(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Return(Some(v)) => self.leaves(v, Way::Returned),
            ExprKind::Raise(v) if !self.raise_broken => self.leaves(v, Way::Raised),
            // shared.tasks-and-modes, and par.what-runs-in-parallel: a demand on the thread axes
            // reports an argument that it checks (E0431, E0432).
            ExprKind::Call(callee, _, args, _) | ExprKind::Project(callee, _, args, _) => {
                for (_, a) in args
                    .iter()
                    .enumerate()
                    .filter(|(i, a)| a.kept && !super::super::demands::demanded(callee, *i))
                {
                    if matches!(a.value.kind, ExprKind::Closure(..) | ExprKind::Local(_)) {
                        self.leaves(&a.value, Way::Passed);
                    }
                }
            }
            ExprKind::Closure(params, body) => return self.closure_results(e, params, body),
            _ => {}
        }
        for part in walk::parts(e) {
            match part {
                Part::Expr(x) => self.expr(x),
                Part::Block(b) => self.block(b, false),
            }
        }
    }

    /// Checks a value that leaves the function in the way `way`: in its result, a view may
    /// keep sources that are allowed parameters, and nothing else may keep any.
    fn leaves(&mut self, e: &Expr, way: Way) {
        let mut ends = Vec::new();
        ends_of(e, &mut ends);
        for x in ends {
            self.leaf(x, way);
        }
    }

    /// The results of a closure literal, and of the closures inside it (views.escaping): a
    /// closure is a function of its own, so its results may view what it captures and its `let`
    /// parameters, and nothing it binds itself or makes for a statement, as the function's
    /// results may view only its parameters. E0422 at each result that views one.
    fn closure_results(&mut self, closure: &Expr, params: &[Pat], body: &Expr) {
        let mut own = sources::declared_in(body);
        if let Ty::Fn(f) = &closure.ty {
            for (p, (mode, _)) in params.iter().zip(&f.params) {
                if *mode == Mode::Inout {
                    let mut ids = Vec::new();
                    sources::bound_by(p, &mut ids);
                    own.extend(ids);
                }
            }
        }
        let mut ends = Vec::new();
        ends_of(body, &mut ends);
        returned_in(body, &mut ends);
        for e in ends {
            let bad = self.found.sources(e).into_iter().find(|s| match s.place() {
                Some(p) => own.contains(&p.root),
                None => true,
            });
            if let Some(source) = bad {
                self.closure_leaf(e, &source);
            }
        }
        for_closures_in(body, &mut |c, ps, b| self.closure_results(c, ps, b));
    }

    /// E0422 at a closure's result `e`, which views `source`, which the closure can't give back.
    fn closure_leaf(&mut self, e: &Expr, source: &Source) {
        let (name, kind) = match source {
            Source::Temporary(_) => self.describe(source),
            Source::Place(p) | Source::Written(p) => (
                format!("`{}`", p.name(self.locals)),
                "which the closure binds itself",
            ),
        };
        let what = if matches!(e.ty, Ty::Fn(_)) {
            "this closure"
        } else {
            "this view"
        };
        let message = format!("{what} is a closure's result, but it views {name}, {kind}");
        let mut d = Diagnostic::new(codes::E0422, e.at, message);
        if let Source::Temporary(at) = source {
            d = d.with_note(*at, "the value is made here, for this statement alone");
        }
        self.errors.push(d);
    }

    /// E0422 at a value that leaves the function with a source it can't keep there, or E0428 at a
    /// result that reads an `inout` parameter, which it may only write
    /// (projections.results-that-write).
    fn leaf(&mut self, e: &Expr, way: Way) {
        let sources = self.found.sources(e);
        let closure = matches!(e.ty, Ty::Fn(_));
        let bad = if closure || way != Way::Returned {
            sources.first()
        } else {
            sources.iter().find(|s| !self.found.allowed(s))
        };
        let Some(source) = bad else {
            return;
        };
        if way == Way::Returned && !closure && self.found.reads_inout(source) {
            self.errors.push(self.reads_inout(e, source));
            return;
        }
        let (name, kind) = self.describe(source);
        let message = Self::message(&name, kind, closure, way);
        let mut d = Diagnostic::new(codes::E0422, e.at, message);
        if let ExprKind::Local(v) = e.kind
            && let Some(at) = self.found.binding_at(v)
        {
            let held = &self.locals[v.0 as usize];
            d = d.with_note(at, format!("`{held}` views {name} from here"));
        } else if let Source::Temporary(at) = source {
            d = d.with_note(*at, "the value is made here, for this statement alone");
        }
        self.errors.push(d);
    }

    /// E0428 at a result that reads the `inout` parameter `source`, with the fix the rule
    /// names: make the view through `inout`.
    fn reads_inout(&self, e: &Expr, source: &Source) -> Diagnostic {
        let (name, _) = self.describe(source);
        let bare = name.trim_matches('`');
        let message = format!(
            "this view reads {name}, which the result must write: make it with \
             `view.into(inout {bare}, …)`"
        );
        Diagnostic::new(codes::E0428, e.at, message)
    }

    /// A source as a message names it, with what it is: a parameter, `inout` or not, a local,
    /// or a temporary.
    fn describe(&self, source: &Source) -> (String, &'static str) {
        match source {
            Source::Place(p) | Source::Written(p) => {
                let name = format!("`{}`", p.name(self.locals));
                let kind = if self.params.contains(&(Mode::Inout, p.root)) {
                    "an `inout` parameter, which goes back to the caller"
                } else if self.params.iter().any(|&(_, v)| v == p.root) {
                    "a parameter"
                } else {
                    "a local of this function"
                };
                (name, kind)
            }
            Source::Temporary(_) => (
                "a value made in this statement".to_owned(),
                "which lasts only as long as the statement",
            ),
        }
    }

    /// The message of E0422: the value, how it leaves, and the source it can't keep.
    fn message(name: &str, kind: &str, closure: bool, way: Way) -> String {
        let what = if closure { "this closure" } else { "this view" };
        let how = match way {
            Way::Returned => "is returned",
            Way::Raised => "is raised",
            Way::Assigned => "is stored where it outlives its source",
            Way::Passed => "is kept by the function it is passed to",
        };
        format!("{what} {how}, but it views {name}, {kind}")
    }
}

/// The expressions whose values are `e`'s, through its blocks' last statements and its
/// branches.
fn ends_of<'e>(e: &'e Expr, out: &mut Vec<&'e Expr>) {
    let tail = |b: &'e Block, out: &mut Vec<&'e Expr>| {
        if let Some(StmtKind::Expr(x)) = b.last().map(|s| &s.kind) {
            ends_of(x, out);
        }
    };
    match &e.kind {
        ExprKind::Block(b) => tail(b, out),
        ExprKind::If(_, b, alt) | ExprKind::IfLet(_, _, b, alt) => {
            tail(b, out);
            if let Some(a) = alt {
                ends_of(a, out);
            }
        }
        ExprKind::Match(_, arms) => arms.iter().for_each(|a| ends_of(&a.body, out)),
        ExprKind::Else(a, b) => {
            ends_of(a, out);
            ends_of(b, out);
        }
        _ => out.push(e),
    }
}

/// The values that `return` gives in `e`, outside the closures in it, through their branches.
fn returned_in<'e>(e: &'e Expr, out: &mut Vec<&'e Expr>) {
    match &e.kind {
        ExprKind::Return(Some(v)) => ends_of(v, out),
        ExprKind::Closure(..) => return,
        _ => {}
    }
    for part in walk::parts(e) {
        match part {
            Part::Expr(x) => returned_in(x, out),
            Part::Block(b) => {
                for s in b {
                    for x in walk::stmt_exprs(s) {
                        returned_in(x, out);
                    }
                }
            }
        }
    }
}

/// Calls `f` on each closure literal in `e`, outside the closures in it.
fn for_closures_in<'e>(e: &'e Expr, f: &mut dyn FnMut(&'e Expr, &'e [Pat], &'e Expr)) {
    if let ExprKind::Closure(ps, b) = &e.kind {
        return f(e, ps, b);
    }
    for part in walk::parts(e) {
        match part {
            Part::Expr(x) => for_closures_in(x, f),
            Part::Block(b) => {
                for s in b {
                    for x in walk::stmt_exprs(s) {
                        for_closures_in(x, f);
                    }
                }
            }
        }
    }
}
