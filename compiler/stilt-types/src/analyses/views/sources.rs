//! The sources of views (views.making-view, views.across-calls and views.fixed), found lexically,
//! in source order, and which of them a view writes (projections.what-view-writes and
//! projections.places-through-views). A view made by `View.of` or `View.all` has as source its
//! argument when it is a place, its variable followed by its projections, and otherwise a temporary
//! that nothing else names; any other call that gives a view type has the sources of each argument
//! whose type is viewable or a view type, since the callee could view any of them, and writes each
//! such argument passed `inout`; a binding has the sources of the value it is bound to, a `var`
//! those of every value assigned to it; a view parameter, and a writable binding, has itself as
//! source; and a closure literal has the sources of the views it captures.

use std::collections::{HashMap, HashSet};

use stilt_hir::hir::{LocalId, Mode};
use stilt_syntax::TextRange;

use super::super::modes::places::{Place, place};
use crate::tast::walk::{self, Part};
use crate::tast::{Block, Callee, Expr, ExprKind, Pat, PatKind, StmtKind, TypedBody};
use crate::ty::{Ty, is_prelude, is_view_type};

/// What a view reads: a place (modes.places), or a temporary that lasts as long as the view,
/// made by the expression at a position (views.making-view); or what it writes, a place it was made
/// from through `inout` (projections.what-view-writes).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Source {
    Place(Place),
    Written(Place),
    Temporary(TextRange),
}

impl Source {
    /// The place, of a source that is one.
    pub(crate) fn place(&self) -> Option<&Place> {
        match self {
            Source::Place(p) | Source::Written(p) => Some(p),
            Source::Temporary(_) => None,
        }
    }

    /// Whether a view reads the source, a place it views or a temporary, as against a place
    /// it writes (projections.what-view-writes).
    pub(crate) fn reads(&self) -> bool {
        !matches!(self, Source::Written(_))
    }
}

/// The sources of a function's views, and what it needs to tell them.
pub(crate) struct Sources {
    /// The type of each local that the body uses or binds.
    types: HashMap<LocalId, Ty>,
    /// The sources of each binding of a view type, and of a closure that captures one.
    bound: HashMap<LocalId, Vec<Source>>,
    /// The `var` bindings of `View<T>`, which are writable: sources in their own right
    /// (projections.writable-bindings and projections.places-through-views).
    writable: HashSet<LocalId>,
    /// The locals each closure literal binds itself, by where it is.
    inner: HashMap<stilt_syntax::TextSize, HashSet<LocalId>>,
    /// Where each binding with sources is bound: its pattern.
    at: HashMap<LocalId, TextRange>,
    /// The function's parameters, with their modes.
    params: Vec<(Mode, LocalId)>,
}

/// Adds the sources of `more` that `to` doesn't hold.
fn join(to: &mut Vec<Source>, more: Vec<Source>) {
    for p in more {
        if !to.contains(&p) {
            to.push(p);
        }
    }
}

/// The variables a pattern binds.
pub(crate) fn bound_by(p: &Pat, out: &mut Vec<LocalId>) {
    match &p.kind {
        PatKind::Bind(v) => out.push(*v),
        PatKind::Tuple(ps) | PatKind::Variant(_, ps) | PatKind::Or(ps) => {
            for p in ps {
                bound_by(p, out);
            }
        }
        PatKind::List(ps, rest) => {
            if let stilt_hir::hir::ListRest::Bind(v) = rest {
                out.push(*v);
            }
            for p in ps {
                bound_by(p, out);
            }
        }
        PatKind::Record(fields) => fields.iter().for_each(|(_, p)| bound_by(p, out)),
        _ => {}
    }
}

/// Where a pattern binds the variable `v`: the binding itself, or the pattern if it isn't found.
fn pattern_at(p: &Pat, v: LocalId) -> TextRange {
    fn find(p: &Pat, v: LocalId) -> Option<TextRange> {
        match &p.kind {
            PatKind::Bind(w) if *w == v => Some(p.at),
            PatKind::Tuple(ps)
            | PatKind::Variant(_, ps)
            | PatKind::Or(ps)
            | PatKind::List(ps, _) => ps.iter().find_map(|p| find(p, v)),
            PatKind::Record(fields) => fields.iter().find_map(|(_, p)| find(p, v)),
            _ => None,
        }
    }
    find(p, v).unwrap_or(p.at)
}

/// Records the type of each variable a pattern binds.
fn pattern_types(p: &Pat, types: &mut HashMap<LocalId, Ty>) {
    if let PatKind::Bind(v) = &p.kind {
        types.insert(*v, p.ty.clone());
    }
    let mut inner = Vec::new();
    match &p.kind {
        PatKind::Tuple(ps) | PatKind::Variant(_, ps) | PatKind::Or(ps) | PatKind::List(ps, _) => {
            inner.extend(ps);
        }
        PatKind::Record(fields) => inner.extend(fields.iter().map(|(_, p)| p)),
        _ => {}
    }
    for p in inner {
        pattern_types(p, types);
    }
}

impl Sources {
    /// The sources of a function body's views.
    pub(crate) fn of(body: &TypedBody, block: &Block) -> Self {
        let mut s = Self {
            types: HashMap::new(),
            bound: HashMap::new(),
            writable: HashSet::new(),
            inner: HashMap::new(),
            at: HashMap::new(),
            params: body.params.clone(),
        };
        let mut stmt = |st: &crate::tast::Stmt| {
            if let StmtKind::Let(b) | StmtKind::Var(b) = &st.kind {
                pattern_types(&b.pattern, &mut s.types);
            }
        };
        let mut types = HashMap::new();
        walk::iter_block(block, &mut stmt, &mut |e| record_types(e, &mut types));
        s.types.extend(types);
        for &(_, p) in &body.params {
            if s.types.get(&p).is_some_and(Ty::is_view) {
                s.bound.insert(
                    p,
                    vec![Source::Place(Place {
                        root: p,
                        path: Vec::new(),
                    })],
                );
            }
        }
        s.block(block);
        s
    }

    /// Whether a source is a parameter that a view in the result may have: a `let` parameter of
    /// viewable type, or a view parameter, which it reads (views.across-calls and views.escaping),
    /// or an `inout` parameter, which it writes (projections.results-that-write).
    pub(crate) fn allowed(&self, source: &Source) -> bool {
        match source {
            Source::Place(p) => self.params.iter().any(|&(mode, v)| {
                v == p.root
                    && mode == Mode::Let
                    && self
                        .types
                        .get(&v)
                        .is_some_and(|t| t.is_viewable() || t.is_view())
            }),
            Source::Written(p) => self.params.contains(&(Mode::Inout, p.root)),
            Source::Temporary(_) => false,
        }
    }

    /// Whether a source reads the `inout` parameter `p`, which a result may only write
    /// (projections.results-that-write).
    pub(crate) fn reads_inout(&self, source: &Source) -> bool {
        match source {
            Source::Place(p) => self.params.contains(&(Mode::Inout, p.root)),
            Source::Written(_) | Source::Temporary(_) => false,
        }
    }

    /// The sources of a binding of a view type or of a closure that captures one.
    pub(crate) fn of_binding(&self, v: LocalId) -> Option<&[Source]> {
        self.bound.get(&v).map(Vec::as_slice)
    }

    /// Whether a binding is writable: a `var` binding of `View<T>` (projections.writable-bindings).
    pub(crate) fn is_writable(&self, v: LocalId) -> bool {
        self.writable.contains(&v)
    }

    /// Where a binding with sources is bound, if the body binds it.
    pub(crate) fn binding_at(&self, v: LocalId) -> Option<TextRange> {
        self.at.get(&v).copied()
    }

    /// The bindings with sources, each with where it is bound, in no order.
    pub(crate) fn bindings(&self) -> impl Iterator<Item = (LocalId, TextRange)> + '_ {
        self.at.iter().map(|(&v, &at)| (v, at))
    }

    /// Records the sources of the bindings of a block's statements, in order.
    fn block(&mut self, b: &Block) {
        for st in b {
            for e in walk::stmt_exprs(st) {
                self.expr(e);
            }
            match &st.kind {
                StmtKind::Let(binding) | StmtKind::Var(binding) => {
                    let found = self.sources(&binding.value);
                    let var = matches!(st.kind, StmtKind::Var(_));
                    self.bind(&binding.pattern, &found, var);
                }
                StmtKind::Assign(None, target, value) => {
                    if let ExprKind::Local(v) = target.kind
                        && self.bound.contains_key(&v)
                    {
                        let found = self.sources(value);
                        join(self.bound.entry(v).or_default(), found);
                    }
                }
                _ => {}
            }
        }
    }

    /// Gives each variable that a pattern binds to part of a value with sources `found` those
    /// sources, if it holds a view or a closure; a `var` binding of `View<T>` is writable
    /// (projections.writable-bindings).
    fn bind(&mut self, p: &Pat, found: &[Source], var: bool) {
        let mut vars = Vec::new();
        bound_by(p, &mut vars);
        for v in vars {
            let ty = self.types.get(&v);
            let holds = ty.is_some_and(|t| t.is_view() || matches!(t, Ty::Fn(_)));
            if holds && (!found.is_empty() || ty.is_some_and(Ty::is_view)) {
                join(self.bound.entry(v).or_default(), found.to_vec());
                self.at.entry(v).or_insert(pattern_at(p, v));
                if var && ty.is_some_and(Ty::is_window) {
                    self.writable.insert(v);
                }
            }
        }
    }

    /// Records the sources of the bindings inside an expression: those of its blocks, of its
    /// closures, of its arms' patterns and of a `for` over views.
    fn expr(&mut self, e: &Expr) {
        if matches!(e.kind, ExprKind::Closure(..)) {
            self.inner.insert(e.at.start(), declared_in(e));
        }
        match &e.kind {
            ExprKind::Match(scrutinee, arms) => {
                self.expr(scrutinee);
                let found = self.sources(scrutinee);
                for arm in arms {
                    self.bind(&arm.pattern, &found, false);
                    arm.guard.iter().for_each(|g| self.expr(g));
                    self.expr(&arm.body);
                }
            }
            ExprKind::IfLet(p, scrutinee, b, alt) => {
                self.expr(scrutinee);
                let found = self.sources(scrutinee);
                self.bind(p, &found, false);
                self.block(b);
                if let Some(a) = alt {
                    self.expr(a);
                }
            }
            ExprKind::For(p, iterable, b) => {
                if let crate::tast::Iterable::Iter(it) = &**iterable {
                    self.expr(it);
                    let found = self.sources(it);
                    self.bind(p, &found, false);
                }
                self.block(b);
            }
            _ => self.parts(e),
        }
    }

    fn parts(&mut self, e: &Expr) {
        for part in walk::parts(e) {
            match part {
                Part::Expr(e) => self.expr(e),
                Part::Block(b) => self.block(b),
            }
        }
    }
}

/// The variables that the patterns inside an expression bind: a closure's parameters, and those
/// of its statements, arms and loops, and the names of its `when`s.
pub(crate) fn declared_in(e: &Expr) -> HashSet<LocalId> {
    let mut found = Vec::new();
    let mut patterns: Vec<&Pat> = Vec::new();
    let mut held = Vec::new();
    walk::iter(
        e,
        &mut |st| {
            if let StmtKind::Let(b) | StmtKind::Var(b) = &st.kind {
                bound_by(&b.pattern, &mut found);
            }
        },
        &mut |x| match &x.kind {
            ExprKind::Closure(ps, _) => patterns.extend(ps),
            ExprKind::Match(_, arms) => patterns.extend(arms.iter().map(|a| &a.pattern)),
            ExprKind::IfLet(p, ..) | ExprKind::For(p, ..) => patterns.push(p),
            // shared.when: a `when` binds its names in its block.
            ExprKind::When(names, _) => held.extend(names.iter().map(|(_, place)| *place)),
            _ => {}
        },
    );
    found.extend(held);
    for p in patterns {
        bound_by(p, &mut found);
    }
    found.into_iter().collect()
}

/// Records the type of each local that an expression inside `e` uses.
fn record_types(e: &Expr, types: &mut HashMap<LocalId, Ty>) {
    match &e.kind {
        ExprKind::Local(v) => {
            types.entry(*v).or_insert_with(|| e.ty.clone());
        }
        ExprKind::Closure(params, _) => {
            for p in params {
                pattern_types(p, types);
            }
        }
        ExprKind::Match(_, arms) => arms.iter().for_each(|a| pattern_types(&a.pattern, types)),
        ExprKind::IfLet(p, ..) | ExprKind::For(p, ..) => pattern_types(p, types),
        _ => {}
    }
}

/// Whether a callee is `View.of` or `View.all`, which view their first argument
/// (views.making-view).
fn makes_view(callee: &Callee) -> bool {
    matches!(callee, Callee::Member(owner, name)
        if is_view_type(owner, "View") && matches!(&**name, "of" | "all"))
}

impl Sources {
    /// The places among the sources of the value of an expression.
    pub(crate) fn places(&self, e: &Expr) -> Vec<Place> {
        self.sources(e)
            .iter()
            .filter_map(|s| s.place().cloned())
            .collect()
    }

    /// The places among the sources that the argument `index` of the call `e` gives its result,
    /// when the result is a view and the argument is passed `let`, which the view reads from
    /// where the argument is evaluated (views.reads-that-last).
    pub(crate) fn operand(&self, e: &Expr, index: usize) -> Vec<Place> {
        let (makes, args) = match &e.kind {
            ExprKind::Call(callee, _, args, _) | ExprKind::Project(callee, _, args, _) => {
                (makes_view(callee), args)
            }
            ExprKind::CallValue(_, args) => (false, args),
            _ => return Vec::new(),
        };
        match args.get(index) {
            Some(a) if e.ty.is_view() && a.mode == Mode::Let => self
                .argument(a.mode, &a.value, makes && index == 0)
                .iter()
                .filter_map(|s| s.place().cloned())
                .collect(),
            _ => Vec::new(),
        }
    }

    /// The sources of the value of an expression (views.making-view, views.across-calls and
    /// views.fixed; projections.what-view-writes and projections.places-through-views).
    pub(crate) fn sources(&self, e: &Expr) -> Vec<Source> {
        let mut found = Vec::new();
        match &e.kind {
            // projections.places-through-views: a writable binding is a source in its own right, as
            // a view parameter is.
            ExprKind::Local(v) if self.writable.contains(v) => {
                found.push(Source::Place(Place {
                    root: *v,
                    path: Vec::new(),
                }));
            }
            ExprKind::Local(v) => join(&mut found, self.bound.get(v).cloned().unwrap_or_default()),
            ExprKind::Call(callee, _, args, _) | ExprKind::Project(callee, _, args, _)
                if e.ty.is_view() =>
            {
                let makes = makes_view(callee);
                for (i, a) in args.iter().enumerate() {
                    join(&mut found, self.argument(a.mode, &a.value, makes && i == 0));
                }
            }
            ExprKind::CallValue(f, args) if e.ty.is_view() => {
                join(&mut found, self.sources(f));
                for a in args {
                    join(&mut found, self.argument(a.mode, &a.value, false));
                }
            }
            ExprKind::Construct(item, _, es) if is_prelude(item, "Some") => {
                for x in es {
                    join(&mut found, self.sources(x));
                }
            }
            ExprKind::Closure(..) => join(&mut found, self.captured(e)),
            ExprKind::Block(b) => join(&mut found, self.tail(b)),
            ExprKind::If(_, b, alt) | ExprKind::IfLet(_, _, b, alt) => {
                join(&mut found, self.tail(b));
                if let Some(a) = alt {
                    join(&mut found, self.sources(a));
                }
            }
            ExprKind::Match(_, arms) => {
                for a in arms {
                    join(&mut found, self.sources(&a.body));
                }
            }
            ExprKind::Else(a, b) => {
                join(&mut found, self.sources(a));
                join(&mut found, self.sources(b));
            }
            ExprKind::Try(operand, catch) => {
                join(&mut found, self.sources(operand));
                for a in walk::catch_arms(catch.as_ref()) {
                    join(&mut found, self.sources(&a.body));
                }
            }
            _ => {}
        }
        found
    }

    /// The sources that an argument gives the result of a call that gives a view type
    /// (views.across-calls; projections.what-view-writes): the place it is, written when it is
    /// passed `inout` and its type is viewable or a view type, and read when it is viewable, or a
    /// map that `of_map` reads, or `makes` a view of it; a temporary for a viewable value that is
    /// no place, a projection's call passed `inout` among them; and the sources of a view or a
    /// closure.
    fn argument(&self, mode: Mode, a: &Expr, makes: bool) -> Vec<Source> {
        let viewable = makes || a.ty.is_viewable() || a.ty.is_prelude("Map");
        match (mode, place(a)) {
            (Mode::Inout, Some(p)) if viewable || a.ty.is_view() => vec![Source::Written(p)],
            (Mode::Inout, None) if a.ty != Ty::Error => vec![Source::Temporary(a.at)],
            (Mode::Let, Some(p)) if viewable && a.ty != Ty::Error => vec![Source::Place(p)],
            (Mode::Let, None) if viewable && a.ty != Ty::Error => vec![Source::Temporary(a.at)],
            _ if a.ty.is_view() || matches!(a.ty, Ty::Fn(_)) => self.sources(a),
            _ => Vec::new(),
        }
    }

    /// The sources of a block's value, its last statement's.
    fn tail(&self, b: &Block) -> Vec<Source> {
        match b.last().map(|s| &s.kind) {
            Some(StmtKind::Expr(e)) => self.sources(e),
            _ => Vec::new(),
        }
    }

    /// The sources of the views that a closure literal captures (views.fixed).
    pub(crate) fn captured(&self, closure: &Expr) -> Vec<Source> {
        let ExprKind::Closure(_, body) = &closure.kind else {
            return Vec::new();
        };
        let inner = self.inner.get(&closure.at.start());
        let mut found = Vec::new();
        walk::iter(body, &mut |_| {}, &mut |x| {
            if let ExprKind::Local(v) = x.kind
                && !inner.is_some_and(|i| i.contains(&v))
            {
                join(&mut found, self.sources(x));
            }
        });
        found
    }
}
