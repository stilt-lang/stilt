//! Own storage and last uses (facts.own-storage and facts.last-use), read lexically from a typed
//! body: which binding holds its own storage at a point, and where that storage comes from.

use std::collections::HashMap;

use stilt_hir::hir::LocalId;
use stilt_syntax::{TextRange, TextSize};

use crate::tast::walk::{Part, parts, stmt_exprs};
use crate::tast::{Block, Code, Expr, ExprKind, Iterable, PatKind, Stmt, StmtKind, TypedBody};

/// Where storage that a binding holds comes from: a parameter of the function, or a list
/// literal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Origin {
    Param(LocalId),
    Fresh,
}

/// How a binding is declared.
#[derive(Clone, Copy, Debug)]
enum Declared {
    /// A parameter, `let` or `inout`.
    Param,
    /// A `let` or `var` binding, at the start of its statement.
    Local(TextSize),
    /// A pattern of a `match`, an `if let`, a `for` or a `catch`, or a closure's parameter.
    Pattern,
}

/// What an assignment of a whole binding gives it.
#[derive(Clone, Copy, Debug)]
enum Given<'a> {
    /// The storage of a parameter, at its declaration, if a `without alloc` limits the function.
    Param,
    /// A value, unless a pattern takes it apart.
    Value(Option<&'a Expr>),
}

/// An assignment of a whole binding, its declaration among them.
#[derive(Clone, Copy, Debug)]
struct Assignment<'a> {
    /// Where it takes effect.
    took: TextSize,
    /// The end of the block it is a statement of, which holds every point from `took` to there.
    holds: TextSize,
    given: Given<'a>,
}

/// What the rule reads of a body.
pub(super) struct Storage<'a> {
    /// Whether a `without alloc` limits the function, so that its parameters hold their own
    /// storage.
    limited: bool,
    declared: HashMap<LocalId, Declared>,
    /// Each assignment of a whole binding, its declaration among them.
    assigned: HashMap<LocalId, Vec<Assignment<'a>>>,
    /// Each use of a binding, by where it is written and where it counts: at the closure
    /// literal it is in, if it is in one.
    uses: HashMap<LocalId, Vec<(TextRange, TextSize)>>,
    /// The loops of the body, each where its code runs again.
    loops: Vec<TextRange>,
}

impl<'a> Storage<'a> {
    /// What the rule reads of `body`, whose function `without alloc` limits or not.
    pub(super) fn of(body: &'a TypedBody, code: &'a Code, limited: bool) -> Self {
        let mut s = Self {
            limited,
            declared: HashMap::new(),
            assigned: HashMap::new(),
            uses: HashMap::new(),
            loops: Vec::new(),
        };
        let start = Assignment {
            took: TextSize::new(0),
            holds: TextSize::new(u32::MAX),
            given: Given::Param,
        };
        for &(_, v) in &body.params {
            s.declared.insert(v, Declared::Param);
            s.assigned.insert(v, vec![start]);
        }
        let mut closures = Vec::new();
        match code {
            Code::Block(b) => s.block(b, &mut closures),
            Code::Expr(e) => s.expr(e, &mut closures),
        }
        s
    }

    fn block(&mut self, b: &'a Block, closures: &mut Vec<TextRange>) {
        let holds = b.last().map_or(TextSize::new(0), |st| st.at.end());
        for st in b {
            self.stmt(st, holds);
            for e in stmt_exprs(st) {
                self.expr(e, closures);
            }
        }
    }

    fn assign(&mut self, v: LocalId, st: &Stmt, holds: TextSize, value: Option<&'a Expr>) {
        self.assigned.entry(v).or_default().push(Assignment {
            took: st.at.end(),
            holds,
            given: Given::Value(value),
        });
    }

    fn stmt(&mut self, st: &'a Stmt, holds: TextSize) {
        match &st.kind {
            StmtKind::Let(b) | StmtKind::Var(b) => {
                let whole = match b.pattern.kind {
                    PatKind::Bind(v) => Some(v),
                    _ => None,
                };
                for v in super::descent::bound(&b.pattern) {
                    self.declared.insert(v, Declared::Local(st.at.start()));
                    let value = (whole == Some(v)).then_some(&b.value);
                    self.assign(v, st, holds, value);
                }
            }
            StmtKind::Assign(None, place, value) => {
                if let ExprKind::Local(v) = place.kind {
                    self.assign(v, st, holds, Some(value));
                }
            }
            _ => {}
        }
    }

    fn expr(&mut self, e: &'a Expr, closures: &mut Vec<TextRange>) {
        closures.retain(|c| c.contains(e.at.start()));
        match &e.kind {
            ExprKind::Local(v) => {
                let counts = closures.first().map_or(e.at.start(), |c| c.start());
                self.uses.entry(*v).or_default().push((e.at, counts));
            }
            ExprKind::Closure(params, _) => {
                for v in params.iter().flat_map(super::descent::bound) {
                    self.declared.insert(v, Declared::Pattern);
                }
                closures.push(e.at);
            }
            ExprKind::Loop(_) | ExprKind::While(..) => self.loops.push(e.at),
            ExprKind::For(_, iterable, _) => {
                let from = match &**iterable {
                    Iterable::Iter(source) => source.at.end(),
                    Iterable::Range(_, to, _) => to.at.end(),
                };
                self.loops.push(TextRange::new(from, e.at.end()));
            }
            _ => {}
        }
        for part in parts(e) {
            match part {
                Part::Expr(x) => self.expr(x, closures),
                Part::Block(b) => self.block(b, closures),
            }
        }
    }

    /// Whether the use of `v` written at `at` is its last use: no use of it follows, and it
    /// isn't inside a loop that its declaration is outside of.
    pub(super) fn last_use(&self, v: LocalId, at: TextSize) -> bool {
        let Some(uses) = self.uses.get(&v) else {
            return false;
        };
        let Some(&(_, counts)) = uses.iter().find(|(written, _)| written.start() == at) else {
            return false;
        };
        let declared = match self.declared.get(&v) {
            Some(Declared::Local(d)) => Some(*d),
            _ => None,
        };
        let later = uses.iter().any(|&(w, c)| w.start() != at && c >= counts);
        let looped = self
            .loops
            .iter()
            .any(|l| l.contains(counts) && declared.is_none_or(|d| !l.contains(d)));
        !later && !looped
    }

    /// The first use of `v` after its use written at `at`, which keeps that use from being its
    /// last, if one does: a use written later, or inside a closure literal that counts later.
    pub(super) fn later_use(&self, v: LocalId, at: TextSize) -> Option<TextRange> {
        let uses = self.uses.get(&v)?;
        let &(_, counts) = uses.iter().find(|(written, _)| written.start() == at)?;
        uses.iter()
            .filter(|&&(w, c)| w.start() != at && c >= counts)
            .map(|&(w, _)| w)
            .min_by_key(|w| w.start())
    }

    /// Where the storage that `v` holds at `at` comes from, if `v` holds its own storage there:
    /// what each of its assignments before `at` gives it.
    pub(super) fn own(&self, v: LocalId, at: TextSize) -> Option<Vec<Origin>> {
        if matches!(self.declared.get(&v)?, Declared::Pattern) {
            return None;
        }
        let mut origins = Vec::new();
        for a in self.before(v, at)? {
            let given = match a.given {
                Given::Param => self.limited.then_some(vec![Origin::Param(v)]),
                Given::Value(value) => self.given(value?),
            };
            origins.extend(given?);
        }
        Some(origins)
    }

    /// The assignments of `v` before `at`: the last one before it that is a statement of a block
    /// holding it, each one after that and before `at`, and when `at` is inside a loop that the
    /// last one is outside of, each one inside the loop.
    fn before(&self, v: LocalId, at: TextSize) -> Option<Vec<&Assignment<'a>>> {
        let all = self.assigned.get(&v)?;
        let last = all
            .iter()
            .filter(|a| a.took <= at && at <= a.holds)
            .max_by_key(|a| a.took)?;
        let looped: Vec<TextRange> = self
            .loops
            .iter()
            .filter(|l| l.contains(at) && !l.contains(last.took))
            .copied()
            .collect();
        let before = all.iter().filter(|a| {
            (last.took <= a.took && a.took <= at) || looped.iter().any(|l| l.contains(a.took))
        });
        Some(before.collect())
    }

    /// The origins of the storage that an assignment of `value` gives: a list literal's, or those
    /// of a binding it names whole at its last use, which holds its own storage there.
    pub(super) fn given(&self, value: &Expr) -> Option<Vec<Origin>> {
        match &value.kind {
            ExprKind::List(_) => Some(vec![Origin::Fresh]),
            ExprKind::Local(x) if self.last_use(*x, value.at.start()) => {
                self.own(*x, value.at.start())
            }
            _ => None,
        }
    }
}
