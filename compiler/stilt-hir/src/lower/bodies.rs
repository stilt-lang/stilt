//! Bodies, each with locals of its own: those of functions, constants, tests and doc
//! examples (program.doc-examples).

use std::collections::{HashMap, HashSet};

use stilt_diag::Diagnostic;
use stilt_syntax::TextRange;
use stilt_syntax::ast::{self, AstNode};

use super::{Ctx, Resolver};
use crate::hir::{Body, BodyIndex, BodyValue, Local, LocalId, Name, rebase};

/// The locals of the code around a body, and those in scope there.
pub(super) struct Frame {
    locals: Vec<Local>,
    scope: Vec<(Name, Option<LocalId>)>,
}

impl Resolver<'_> {
    /// Starts a body with locals of its own, and returns the state of the code around it.
    pub(super) fn enter_body(&mut self) -> Frame {
        Frame {
            locals: std::mem::take(&mut self.locals),
            scope: std::mem::take(&mut self.scope),
        }
    }

    /// Ends a body, and returns its locals.
    pub(super) fn leave_body(&mut self, frame: Frame) -> Vec<Local> {
        self.scope = frame.scope;
        std::mem::replace(&mut self.locals, frame.locals)
    }

    /// Resolves the code of a body with `resolve`, keeping one E0211 for each name that doesn't
    /// resolve in it, at the place where that name starts first (errors.unknown-names). For a name
    /// that a pattern of the body also writes without a module, only type checking knows where
    /// that is, so its E0211 is returned to be held in the body, with its name. The errors of
    /// its analyses found where it writes types are returned too.
    pub(super) fn body_code<T>(
        &mut self,
        resolve: impl FnOnce(&mut Self) -> T,
    ) -> (T, Vec<(Name, Diagnostic)>, Vec<Diagnostic>) {
        let outer = self.unknown.replace(Vec::new());
        let outer_analysed = std::mem::take(&mut self.analysed);
        // The expansions of a body are numbered from 1 (macros.showing).
        let outer_marks = std::mem::replace(&mut self.marks, 0);
        let value = resolve(self);
        self.marks = outer_marks;
        let analysed = std::mem::replace(&mut self.analysed, outer_analysed);
        let found = std::mem::replace(&mut self.unknown, outer).unwrap_or_default();
        let mut first: HashMap<&str, usize> = HashMap::new();
        for (name, i) in &found {
            let Some(i) = *i else { continue };
            let start = |j: usize| self.diagnostics[j].range.start();
            first
                .entry(name)
                .and_modify(|kept| {
                    if start(i) < start(*kept) {
                        *kept = i;
                    }
                })
                .or_insert(i);
        }
        let deferred = |name: &str| found.iter().any(|(n, i)| n == name && i.is_none());
        let held_at: HashMap<usize, Name> = first
            .iter()
            .filter(|(name, _)| deferred(name))
            .map(|(name, &i)| (i, Name::from(*name)))
            .collect();
        let kept: HashSet<usize> = first.values().copied().collect();
        let reported: HashSet<usize> = found.iter().filter_map(|&(_, i)| i).collect();
        let mut held = Vec::new();
        let diagnostics = std::mem::take(&mut self.diagnostics);
        for (i, d) in diagnostics.into_iter().enumerate() {
            if let Some(name) = held_at.get(&i) {
                held.push((*name, d));
            } else if kept.contains(&i) || !reported.contains(&i) {
                self.diagnostics.push(d);
            }
        }
        (value, held, analysed)
    }

    /// Reports E0211 for `name`, a path as written up to the name in it that doesn't resolve.
    pub(super) fn unknown_name(&mut self, name: String, d: Diagnostic) {
        if let Some(found) = &mut self.unknown {
            found.push((name, Some(self.diagnostics.len())));
        }
        self.diagnostics.push(d);
    }

    /// Records, inside a body, that a pattern writes `name` without a module where it means
    /// nothing in scope, which type checking reports unless the type matched there has a
    /// variant of that name (patterns.unknown-variants).
    pub(super) fn deferred_name(&mut self, name: &str) {
        if let Some(found) = &mut self.unknown {
            found.push((name.to_owned(), None));
        }
    }

    /// Adds a body, whose positions become relative to its start.
    pub(super) fn add_body(&mut self, mut body: Body) -> BodyIndex {
        let index = BodyIndex(u32::try_from(self.bodies.len()).expect("under 4G bodies"));
        let start = body.at.start();
        body.expansions = std::mem::take(&mut self.expansions);
        body.unsafe_blocks = std::mem::take(&mut self.unsafe_blocks);
        rebase(&mut body, start);
        self.bodies.push(body);
        self.body_starts.push(start);
        index
    }

    /// Resolves a body without parameters, reported as a whole at `at`, which records whether
    /// resolving it reported an error.
    pub(super) fn body(
        &mut self,
        at: TextRange,
        resolve: impl FnOnce(&mut Self) -> BodyValue,
    ) -> BodyIndex {
        let frame = self.enter_body();
        let before = self.diagnostics.len();
        let (value, held, analysed) = self.body_code(resolve);
        let has_errors = self.diagnostics.len() > before || !held.is_empty();
        let locals = self.leave_body(frame);
        self.add_body(Body {
            locals,
            params: Vec::new(),
            value,
            at,
            has_errors,
            signature: None,
            limits: Vec::new(),
            held,
            analysed,
            fixed: Vec::new(),
            expansions: Vec::new(),
            unsafe_blocks: Vec::new(),
        })
    }

    /// The bodies of a declaration's doc examples and properties, whose names resolve as in a
    /// test of the declaration's module (program.doc-examples; tests.property-checking).
    pub(super) fn examples(&mut self, docs: Option<ast::Docs>) -> Vec<BodyIndex> {
        let ctx = Ctx::module();
        docs.map(|d| d.lines())
            .unwrap_or_default()
            .into_iter()
            .filter_map(|line| match line {
                ast::DocLine::Example(example, offset) => Some((example, offset, None)),
                ast::DocLine::Property(property, offset, text) => {
                    Some((property, offset, Some(text)))
                }
                ast::DocLine::Text(_) => None,
            })
            .map(|(example, offset, text)| {
                let outer = std::mem::replace(&mut self.base, offset);
                let claim = example.expr();
                let at = claim
                    .as_ref()
                    .map_or_else(|| self.at(example.syntax()), |e| self.at(e.syntax()));
                let index = self.body(at, |this| {
                    let e = this.opt_expr(&ctx, claim);
                    match text {
                        Some(text) => BodyValue::Property(e, text),
                        None => BodyValue::Expr(e),
                    }
                });
                self.base = outer;
                index
            })
            .collect()
    }
}
