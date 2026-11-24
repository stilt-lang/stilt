//! Macro uses (macros.uses, macros.matching and macros.expansion): each names its macro as a
//! function's name is resolved, is matched against the macro's arms, and is replaced by the
//! expansion of the first that matches, which is then resolved as code written there, in a region
//! of its own ([`regions`]), and moved back to the tokens the user wrote.

mod budget;
mod declaration;
mod parts;
mod procedural;
mod regions;
mod tokens;

use std::sync::Arc;

use stilt_diag::{Diagnostic, codes};
use stilt_syntax::ast::{self, AstNode};
use stilt_syntax::forms::{Form, FormParse, Piece, parse_form};
use stilt_syntax::{TextRange, TextSize};

use super::patterns::Binder;
use super::poly::Spot;
use super::{Ctx, Meaning, Resolver, dotted};
use crate::hir::{
    Expansion, Expr, ExprKind, Ident, Item, Name, Pat, PatKind, ShownTok, Template, Ty,
    remap_diagnostic, remap_expr, remap_pat,
};
use crate::macros::matching::match_arms;
use crate::macros::substitute::{Expander, Tok};
use crate::macros::{MacroDef, macro_defs};
use crate::scope::{Kind, Namespace};

pub(crate) use budget::Budget;
pub(crate) use regions::Region;

/// The most expansions that nest (macros.nested-expansions).
const MAX_DEPTH: usize = 128;

/// Why a use has no expansion: it is a failed use of a procedural macro (macros.failed-uses and
/// macros.raised-errors), or it has another error.
enum Unmade {
    Failed,
    Error,
}

/// An expansion made from a use, and parsed, ready to be resolved.
struct Made {
    parsed: FormParse,
    tokens: Vec<Tok>,
    /// The marks of its own tokens' names, each with the module where they resolve.
    marks: Vec<(u32, Name)>,
    /// The macro as the use names it, and where the use is reported.
    name: Name,
    at: TextRange,
    template: Template,
    /// The form it stands as.
    form: Form,
    /// Whether a procedural macro made it, whose fresh names are numbered in the order their
    /// bindings appear in it (macros.showing).
    procedural: bool,
}

impl Resolver<'_> {
    /// A use where an expression stands.
    pub(super) fn macro_expr(&mut self, ctx: &Ctx, m: &ast::MacroUse, at: TextRange) -> Expr {
        let error = Expr {
            kind: ExprKind::Error,
            at,
        };
        if let Some(e) = self.foreign_macro(ctx, m, at) {
            return e;
        }
        let groups: Vec<ast::MacroGroup> = m.groups().collect();
        let expanded = self.written_use(|this| {
            let made = this.make(ctx, m.path(), &groups, at, Form::Expr).ok()?;
            let e = made.parsed.node().and_then(ast::Expr::cast)?;
            let start = this.enter(made, at);
            let mut e = this.expr(ctx, &e);
            let region = this.leave(&start);
            remap_expr(&mut e, &|r| place_in(&region, r));
            Some(e)
        });
        expanded.flatten().unwrap_or(error)
    }

    /// A use where a pattern stands. A failed use binds nothing, and marks the binder so that
    /// the scope it opens takes a name that names nothing as the error type (macros.failed-uses).
    pub(super) fn macro_pat(
        &mut self,
        ctx: &Ctx,
        b: &mut Binder,
        m: &ast::MacroPat,
        at: TextRange,
    ) -> Pat {
        let error = Pat {
            kind: PatKind::Error,
            at,
        };
        let groups: Vec<ast::MacroGroup> = m.group().into_iter().collect();
        let expanded = self.written_use(|this| {
            let made = match this.make(ctx, m.path(), &groups, at, Form::Pattern) {
                Ok(made) => made,
                Err(Unmade::Failed) => {
                    b.failed = true;
                    return None;
                }
                Err(Unmade::Error) => return None,
            };
            let p = made.parsed.node().and_then(ast::Pattern::cast)?;
            let start = this.enter(made, at);
            let mut p = this.pattern(ctx, b, Some(p));
            let region = this.leave(&start);
            remap_pat(&mut p, &|r| place_in(&region, r));
            Some(p)
        });
        expanded.flatten().unwrap_or(error)
    }

    /// A use where a type stands, of a procedural macro whose result is `meta.Type`
    /// (macros.procedural-uses).
    pub(super) fn macro_type(&mut self, ctx: &Ctx, m: &ast::MacroType, spot: Spot) -> Ty {
        let at = self.at(m.syntax());
        let groups: Vec<ast::MacroGroup> = m.group().into_iter().collect();
        let expanded = self.written_use(|this| {
            let made = this.make(ctx, m.path(), &groups, at, Form::Type).ok()?;
            let t = made.parsed.node().and_then(ast::Type::cast)?;
            let start = this.enter(made, at);
            let ty = this.ty_in(ctx, Some(t), spot);
            this.leave(&start);
            Some(ty)
        });
        expanded.flatten().unwrap_or(Ty::Error)
    }

    /// The macro a use's path names, if it names one.
    fn macro_named(&mut self, ctx: &Ctx, path: &[Ident]) -> Option<(Item, Arc<MacroDef>)> {
        match self.walk_to_end(ctx, Namespace::Values, "a macro", path) {
            (Meaning::Item(item, entry), _) if entry.kind == Kind::Macro => {
                let file = self.map.module(&item.home)?.file;
                let def = macro_defs(self.db, file).get(&item.name)?.clone();
                // A macro whose templates have an error expands no use (macros.matching).
                // While a template is checked nothing expands, so its own uses ask nothing, which
                // keeps a macro that uses itself from asking for its own templates.
                if !self.checking
                    && !def.broken
                    && !declaration::templates_resolve(self.db, self.program, file, item.name)
                {
                    return None;
                }
                Some((item, def))
            }
            (Meaning::Broken, _) => None,
            (m, last) => {
                self.wrong_kind(&path[last], &m, "a macro");
                None
            }
        }
    }

    /// The expansion of a use, matched and parsed as `form`, or why it has none: an error,
    /// which is reported unless the macro's declaration has one (errors.root-causes).
    fn make(
        &mut self,
        ctx: &Ctx,
        path: Option<ast::Path>,
        groups: &[ast::MacroGroup],
        at: TextRange,
        form: Form,
    ) -> Result<Made, Unmade> {
        if self.ended() {
            return Err(Unmade::Error);
        }
        let path = self.path(path);
        match self.procedural(&path, groups, at, form) {
            procedural::Found::NotProc => {}
            procedural::Found::Failed => return Err(Unmade::Failed),
            procedural::Found::Made(made) if self.spend(made.tokens.len(), made.name, made.at) => {
                return Ok(*made);
            }
            procedural::Found::Made(_) => return Err(Unmade::Error),
        }
        let (item, def) = self.macro_named(ctx, &path).ok_or(Unmade::Error)?;
        if self.checking || def.broken {
            return Err(Unmade::Error);
        }
        let name = Name::from(dotted(&path));
        let (path_at, _) = self.placed(path_span(&path));
        let (use_at, _) = self.placed(at);
        if !self.fits(&def, name, path_at, form) {
            return Err(Unmade::Error);
        }
        if self.regions.len() >= MAX_DEPTH {
            self.too_deep(name, use_at);
            return Err(Unmade::Error);
        }
        let substituted = self.substituted(&def, name, groups, use_at, form);
        let (arm, tokens, parsed, mark) = substituted.ok_or(Unmade::Error)?;
        if !self.spend(tokens.len(), name, use_at) {
            return Err(Unmade::Error);
        }
        let template = self.template_of(&item, &def, arm);
        Ok(Made {
            parsed,
            tokens,
            marks: vec![(mark, item.home)],
            name,
            at: use_at,
            template,
            form,
            procedural: false,
        })
    }

    /// The tokens of the first arm that matches a use, its template's fragments substituted,
    /// parsed as `form`, with the arm's index and the mark of the template's names.
    fn substituted(
        &mut self,
        def: &MacroDef,
        name: Name,
        groups: &[ast::MacroGroup],
        use_at: TextRange,
        form: Form,
    ) -> Option<(usize, Vec<Tok>, FormParse, u32)> {
        let use_tokens = self.use_tokens(groups);
        if use_tokens.tokens.is_empty() {
            return None;
        }
        let (arm, bindings) = match match_arms(&def.arms, &use_tokens) {
            Ok(found) => found,
            Err(failure) => {
                let tok = &use_tokens.tokens[failure.at.min(use_tokens.tokens.len() - 1)];
                let message = format!(
                    "no arm of `{name}!` matches this use: the closest expects {} here",
                    failure.expected
                );
                self.error(codes::E0222, tok.at, message);
                return None;
            }
        };
        self.marks += 1;
        let mark = self.marks;
        let own = |kind, text: &Name, _| Tok {
            kind,
            text: *text,
            at: use_at,
            user: false,
            mark,
        };
        let mut tokens = Vec::new();
        let expander = Expander {
            bindings: &bindings,
            own: &own,
        };
        expander.items(&def.arms[arm].template, &mut Vec::new(), &mut tokens);
        let parsed = parse(&tokens, form);
        if !parsed.is_whole(tokens.len()) {
            let message = format!("the expansion of `{name}!` here doesn't parse");
            self.error(codes::E0222, use_at, message);
            return None;
        }
        Some((arm, tokens, parsed, mark))
    }

    /// Whether a macro stands where `form` does, or E0223 at its path (macros.uses).
    fn fits(&mut self, def: &MacroDef, name: Name, at: TextRange, form: Form) -> bool {
        let (fits, here) = match form {
            Form::Pattern => (def.pattern, "a pattern"),
            Form::Type => (false, "a type"),
            _ => (def.expr, "an expression"),
        };
        if fits {
            return true;
        }
        let message = if def.expr {
            format!("`{name}!` is an expression macro, but it stands here where {here} does")
        } else if def.pattern {
            format!("`{name}!` is a pattern macro, but it stands here where {here} does")
        } else {
            format!("`{name}!` stands nowhere, since its templates aren't all of one kind")
        };
        self.error(codes::E0223, at, message);
        false
    }

    /// The macros whose expansions are being resolved, outermost first, then `name`.
    fn chain(&self, name: Name) -> String {
        let mut names: Vec<Name> = Vec::new();
        for n in self.regions.iter().map(|r| r.name).chain([name]) {
            if !names.contains(&n) {
                names.push(n);
            }
        }
        names
            .iter()
            .map(|n| format!("`{n}!`"))
            .collect::<Vec<_>>()
            .join(" and ")
    }

    /// Where a note shows the template of an arm.
    fn template_of(&self, item: &Item, def: &MacroDef, arm: usize) -> Template {
        let arm = &def.arms[arm];
        if item.home == self.module.name {
            Template::Here(arm.at)
        } else {
            Template::Elsewhere(arm.text.clone())
        }
    }

    /// Starts resolving an expansion made for the use at `at`, in a region of its own, and
    /// records it among the body's.
    fn enter(&mut self, made: Made, at: TextRange) -> Start {
        let parent = self.region_at(at.start()).map(|r| {
            let covered = r.place_tokens(at);
            (
                u32::try_from(r.index).unwrap_or(u32::MAX),
                covered.0,
                covered.1,
            )
        });
        let index = self.expansions.len();
        self.expansions.push(Expansion {
            at: made.at,
            name: made.name,
            template: made.template,
            form: made.form,
            tokens: Vec::new(),
            parent,
        });
        let base = TextSize::from(self.next_virtual);
        let spans: Vec<TextRange> = made
            .parsed
            .starts
            .iter()
            .zip(&made.tokens)
            .map(|(&start, t)| TextRange::at(start, TextSize::of(&*t.text)))
            .collect();
        let len = spans.last().map_or(0, |s| u32::from(s.end()));
        self.next_virtual = self.next_virtual.saturating_add(len + 2);
        self.regions.push(Region {
            base,
            spans,
            tokens: made.tokens,
            marks: made.marks,
            name: made.name,
            index,
            fresh: rustc_hash::FxHashSet::default(),
            procedural: made.procedural,
        });
        Start {
            base: std::mem::replace(&mut self.base, base),
            locals: self.locals.len(),
            diagnostics: self.diagnostics.len(),
            references: self.references.len(),
            analysed: self.analysed.len(),
        }
    }

    /// Ends resolving the innermost expansion: every position found in it is moved to the
    /// user's tokens, the errors of names its template writes are left to its declaration, and
    /// the template's names are no references of this module.
    fn leave(&mut self, start: &Start) -> Region {
        self.base = start.base;
        let region = self.regions.pop().expect("an expansion is being resolved");
        let map = |r: TextRange| place_in(&region, r);
        for local in &mut self.locals[start.locals..] {
            local.at = map(local.at);
        }
        let mut kept = Vec::new();
        for (name, at) in self.references.drain(start.references..) {
            if !region.holds_at(at.start()) || region.place(at).1 {
                kept.push((name, map(at)));
            }
        }
        self.references.extend(kept);
        for d in &mut self.analysed[start.analysed..] {
            remap_diagnostic(d, &map);
        }
        self.settle_diagnostics(start.diagnostics, &region);
        self.expansions[region.index].tokens = shown_tokens(&region);
        region
    }

    /// Moves the diagnostics found in an expansion from `from` on to the user's tokens: those
    /// of names the template writes that don't exist, which its declaration reports, are
    /// dropped, those at the template's own tokens get a note that shows it, those at the user's a
    /// note that names the macro (goal compile-time-errors-at-user-code), and a fix that would edit
    /// the template is dropped.
    fn settle_diagnostics(&mut self, from: usize, region: &Region) {
        let found: Vec<Diagnostic> = self.diagnostics.drain(from..).collect();
        let mut renumbered = Vec::new();
        for mut d in found {
            let (_, user) = place_and_user(region, d.range);
            if d.code == codes::E0211 && !user {
                renumbered.push(None);
                continue;
            }
            d.fixes
                .retain(|f| f.edits.iter().all(|e| place_and_user(region, e.range).1));
            remap_diagnostic(&mut d, &|r| place_in(region, r));
            let expansion = &self.expansions[region.index];
            d = if user {
                expansion.named(d)
            } else {
                expansion.noted(d)
            };
            renumbered.push(Some(self.diagnostics.len()));
            self.diagnostics.push(d);
        }
        if let Some(unknown) = &mut self.unknown {
            unknown.retain_mut(|(_, at)| match at {
                Some(i) if *i >= from => match renumbered[*i - from] {
                    Some(j) => {
                        *i = j;
                        true
                    }
                    None => false,
                },
                _ => true,
            });
        }
    }
}

/// What the resolver was doing before an expansion, to go back to.
struct Start {
    base: TextSize,
    locals: usize,
    diagnostics: usize,
    references: usize,
    analysed: usize,
}

/// A position moved out of a region to where it is reported, or left as it is when the region
/// doesn't hold it.
fn place_in(region: &Region, r: TextRange) -> TextRange {
    place_and_user(region, r).0
}

fn place_and_user(region: &Region, r: TextRange) -> (TextRange, bool) {
    if region.holds_at(r.start()) {
        region.place(r)
    } else {
        (r, true)
    }
}

/// The span of a path, from its first name to its last.
fn path_span(path: &[Ident]) -> TextRange {
    match (path.first(), path.last()) {
        (Some(first), Some(last)) => first.at.cover(last.at),
        _ => TextRange::default(),
    }
}

fn parse(tokens: &[Tok], form: Form) -> FormParse {
    let pieces: Vec<Piece<'_>> = tokens
        .iter()
        .map(|t| Piece {
            kind: t.kind,
            text: &t.text,
        })
        .collect();
    parse_form(&pieces, form)
}

/// The tokens of an expansion as `stilt show --expanded` writes them, each fresh name with
/// the number written after its `#`: a pattern macro's expansion's (macros.showing), or, in a
/// procedural macro's expansion, its place in the order the fresh names' bindings appear
/// (macros.showing), which a name's first token is.
fn shown_tokens(region: &Region) -> Vec<ShownTok> {
    let mut order: Vec<(u32, Name)> = Vec::new();
    region
        .tokens
        .iter()
        .map(|t| {
            let key = (t.mark, t.text);
            if !region.fresh.contains(&key) {
                return (t.kind, t.text, None);
            }
            let number = if region.procedural {
                let at = order.iter().position(|k| *k == key).unwrap_or_else(|| {
                    order.push(key);
                    order.len() - 1
                });
                u32::try_from(at + 1).unwrap_or(u32::MAX)
            } else {
                t.mark
            };
            (t.kind, t.text, Some(number))
        })
        .collect()
}
