//! A macro's declaration (macros.syntax-declarations, macros.patterns and macros.templates): the
//! errors of its patterns and templates, and the names its templates write, resolved where it is
//! declared, so that one that doesn't exist is E0211 there rather than at a use.

use std::collections::{HashMap, HashSet};

use stilt_diag::codes;
use stilt_syntax::TextSize;
use stilt_syntax::ast::{self, AstNode};
use stilt_syntax::forms::Form;

use super::super::patterns::Binder;
use super::super::{Ctx, Resolver};
use super::regions::Region;
use super::{parse, place_and_user};
use crate::hir::walk::{Visitor, walk_expr};
use crate::hir::{Expr, ExprKind, Item, MacroDecl, Name, Pat, remap_diagnostic};
use crate::macros::substitute::{Tok, placeholders};
use crate::macros::{FragKind, MacroArm, MacroDef, read};

use stilt_db::{Db, Program, SourceFile};

use crate::scope::modules_of;

/// Whether the names that the templates of the macro `name`, declared in `file`, write resolve
/// where it is declared without an error (macros.checked-templates), so that its uses, in any
/// module, expand. A macro whose templates don't is reported at its declaration and expands no use
/// (macros.matching). Resolving a template expands no macro, so this reads no module's resolution.
#[salsa::tracked]
pub(crate) fn templates_resolve(
    db: &dyn Db,
    program: Program,
    file: SourceFile,
    name: Name,
) -> bool {
    let Some(def) = crate::macros::macro_defs(db, file).get(&name).cloned() else {
        return false;
    };
    let map = modules_of(db, program, file);
    let Some(module) = map.of_file(file) else {
        return false;
    };
    let mut resolver = Resolver::new(db, program, map, module, file);
    !def.broken && resolver.template_names(&def).1
}

impl Resolver<'_> {
    /// A macro's declaration, with the errors of its patterns and templates reported.
    pub(in crate::lower) fn macro_decl(&mut self, s: &ast::Syntax) -> MacroDecl {
        let (def, errors) = read(s);
        self.diagnostics.extend(errors);
        let names = if def.broken {
            Vec::new()
        } else {
            self.template_names(&def).0
        };
        let written = |node: Option<&stilt_syntax::SyntaxNode>| {
            node.map(|n| {
                n.text()
                    .to_string()
                    .split_whitespace()
                    .collect::<Vec<_>>()
                    .join(" ")
            })
            .unwrap_or_default()
        };
        let mut patterns = Vec::new();
        let mut templates = Vec::new();
        for arm in s.arms() {
            let group = arm.pattern().map(|g| g.syntax().clone());
            let trailing = arm.trailing().map(|f| f.syntax().clone());
            patterns.push(format!(
                "{} {}",
                written(group.as_ref()),
                written(trailing.as_ref())
            ));
            templates.push(written(arm.template().map(|t| t.syntax().clone()).as_ref()));
        }
        MacroDecl {
            name: def.name,
            patterns: patterns.join("\n"),
            templates: templates.join("\n"),
            names,
        }
    }

    /// Resolves the names each template writes, with a placeholder for each fragment, and reports
    /// each error they give at the template, an unknown name once (macros.checked-templates). Such
    /// an error makes the macro expand no use (macros.matching), so that it is the declaration's
    /// alone. Returns the functions they name, and whether they gave no error.
    pub(in crate::lower) fn template_names(&mut self, def: &MacroDef) -> (Vec<Item>, bool) {
        let mut unknown = HashSet::new();
        let mut names = Functions(Vec::new());
        let mut clean = true;
        for arm in &def.arms {
            let from = self.diagnostics.len();
            match self.resolve_template(def, arm) {
                Some(Either::Expr(e)) => names.expr(&e),
                Some(Either::Pat(p)) => names.pat(&p),
                None => {}
            }
            let found: Vec<_> = self.diagnostics.drain(from..).collect();
            for d in found {
                clean &= !d.is_error();
                if d.code != codes::E0211 || unknown.insert(d.message.clone()) {
                    self.diagnostics.push(d);
                }
            }
        }
        (names.0, clean)
    }

    /// Resolves a template in a region of its own, and keeps the errors at its own tokens.
    fn resolve_template(&mut self, def: &MacroDef, arm: &MacroArm) -> Option<Either> {
        self.marks += 1;
        let mark = self.marks;
        let own = |kind, text: &Name, at| Tok {
            kind,
            text: *text,
            at,
            user: false,
            mark,
        };
        let kinds: HashMap<Name, FragKind> = arm.kinds().into_iter().collect();
        let tokens = placeholders(&arm.template, &kinds, &own);
        let form = if def.expr { Form::Expr } else { Form::Pattern };
        let parsed = parse(&tokens, form);
        let node = parsed.node().filter(|_| parsed.is_whole(tokens.len()))?;
        let base = TextSize::from(self.next_virtual);
        let spans: Vec<_> = parsed
            .starts
            .iter()
            .zip(&tokens)
            .map(|(&start, t)| stilt_syntax::TextRange::at(start, TextSize::of(&*t.text)))
            .collect();
        let len = spans.last().map_or(0, |s| u32::from(s.end()));
        self.next_virtual = self.next_virtual.saturating_add(len + 2);
        self.regions.push(Region {
            base,
            spans,
            tokens,
            marks: vec![(mark, self.module.name)],
            name: def.name,
            index: usize::MAX,
            fresh: rustc_hash::FxHashSet::default(),
            procedural: false,
        });
        let frame = self.enter_body();
        let outer = (std::mem::replace(&mut self.base, base), self.checking);
        self.checking = true;
        let from = self.diagnostics.len();
        let ctx = Ctx::module();
        let resolved = if let Some(e) = ast::Expr::cast(node.clone()) {
            Some(Either::Expr(self.expr(&ctx, &e)))
        } else {
            ast::Pattern::cast(node)
                .map(|p| Either::Pat(self.pattern(&ctx, &mut Binder::default(), Some(p))))
        };
        (self.base, self.checking) = outer;
        self.leave_body(frame);
        let region = self.regions.pop().expect("the template's region");
        let found: Vec<_> = self.diagnostics.drain(from..).collect();
        for mut d in found {
            // At a declaration, each of the template's tokens is where it is written.
            if !place_and_user(&region, d.range).1 {
                remap_diagnostic(&mut d, &|r| place_and_user(&region, r).0);
                self.diagnostics.push(d);
            }
        }
        resolved
    }
}

/// A resolved template.
enum Either {
    Expr(Expr),
    Pat(Pat),
}

/// The functions that code names, each once.
struct Functions(Vec<Item>);

impl Visitor for Functions {
    fn expr(&mut self, e: &Expr) {
        if let ExprKind::Func(item) = &e.kind
            && !self.0.contains(item)
        {
            self.0.push(item.clone());
        }
        walk_expr(self, e);
    }
}
