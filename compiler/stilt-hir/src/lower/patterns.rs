//! Patterns, and the names they bind (patterns.pattern-forms).

use std::collections::{BTreeSet, HashSet};
use stilt_diag::{Diagnostic, Edit, Fix, MAX_ALTERNATIVES, codes};

use stilt_syntax::ast::{self, AstNode};
use stilt_syntax::text::{number_text, string_value};
use stilt_syntax::{SyntaxKind as K, TextRange};

use super::{Ctx, Meaning, Resolver};
use crate::hir::{
    Failure, Fallback, FieldPat, Ident, ListRest, Local, LocalId, Name, Pat, PatKind, Ty, TypeRef,
};
use crate::scope::{Kind, Namespace, Value, is_primitive};

/// The names a pattern binds.
#[derive(Debug, Default)]
pub(super) struct Binder {
    /// Oldest first.
    pub(super) bound: Vec<(Name, LocalId)>,
    /// Bound names whose uses have the error type.
    broken: HashSet<Name>,
    /// Names that only some alternatives of an or-pattern bind. They bind nothing, but their
    /// uses have the error type unless the pattern binds them elsewhere (patterns.or-patterns).
    partial: Vec<Name>,
    /// In an alternative of an or-pattern after the first, the variables of the first, which
    /// the same names bind again.
    shared: Vec<(Name, LocalId)>,
    /// Whether names are checked against the module's names here. Inside an alternative of an
    /// or-pattern they are checked once, when the or-pattern adds them to its own binder.
    unchecked: bool,
    /// Whether it holds a failed use of a procedural macro, which binds nothing, so that in the
    /// scope it opens a name that names nothing has the error type and is reported nowhere
    /// (macros.failed-uses; program.bodies-with-errors).
    pub(super) failed: bool,
}

/// What a scope holds after the names of a pattern with a failed use: no name is empty.
const FAILED_USE: &str = "";

impl Binder {
    pub(super) fn names(&self) -> BTreeSet<Name> {
        self.bound
            .iter()
            .map(|(name, _)| *name)
            .chain(self.partial.iter().copied())
            .collect()
    }
}

impl Resolver<'_> {
    pub(super) fn fresh(&mut self, n: &Ident) -> LocalId {
        let id = LocalId(u32::try_from(self.locals.len()).expect("under 4G locals"));
        self.locals.push(Local {
            name: n.name,
            at: n.at,
        });
        id
    }

    /// Puts the names a pattern binds in scope.
    pub(super) fn bring_into_scope(&mut self, b: &Binder) {
        if b.failed {
            self.scope.push((Name::from(FAILED_USE), None));
        }
        for name in &b.partial {
            self.scope.push((*name, None));
        }
        for (name, v) in &b.bound {
            let v = (!b.broken.contains(name)).then_some(*v);
            self.scope.push((*name, v));
        }
    }

    /// Whether the scope is one that a pattern with a failed use opens.
    pub(super) fn after_failed_use(&self) -> bool {
        self.scope.iter().any(|(name, _)| &**name == FAILED_USE)
    }

    fn imports_module(&self, name: &str) -> bool {
        matches!(
            self.own.values.get(name),
            Some(Value::Import(_) | Value::ImportError)
        )
    }

    /// Binds `n` to `v`, unless the pattern already binds that name.
    fn add(&mut self, b: &mut Binder, n: &Ident, v: LocalId) {
        if b.bound.iter().any(|(name, _)| *name == n.name) {
            let message = format!("`{}` is already bound here", n.name);
            self.error(codes::E0208, n.at, message);
            return;
        }
        if !b.unchecked {
            if is_primitive(&n.name) {
                // errors.primitive-type-bindings
                let message = format!("`{}` is a primitive type name", n.name);
                self.error(codes::E0210, n.at, message);
                b.broken.insert(n.name);
            } else if self.imports_module(&n.name) {
                // program.one-value-namespace
                let message = format!("`{}` is the name of an imported module", n.name);
                self.error(codes::E0207, n.at, message);
                b.broken.insert(n.name);
            }
        }
        b.bound.push((n.name, v));
    }

    /// Binds `n`, under its key in scope: a name a macro's template binds is fresh
    /// (macros.hygiene).
    pub(super) fn bind(&mut self, b: &mut Binder, n: &Ident) -> LocalId {
        self.check_binding(n);
        let key = Ident {
            name: self.key(n),
            at: n.at,
        };
        if key.name != n.name {
            self.bound_fresh(n.at, n.name);
        }
        let shared = b.shared.iter().find(|(name, _)| *name == key.name);
        let v = match shared {
            Some(&(_, v)) => v,
            None => self.fresh(n),
        };
        self.add(b, &key, v);
        v
    }

    /// The type a struct literal or a record pattern names (declarations.name-lookup).
    pub(super) fn record_ty(&mut self, ctx: &Ctx, path: &[Ident]) -> TypeRef {
        let at = path.first().map_or(TextRange::default(), |n| n.at);
        let ty = match self.walk_to_end(ctx, Namespace::Types, "a type", path) {
            (Meaning::Broken, _) => Ty::Error,
            (Meaning::Param(v), _) => Ty::Param(v),
            (Meaning::SelfType(t), _) => t,
            (Meaning::Item(item, entry), _) if entry.kind == Kind::Type => {
                Ty::Con(item, Vec::new())
            }
            (m, last) => {
                self.wrong_kind(&path[last], &m, "a type");
                Ty::Error
            }
        };
        TypeRef { ty, at }
    }

    /// A path in a pattern names a variant, a constant, or a constant of a type
    /// (patterns.pattern-forms and patterns.constants).
    fn pattern_path(&mut self, ctx: &Ctx, path: &[Ident], payload: Option<Vec<Pat>>) -> PatKind {
        let noun = "a variant or a constant";
        let (m, last) = self.walk(ctx, Namespace::Values, noun, false, path);
        let rest = path.len() - last - 1;
        let has_payload = payload.is_some();
        let no_payload = |this: &mut Self, n: &Ident, kind| {
            if has_payload {
                let message = format!("`{}` is a constant, which takes no payload", n.name);
                this.error(codes::E0212, n.at, message);
                PatKind::Error
            } else {
                kind
            }
        };
        let as_type = m.as_type();
        match (m, as_type) {
            (Meaning::Broken, _) => PatKind::Error,
            (Meaning::Item(item, entry), _) if rest == 0 && entry.kind == Kind::Variant => {
                PatKind::Variant(item, payload.unwrap_or_default())
            }
            (Meaning::Item(item, entry), _) if rest == 0 && entry.kind == Kind::Const => {
                no_payload(self, &path[last], PatKind::Const(item))
            }
            (_, Some(ty)) if rest == 1 => {
                let member = path[last + 1].clone();
                if has_payload && self.is_variant(ctx, &member) {
                    self.variant_through_type(&path[last], &member);
                    return PatKind::Error;
                }
                let ty = TypeRef {
                    ty,
                    at: path[last].at,
                };
                no_payload(
                    self,
                    &member,
                    PatKind::AssocConst(Box::new(ty), member.clone()),
                )
            }
            (m, _) => {
                let what = if rest == 0 { noun } else { "a module" };
                self.wrong_kind(&path[last], &m, what);
                PatKind::Error
            }
        }
    }

    /// Whether `n` names a variant where it is written.
    fn is_variant(&mut self, ctx: &Ctx, n: &Ident) -> bool {
        matches!(
            self.lookup(ctx, Namespace::Values, false, n),
            Some(Meaning::Item(_, entry)) if entry.kind == Kind::Variant
        )
    }

    /// `Shape.Circle(r)`, a variant named through its type, as other languages write it: E0212
    /// says that a pattern names a variant alone (patterns.pattern-forms), and the fix deletes the
    /// type.
    fn variant_through_type(&mut self, ty: &Ident, variant: &Ident) {
        let message = format!(
            "`{}` is a variant, named alone rather than through `{}`",
            variant.name, ty.name
        );
        let written = TextRange::new(ty.at.start(), variant.at.start());
        let fix = Fix::new("name the variant alone", vec![Edit::delete(written)]);
        let d = Diagnostic::new(codes::E0212, variant.at, message)
            .with_help(
                "A variant's name is visible wherever its type is, in patterns and in \
                 expressions alike.",
            )
            .with_fix(fix);
        self.diagnostics.push(d);
    }

    /// A name that a pattern writes without a module, with its payload. What it means in the
    /// module's scope, as [`Self::pattern_path`] reads it, is its fallback, with the error kept
    /// for type checking, which reports it only if the type the pattern is matched against has
    /// no variant of that name (patterns.variants-by-type).
    fn bare(&mut self, ctx: &Ctx, n: &Ident, payload: Vec<Pat>, has_payload: bool) -> PatKind {
        let noun = "a variant or a constant";
        let failed = |code, message| {
            Fallback::Failed(Failure {
                code,
                message,
                close: Vec::new(),
            })
        };
        let wrong = |m: &Meaning| format!("`{}` is {}, not {noun}", n.name, m.describe());
        let fallback = match self.lookup(ctx, Namespace::Values, false, n) {
            Some(Meaning::Item(item, entry)) if entry.kind == Kind::Variant => {
                Fallback::Variant(item)
            }
            Some(Meaning::Item(item, entry)) if entry.kind == Kind::Const && !has_payload => {
                Fallback::Const(item)
            }
            Some(Meaning::Item(_, entry)) if entry.kind == Kind::Const => {
                let message = format!("`{}` is a constant, which takes no payload", n.name);
                failed(codes::E0212, message)
            }
            Some(Meaning::Broken) => Fallback::Error,
            Some(m) => failed(codes::E0212, wrong(&m)),
            None => match self.lookup(ctx, Namespace::Types, true, n) {
                Some(Meaning::Broken) => Fallback::Error,
                Some(m) => failed(codes::E0212, wrong(&m)),
                None => {
                    let here = self.names_here(ctx, Namespace::Values, false);
                    let close =
                        stilt_diag::close(&n.name, here.iter().map(|h| &**h), MAX_ALTERNATIVES);
                    self.deferred_name(&n.name);
                    Fallback::Failed(Failure {
                        code: codes::E0211,
                        message: format!("unknown name `{}`", n.name),
                        close: close.into_iter().map(Name::from).collect(),
                    })
                }
            },
        };
        PatKind::Bare(n.clone(), payload, Box::new(fallback))
    }

    pub(super) fn pattern(&mut self, ctx: &Ctx, b: &mut Binder, p: Option<ast::Pattern>) -> Pat {
        let Some(p) = p else {
            return Pat {
                kind: PatKind::Error,
                at: TextRange::default(),
            };
        };
        let at = self.at(p.syntax());
        let kind = match p {
            // A splice stands only in a quote, whose contents [`Resolver::quote`] reads.
            ast::Pattern::WildcardPat(_) | ast::Pattern::SplicePat(_) => PatKind::Wild,
            ast::Pattern::BindPat(bind) => {
                let n = self.name(bind.name(), bind.syntax());
                PatKind::Bind(self.bind(b, &n))
            }
            ast::Pattern::LiteralPat(literal) => literal_pattern(&literal),
            ast::Pattern::TuplePat(t) => PatKind::Tuple(self.patterns(ctx, b, t.patterns())),
            ast::Pattern::ParenPat(inner) => return self.pattern(ctx, b, inner.pattern()),
            ast::Pattern::PathPat(path) => {
                let path = self.path(path.path());
                match bare(&path) {
                    Some(n) => self.bare(ctx, n, Vec::new(), false),
                    None => self.pattern_path(ctx, &path, None),
                }
            }
            ast::Pattern::VariantPat(variant) => {
                let payload = self.patterns(ctx, b, variant.patterns());
                let path = self.path(variant.path());
                match bare(&path) {
                    Some(n) => self.bare(ctx, n, payload, true),
                    None => self.pattern_path(ctx, &path, Some(payload)),
                }
            }
            ast::Pattern::RecordPat(record) => self.record_pattern(ctx, b, &record),
            ast::Pattern::ListPat(list) => self.list_pattern(ctx, b, &list),
            ast::Pattern::OrPat(or) => PatKind::Or(self.alternatives(ctx, b, or.patterns())),
            ast::Pattern::MacroPat(m) => return self.macro_pat(ctx, b, &m, at),
        };
        Pat { kind, at }
    }

    fn patterns(
        &mut self,
        ctx: &Ctx,
        b: &mut Binder,
        patterns: impl Iterator<Item = ast::Pattern>,
    ) -> Vec<Pat> {
        patterns.map(|q| self.pattern(ctx, b, Some(q))).collect()
    }

    /// A record pattern. A field without a pattern binds a variable of its own name.
    fn record_pattern(&mut self, ctx: &Ctx, b: &mut Binder, record: &ast::RecordPat) -> PatKind {
        let fields = record
            .fields()
            .map(|f| {
                let field = self.field(f.field(), f.syntax());
                let pattern = match f.pattern() {
                    Some(q) => self.pattern(ctx, b, Some(q)),
                    None => Pat {
                        kind: PatKind::Bind(self.bind(b, &field)),
                        at: field.at,
                    },
                };
                FieldPat { field, pattern }
            })
            .collect();
        // A pattern that names no type matches an anonymous record, or any record known to
        // have its fields (records.anonymous-patterns).
        if record.path().is_none() {
            return PatKind::AnonRecord(fields, record.has_rest());
        }
        let path = self.path(record.path());
        PatKind::Record(
            Box::new(self.record_ty(ctx, &path)),
            fields,
            record.has_rest(),
        )
    }

    fn list_pattern(&mut self, ctx: &Ctx, b: &mut Binder, list: &ast::ListPat) -> PatKind {
        let items = self.patterns(ctx, b, list.patterns());
        let rest = match list.rest() {
            None => ListRest::Exact,
            Some(rest) => match rest.name() {
                None => ListRest::Rest,
                Some(name) => {
                    let n = self.name(Some(name), rest.syntax());
                    ListRest::Bind(self.bind(b, &n))
                }
            },
        };
        PatKind::List(items, rest)
    }

    /// patterns.or-patterns. Each alternative binds its names in a binder of its own, and the later
    /// ones reuse the first one's variables. Then the or-pattern binds, once, each name that
    /// every alternative binds. A name that only some alternatives bind has the error type
    /// wherever it is used.
    fn alternatives(
        &mut self,
        ctx: &Ctx,
        b: &mut Binder,
        patterns: impl Iterator<Item = ast::Pattern>,
    ) -> Vec<Pat> {
        let mut resolved = Vec::new();
        let mut binders: Vec<Binder> = Vec::new();
        for p in patterns {
            let mut sub = Binder {
                shared: binders
                    .first()
                    .map(|first| first.bound.clone())
                    .unwrap_or_default(),
                unchecked: true,
                ..Binder::default()
            };
            // A parenthesized alternative is placed where the pattern inside is.
            let pattern = self.pattern(ctx, &mut sub, Some(p));
            if let Some(first) = binders.first()
                && sub.names() != first.names()
            {
                let message = "this alternative binds different names from the first".to_owned();
                self.error(codes::E0217, pattern.at, message);
            }
            resolved.push(pattern);
            binders.push(sub);
        }
        let mut vars: Vec<(Name, LocalId)> = Vec::new();
        for sub in &binders {
            for (name, v) in &sub.bound {
                if !vars.iter().any(|(n, _)| n == name) {
                    vars.push((*name, *v));
                }
            }
        }
        let everywhere = |name: &Name| {
            binders
                .iter()
                .all(|sub| sub.bound.iter().any(|(n, _)| n == name) && !sub.broken.contains(name))
        };
        let mut partial: BTreeSet<Name> = vars
            .iter()
            .filter(|(name, _)| !everywhere(name))
            .map(|(name, _)| *name)
            .collect();
        partial.extend(binders.iter().flat_map(|sub| sub.partial.iter().copied()));
        for (name, v) in &vars {
            if everywhere(name) {
                let n = Ident {
                    name: *name,
                    at: self.locals[v.0 as usize].at,
                };
                self.add(b, &n, *v);
            }
        }
        let mut merged: Vec<Name> = partial.into_iter().collect();
        merged.append(&mut b.partial);
        b.partial = merged;
        b.failed |= binders.iter().any(|sub| sub.failed);
        resolved
    }
}

/// The name of a path of one name, which a pattern writes without a module
/// (patterns.pattern-forms). `Self` is a type wherever it is written.
fn bare(path: &[Ident]) -> Option<&Ident> {
    match path {
        [n] if &*n.name != "Self" => Some(n),
        _ => None,
    }
}

/// A literal pattern: an integer, with its `-` if it has one, a string or a `bool`.
fn literal_pattern(literal: &ast::LiteralPat) -> PatKind {
    match literal.literal() {
        Some(t) if t.kind() == K::INT => {
            let sign = if literal.is_negative() { "-" } else { "" };
            PatKind::Int(format!("{sign}{}", number_text(&t)))
        }
        Some(t) if t.kind() == K::STRING => PatKind::Str(string_value(&t)),
        Some(t) => PatKind::Bool(t.kind() == K::TRUE_KW),
        None => PatKind::Error,
    }
}
