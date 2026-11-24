//! Lookups of names, and of paths of names through modules (program.visibility and
//! program.namespaces; declarations.name-lookup).

use stilt_diag::{AlternativeKind, Diagnostic, codes};
use stilt_syntax::TextRange;

use rustc_hash::FxHashMap;

use super::{Ctx, Meaning, Resolver, SelfKind};
use crate::hir::{Ident, Item, Name, Ty};
use crate::scope::{Entry, Named, Namespace, PRELUDE, Scope, Value, module_scope, named};

/// What a module's resolution looked up in other modules, each read once: whole scopes, and
/// what a scope says of one name.
#[derive(Default)]
pub(super) struct Looked<'a> {
    scopes: FxHashMap<Box<str>, Option<&'a Scope>>,
    names: FxHashMap<(Name, Name), Option<&'a Named>>,
}

impl<'a> Resolver<'a> {
    /// The scope of the module `ns`, if there is one of that name. Reading it makes the module's
    /// resolution depend on all of that scope, so only what needs all of it reads it: the names
    /// a failed lookup suggests, and those of a macro's template; a lookup of one name reads
    /// [`Self::named_in`].
    pub(super) fn scope_of(&self, ns: &str) -> Option<&'a Scope> {
        if let Some(&scope) = self.looked.borrow().scopes.get(ns) {
            return scope;
        }
        let scope = (self.map.module(ns))
            .map(|module| &module_scope(self.db, self.program, module.file).scope);
        self.looked.borrow_mut().scopes.insert(ns.into(), scope);
        scope
    }

    /// What the scope of the module `ns` says of `name`, if there is a module of that name.
    /// Reading it makes the module's resolution depend on that name alone, so that an edit of
    /// `ns` that leaves it as it was doesn't resolve this module again (goal edit-to-diagnostics).
    pub(super) fn named_in(&self, ns: &str, name: &str) -> Option<&'a Named> {
        let key = (Name::from(ns), Name::from(name));
        if let Some(&found) = self.looked.borrow().names.get(&key) {
            return found;
        }
        let found =
            (self.map.module(ns)).map(|module| named(self.db, self.program, module.file, key.1));
        self.looked.borrow_mut().names.insert(key, found);
        found
    }
}

impl Resolver<'_> {
    /// `Self`, which only impl and trait blocks define (traits.impl-blocks).
    fn self_type(&mut self, ctx: &Ctx, at: TextRange) -> Meaning {
        match &ctx.self_kind {
            SelfKind::Impl(t) => Meaning::SelfType(t.clone()),
            SelfKind::Trait(_) => Meaning::SelfType(Ty::SelfTy),
            SelfKind::None => {
                let message = "`Self` exists only in impl and trait blocks".to_owned();
                self.error(codes::E0215, at, message);
                Meaning::Broken
            }
        }
    }

    /// The item `name` of module `ns`, in one namespace.
    pub(super) fn find(&self, namespace: Namespace, ns: &str, name: &str) -> Option<Entry> {
        self.named_in(ns, name)?.find(namespace)
    }

    fn in_prelude(&self, namespace: Namespace, name: &str) -> Option<Meaning> {
        let entry = self.find(namespace, PRELUDE, name).filter(|e| e.is_pub)?;
        let item = Item {
            home: Name::from(PRELUDE),
            name: Name::from(name),
        };
        Some(Meaning::Item(item, entry))
    }

    /// What the name `n` means where the context is, in one namespace. A name that a macro's
    /// template writes means what it means where the macro is declared, and only the
    /// template's own variables (macros.hygiene).
    pub(super) fn lookup(
        &self,
        ctx: &Ctx,
        namespace: Namespace,
        locals: bool,
        n: &Ident,
    ) -> Option<Meaning> {
        let name = &*n.name;
        let (home, scope) = self.home(n.at);
        let user = self.mark_of(n.at) == 0;
        let item = |name: &str| Item {
            home,
            name: Name::from(name),
        };
        match namespace {
            Namespace::Types => {
                let param = ctx.type_params.iter().rev().find(|(p, _)| &**p == name);
                if let Some((_, v)) = param.filter(|_| user) {
                    Some(Meaning::Param(v.clone()))
                } else if scope.shadowed_types.contains(name) || scope.unknown_types.contains(name)
                {
                    Some(Meaning::Broken)
                } else if let Some(&entry) = scope.types.get(name) {
                    Some(Meaning::Item(item(name), entry))
                } else {
                    self.in_prelude(Namespace::Types, name)
                }
            }
            Namespace::Values => {
                let key = self.key(n);
                let local = locals
                    .then(|| self.scope.iter().rev().find(|(k, _)| *k == key))
                    .flatten();
                if let Some((_, v)) = local {
                    Some(v.map_or(Meaning::Broken, Meaning::Local))
                } else if let Some(value) = self.value_param_named(ctx, n) {
                    // A value parameter hides an item of its name
                    // (generics.value-parameters-in-body).
                    Some(value)
                } else if scope.shadowed_values.contains(name)
                    || scope.unknown_values.contains(name)
                {
                    Some(Meaning::Broken)
                } else {
                    match scope.values.get(name) {
                        Some(Value::Item(entry)) => Some(Meaning::Item(item(name), *entry)),
                        Some(Value::Import(ns)) => Some(Meaning::Namespace(*ns)),
                        Some(Value::ImportError) => Some(Meaning::Broken),
                        // macros.failed-uses: after a pattern with a failed use, a name that
                        // names nothing has the error type.
                        None => self.in_prelude(Namespace::Values, name).or_else(|| {
                            (locals && self.after_failed_use()).then_some(Meaning::Broken)
                        }),
                    }
                }
            }
        }
    }

    /// Resolves the names of `path` for as long as they name namespaces, the first name
    /// lexically and each later one in the namespace before it (program.namespaces). Returns what
    /// the first name that isn't a namespace means, that name, and how many names follow it.
    ///
    /// A name followed by more names is read as a type first, then as a value
    /// (declarations.name-lookup). The last name is read in `want`, and named `noun` in errors.
    /// Naming an item of another module records a reference from the path's first name, and needs
    /// the item to be visible (program.visibility). An item that isn't visible means nothing, so
    /// the names after it cause no further error (errors.root-causes).
    pub(super) fn walk(
        &mut self,
        ctx: &Ctx,
        want: Namespace,
        noun: &str,
        locals: bool,
        path: &[Ident],
    ) -> (Meaning, usize) {
        let Some((first, rest)) = path.split_first() else {
            return (Meaning::Broken, 0);
        };
        let meaning = if &*first.name == "Self" {
            Some(self.self_type(ctx, first.at))
        } else if rest.is_empty() {
            self.lookup(ctx, want, locals, first)
        } else {
            self.lookup(ctx, Namespace::Types, locals, first)
                .or_else(|| self.lookup(ctx, Namespace::Values, locals, first))
        };
        match meaning {
            Some(Meaning::Namespace(ns)) if !rest.is_empty() => {
                self.inside(want, noun, first.at, &ns, path, 1)
            }
            Some(m) => (m, 0),
            None => {
                let namespace = if rest.is_empty() {
                    want
                } else {
                    Namespace::Types
                };
                match self.lookup(ctx, namespace.other(), true, first) {
                    Some(Meaning::Broken) => {}
                    Some(m) => {
                        let message = format!("`{}` is {}, not {noun}", first.name, m.describe());
                        self.error(codes::E0212, first.at, message);
                    }
                    None => {
                        let d = self.unknown_first(ctx, namespace, locals, path);
                        let d = self.through_splice(d, first);
                        self.unknown_name(first.name.to_string(), d);
                    }
                }
                (Meaning::Broken, path.len() - 1)
            }
        }
    }

    /// The rest of [`Self::walk`], from the name at `index`, inside the namespace `ns`.
    pub(super) fn inside(
        &mut self,
        want: Namespace,
        noun: &str,
        start: TextRange,
        ns: &str,
        path: &[Ident],
        index: usize,
    ) -> (Meaning, usize) {
        let s = &path[index];
        let last = index + 1 == path.len();
        let namespace = if last { want } else { Namespace::Types };
        let found = self.find(namespace, ns, &s.name).or_else(|| {
            (!last)
                .then(|| self.find(Namespace::Values, ns, &s.name))
                .flatten()
        });
        let child = format!("{ns}.{}", s.name);
        let unknown = |r: &Self| {
            r.named_in(ns, &s.name)
                .is_some_and(|named| named.unknown(namespace))
        };
        match found {
            Some(_) if unknown(self) => (Meaning::Broken, path.len() - 1),
            Some(entry) => {
                if self.accessible(start, ns, s, entry) {
                    let item = Item {
                        home: Name::from(ns),
                        name: s.name,
                    };
                    (Meaning::Item(item, entry), index)
                } else {
                    (Meaning::Broken, path.len() - 1)
                }
            }
            None if self.map.is_namespace(&child) => {
                if last {
                    (Meaning::Namespace(Name::from(child)), index)
                } else {
                    self.inside(want, noun, start, &child, path, index + 1)
                }
            }
            None if self.map.is_unnamed(&child) => (Meaning::Broken, path.len() - 1),
            None => {
                let (code, message) = match self.find(namespace.other(), ns, &s.name) {
                    Some(entry) => (
                        codes::E0212,
                        format!("`{child}` is {}, not {noun}", entry.kind.describe()),
                    ),
                    None if self.map.is_module(ns) => (
                        codes::E0211,
                        format!("module `{ns}` has no item `{}`", s.name),
                    ),
                    None => (codes::E0211, format!("there is no module `{child}`")),
                };
                let visible = self.items_of(ns, namespace);
                let d = Diagnostic::new(code, s.at, message);
                let names = visible.iter().map(|n| &**n);
                let d = d.with_closest(AlternativeKind::Name, s.at, &s.name, names);
                if code == codes::E0211 {
                    let written: Vec<&str> = path[..=index].iter().map(|n| &*n.name).collect();
                    self.unknown_name(written.join("."), d);
                } else {
                    self.diagnostics.push(d);
                }
                (Meaning::Broken, path.len() - 1)
            }
        }
    }

    /// The names that a lookup of one name where the context is finds, in one namespace, among
    /// which a failed lookup finds the closest (goal closest-candidates).
    pub(super) fn names_here(&self, ctx: &Ctx, namespace: Namespace, locals: bool) -> Vec<Name> {
        let scope = self.own;
        let mut names = Vec::new();
        match namespace {
            Namespace::Types => {
                names.extend(ctx.type_params.iter().map(|(n, _)| *n));
                names.extend(scope.types.keys().copied());
            }
            Namespace::Values => {
                if locals {
                    names.extend(self.scope.iter().map(|(n, _)| *n));
                }
                names.extend(scope.values.keys().copied());
            }
        }
        names.extend(self.items_of(PRELUDE, namespace));
        names
    }

    /// The names of the items of module `ns`, in one namespace, that may be named here.
    fn items_of(&self, ns: &str, namespace: Namespace) -> Vec<Name> {
        let Some(scope) = self.scope_of(ns) else {
            return Vec::new();
        };
        let visible = |e: &Entry| e.is_pub || ns == &*self.module.name;
        match namespace {
            Namespace::Types => scope
                .types
                .iter()
                .filter(|(_, e)| visible(e))
                .map(|(n, _)| *n)
                .collect(),
            Namespace::Values => scope
                .values
                .iter()
                .filter(|(_, v)| matches!(v, Value::Item(e) if visible(e)))
                .map(|(n, _)| *n)
                .collect(),
        }
    }

    /// Whether the item `name` of module `ns` may be named here. Naming another module's item
    /// is a reference to that module.
    fn accessible(&mut self, start: TextRange, ns: &str, name: &Ident, entry: Entry) -> bool {
        // A template's names are its module's, private ones included (macros.hygiene).
        if ns == &*self.module.name || ns == &*self.home(start).0 {
            return true;
        }
        self.references.push((Name::from(ns), start));
        if !entry.is_pub {
            let message = format!("`{ns}.{}` is private to module `{ns}`", name.name);
            self.error(codes::E0213, name.at, message);
        }
        entry.is_pub
    }

    /// The meaning of a path that must end at its last name, since only modules hold items in
    /// a path, and the index of the name it is the meaning of.
    pub(super) fn walk_to_end(
        &mut self,
        ctx: &Ctx,
        want: Namespace,
        noun: &str,
        path: &[Ident],
    ) -> (Meaning, usize) {
        match self.walk(ctx, want, noun, false, path) {
            (Meaning::Broken, last) => (Meaning::Broken, last),
            (m, last) if last + 1 >= path.len() => (m, last),
            (m, last) => {
                let name = &path[last];
                let message = format!("`{}` is {}, not a module", name.name, m.describe());
                self.error(codes::E0212, name.at, message);
                (Meaning::Broken, last)
            }
        }
    }

    /// An unknown name of a quote that names a local of the code around it, which the quote
    /// names through a splice, `$n` (macros.quote-hygiene).
    pub(super) fn through_splice(&self, d: Diagnostic, n: &Ident) -> Diagnostic {
        if !self
            .quoting
            .as_ref()
            .is_some_and(|names| names.contains(&n.name))
        {
            return d;
        }
        let mut d = d;
        d.message = format!(
            "{}: `{}` is a local of the macro's code, which a quote names with `${}`",
            d.message, n.name, n.name
        );
        let fix = stilt_diag::Fix::new(
            format!("splice the local: `${}`", n.name),
            vec![stilt_diag::Edit::insert(n.at.start(), "$")],
        );
        d.with_fix(fix)
    }

    pub(super) fn wrong_kind(&mut self, name: &Ident, m: &Meaning, noun: &str) {
        let message = format!("`{}` is {}, not {noun}", name.name, m.describe());
        self.error(codes::E0212, name.at, message);
    }
}
