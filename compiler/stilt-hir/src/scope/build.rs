//! The scope of one module (program.prelude-names; declarations.namespaces).

use std::collections::HashSet;
use stilt_diag::{Code, closest, codes};

use super::imports::{ItemsOf, item_import};
use super::paths::dotted;
use super::view::{Lookup, View};
use super::{
    DefMap, Entry, Kind, Namespace, PRIMITIVE_TYPES, PreludeNames, Problem, Scope, Value,
    is_primitive,
};
use crate::Anchor;
use crate::hir::Name;
use crate::items::{DeclSummary, ItemSummary, ItemTree};

/// The types of the prelude that have no declaration, with their numbers of type parameters.
fn builtin_types() -> impl Iterator<Item = (&'static str, u32)> {
    PRIMITIVE_TYPES
        .into_iter()
        .map(|name| (name, 0))
        .chain([("Never", 0), ("List", 1), ("Map", 2)])
}

/// The scope of a module. Every name it declares is checked against the primitive types
/// (lexical.primitive-type-names), the prelude's names of its namespace (program.prelude-names) and
/// the module's other names (declarations.unique-names). Of two items with the same name, the first
/// is the one names refer to (errors.several-places).
pub(super) fn build_scope(
    map: &DefMap,
    view: &View,
    prelude_names: &PreludeNames,
    is_prelude: bool,
    tree: &ItemTree,
    items_of: ItemsOf<'_>,
) -> (Scope, Vec<Problem>) {
    let mut declarer = Declarer {
        scope: Scope::default(),
        problems: Vec::new(),
        tests: HashSet::new(),
        prelude_names,
        is_prelude,
        items_of,
    };
    if is_prelude {
        for (name, arity) in builtin_types() {
            let entry = Entry {
                kind: Kind::Type,
                is_pub: true,
                arity,
                pack: false,
            };
            declarer.scope.types.insert(Name::from(name), entry);
        }
    }
    for (i, item) in (0..).zip(&tree.items) {
        match item {
            ItemSummary::Use(path) => declarer.import(map, view, i, path),
            ItemSummary::MetaUse(path) => declarer.meta_import(map, view, i, path),
            ItemSummary::Decl {
                is_pub,
                kind,
                unknown,
            } => {
                declarer.decl(i, *is_pub, kind);
                if *unknown {
                    declarer.unknown(kind);
                }
            }
            ItemSummary::Impl => {}
        }
    }
    (declarer.scope, declarer.problems)
}

/// Declares the names of a module in its scope, reporting clashes.
struct Declarer<'a> {
    scope: Scope,
    problems: Vec<Problem>,
    /// The names of the module's tests, which are in no namespace but are unique.
    tests: HashSet<String>,
    prelude_names: &'a PreludeNames,
    is_prelude: bool,
    /// What each module declares, which a `use` that names no namespace may name (E0230).
    items_of: ItemsOf<'a>,
}

impl Declarer<'_> {
    /// The `use` declaration at `i`, which binds the last name of its path to a namespace, by
    /// its name in the program (packages.modules-of-dependencies).
    fn import(&mut self, map: &DefMap, view: &View, i: u32, path: &[Name]) {
        let Some(last) = path.last() else { return };
        let namespace = Name::from(dotted(path));
        let value = match view.lookup(map, &namespace) {
            Lookup::Found(name) => Value::Import(name),
            Lookup::Unnamed => Value::ImportError,
            Lookup::Foreign(package) => {
                let other = view.other(&package).cloned().unwrap_or_default();
                let message = format!(
                    "`{package}` is a dependency of `{}`, not of this package: add `{package} = \
                     {}` to its stilt.toml",
                    other.by, other.entry
                );
                self.problem(codes::E0218, Anchor::Item(i), message);
                Value::ImportError
            }
            Lookup::Missing => {
                self.missing(map, view, i, path, false);
                Value::ImportError
            }
        };
        // A `use` with an error binds a name that no module can have, so the name isn't checked.
        let checked = value != Value::ImportError;
        self.value(*last, Anchor::Item(i), checked, value);
    }

    /// The `meta use` declaration at `i`, which binds the last name of its path to a module whose
    /// procedural macros it makes available, apart from the names `use` binds (macros.meta-use).
    /// Two that bind one name clash, as two `use` declarations do (declarations.unique-names).
    fn meta_import(&mut self, map: &DefMap, view: &View, i: u32, path: &[Name]) {
        let Some(last) = path.last() else { return };
        let namespace = Name::from(dotted(path));
        let found = match view.lookup(map, &namespace) {
            Lookup::Found(name) => Some(name),
            Lookup::Unnamed => None,
            Lookup::Foreign(package) => {
                let other = view.other(&package).cloned().unwrap_or_default();
                let message = format!(
                    "`{package}` is a dependency of `{}`, not of this package: add `{package} = \
                     {}` to its stilt.toml",
                    other.by, other.entry
                );
                self.problem(codes::E0218, Anchor::Item(i), message);
                None
            }
            Lookup::Missing => {
                self.missing(map, view, i, path, true);
                None
            }
        };
        if self.scope.metas.contains_key(last) {
            let message = format!("`{last}` is already named by a `meta use` in this module");
            self.problem(codes::E0208, Anchor::Item(i), message);
        } else if let Some(ns) = found {
            self.scope.metas.insert(*last, ns);
        }
    }

    /// The error of a `use`, or with `meta` a `meta use`, that names no module: E0230 when it
    /// names an item of one, with the module as its fix, and otherwise E0205, with the closest
    /// modules that it can name (goal closest-candidates).
    fn missing(&mut self, map: &DefMap, view: &View, i: u32, path: &[Name], meta: bool) {
        if let Some((message, fix)) = item_import(map, view, path, meta, self.items_of) {
            self.problem(codes::E0230, Anchor::Item(i), message);
            let problem = self.problems.last_mut().expect("the problem is reported");
            problem.fixes.push(fix);
            return;
        }
        let namespace = dotted(path);
        let deps = view.dependencies();
        let message = match deps.as_slice() {
            [] => format!("there is no module `{namespace}`"),
            [one] => format!(
                "there is no module `{namespace}`, in this package or in its dependency `{one}`"
            ),
            [init @ .., last] => format!(
                "there is no module `{namespace}`, in this package or in its dependencies {} \
                 and `{last}`",
                init.iter()
                    .map(|d| format!("`{d}`"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        };
        self.problem(codes::E0205, Anchor::Item(i), message);
        let named = view.named_modules(map);
        let fixes = closest(&namespace, named.iter().map(|m| &**m))
            .into_iter()
            .map(|m| (format!("import `{m}`"), format!("use {m}")));
        self.problems
            .last_mut()
            .expect("the problem is reported")
            .fixes
            .extend(fixes);
    }

    /// The declaration at `i`, with its variants.
    fn decl(&mut self, i: u32, is_pub: bool, kind: &DeclSummary) {
        let entry = |kind, arity, pack| Entry {
            kind,
            is_pub,
            arity,
            pack,
        };
        let item = |kind| Value::Item(entry(kind, 0, false));
        match kind {
            DeclSummary::Fn(name) => self.value(*name, Anchor::Name(i), true, item(Kind::Fn)),
            DeclSummary::Const(name) => self.value(*name, Anchor::Name(i), true, item(Kind::Const)),
            DeclSummary::Macro(name) => self.value(*name, Anchor::Name(i), true, item(Kind::Macro)),
            DeclSummary::Proc(name) => self.value(*name, Anchor::Name(i), true, item(Kind::Proc)),
            DeclSummary::Type {
                name,
                arity,
                pack,
                variants,
                values,
            } => {
                if !values.is_empty() && !self.scope.types.contains_key(name) {
                    self.scope.value_params.insert(*name, values.clone());
                }
                self.ty(*name, Anchor::Name(i), entry(Kind::Type, *arity, *pack));
                for (j, variant) in (0..).zip(variants) {
                    self.value(*variant, Anchor::Variant(i, j), true, item(Kind::Variant));
                }
            }
            DeclSummary::Effect(name, arity) => {
                self.ty(*name, Anchor::Name(i), entry(Kind::Effect, *arity, false));
            }
            DeclSummary::Trait(name, shape) => {
                if !self.scope.types.contains_key(name) {
                    self.scope.traits.insert(*name, shape.clone());
                }
                self.ty(*name, Anchor::Name(i), entry(Kind::Trait, 0, false));
            }
            DeclSummary::Test(name) => {
                if !self.tests.insert(name.clone()) {
                    let message =
                        format!("a test named {name:?} is already declared in this module");
                    self.problem(codes::E0208, Anchor::Item(i), message);
                }
            }
        }
    }

    /// A declaration that a part with a syntax error leaves with only its name, every use of which
    /// has the error type (errors.declarations-with-errors). A procedural macro stays one: it
    /// expands no use, since its module has an error, but a use that no procedural macro may have,
    /// as a value or in its own module, is still E0212 (macros.meta-use and
    /// macros.expansion-order).
    fn unknown(&mut self, kind: &DeclSummary) {
        match kind {
            DeclSummary::Fn(name) | DeclSummary::Const(name) | DeclSummary::Macro(name) => {
                self.scope.unknown_values.insert(*name);
            }
            DeclSummary::Type { name, .. }
            | DeclSummary::Trait(name, _)
            | DeclSummary::Effect(name, _) => {
                self.scope.unknown_types.insert(*name);
            }
            DeclSummary::Proc(_) | DeclSummary::Test(_) => {}
        }
    }

    fn problem(&mut self, code: Code, at: Anchor, message: String) {
        self.problems.push(Problem {
            code,
            at,
            message,
            fixes: Vec::new(),
        });
    }

    fn ty(&mut self, name: Name, at: Anchor, entry: Entry) {
        if self.scope.types.contains_key(&name) {
            self.defined_twice(name, at);
        } else {
            self.check(Namespace::Types, name, at);
            self.scope.types.insert(name, entry);
        }
    }

    fn value(&mut self, name: Name, at: Anchor, checked: bool, value: Value) {
        if self.scope.values.contains_key(&name) {
            self.defined_twice(name, at);
        } else {
            if checked {
                self.check(Namespace::Values, name, at);
            }
            self.scope.values.insert(name, value);
        }
    }

    fn defined_twice(&mut self, name: Name, at: Anchor) {
        let message = format!("`{name}` is already defined in this module");
        self.problem(codes::E0208, at, message);
    }

    fn check(&mut self, namespace: Namespace, name: Name, at: Anchor) {
        if is_primitive(&name) {
            self.problem(
                codes::E0210,
                at,
                format!("`{name}` is a primitive type name"),
            );
        } else if !self.is_prelude && self.prelude_names.of(namespace).contains(&name) {
            let message = format!("`{name}` is the name of a prelude item");
            self.problem(codes::E0209, at, message);
            match namespace {
                Namespace::Types => self.scope.shadowed_types.insert(name),
                Namespace::Values => self.scope.shadowed_values.insert(name),
            };
        }
    }
}
