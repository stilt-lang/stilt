//! The first step of name resolution: the modules of a program and of the standard library,
//! and the scope of each, the names it declares and those its `use` declarations bind, in a type
//! namespace and a value namespace (program.module-names, program.what-use-binds and
//! program.namespaces; declarations.namespaces and declarations.unique-names).
//!
//! The standard library's modules are found first, since it names no module of a program, so
//! that an edit to a program leaves them as they are. The modules' names come from their files'
//! places alone, each module's scope is a query of its own, and so is what it says of each name
//! another module looks up there ([`named`]), so that an edit that adds an item resolves again
//! only the modules that look that name up in the edited one (goal edit-to-diagnostics).

mod build;
mod imports;
mod names;
mod paths;
pub mod view;

use std::collections::{HashMap, HashSet};
use stilt_diag::{Code, codes};

use stilt_db::{Db, Program, SourceFile};

use crate::Anchor;
use crate::hir::Name;
use crate::items::item_tree;
use build::build_scope;
pub use names::{Named, named};
use paths::{dotted, prefixes, valid_module_path};
use view::view_of;

/// The module that holds the prelude and the built-in types (program.prelude-names).
pub const PRELUDE: &str = "std.prelude";

pub use stilt_syntax::{PRIMITIVE_TYPES, is_primitive};

/// What kind of item a name in a scope is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Kind {
    /// A type.
    Type,
    /// A trait.
    Trait,
    /// A function.
    Fn,
    /// A constant.
    Const,
    /// A variant, in the value namespace.
    Variant,
    /// A macro (macros.syntax-declarations).
    Macro,
    /// A procedural macro (macros.procedural-declarations), named only through `meta use`.
    Proc,
    /// An effect (handlers.declaring-effect), in the type namespace.
    Effect,
}

impl Kind {
    /// The kind, as errors name it.
    #[must_use]
    pub fn describe(self) -> &'static str {
        match self {
            Self::Type => "a type",
            Self::Trait => "a trait",
            Self::Fn => "a function",
            Self::Const => "a constant",
            Self::Variant => "a variant",
            Self::Macro => "a macro",
            Self::Proc => "a procedural macro",
            Self::Effect => "an effect",
        }
    }

    /// Whether items of the kind are in the type namespace.
    #[must_use]
    pub fn is_type(self) -> bool {
        matches!(self, Self::Type | Self::Trait | Self::Effect)
    }
}

/// An item: what it is, whether other modules may name it, and, for a type, its number of type
/// parameters. A variant has the visibility of its type (program.visibility).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Entry {
    /// What it is.
    pub kind: Kind,
    /// Whether other modules may name it.
    pub is_pub: bool,
    /// For a type, its number of type parameters.
    pub arity: u32,
    /// Whether a type's last parameter is a pack, which its arguments after the others give
    /// (variadics.packs).
    pub pack: bool,
}

/// A name in a module's value namespace: one of its items, or a name that a `use` declaration
/// binds to a namespace. A `use` with an error binds its name to nothing, and uses of that name
/// have the error type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    /// An item.
    Item(Entry),
    /// A namespace that a `use` binds the name to.
    Import(Name),
    /// A name that a `use` with an error binds.
    ImportError,
}

/// The names a module declares and imports.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Scope {
    /// The type namespace.
    pub types: HashMap<Name, Entry>,
    /// The value namespace.
    pub values: HashMap<Name, Value>,
    /// The names of the types that clash with prelude items. Uses of them in the module have
    /// the error type (program.prelude-names).
    pub shadowed_types: HashSet<Name>,
    /// The same for values.
    pub shadowed_values: HashSet<Name>,
    /// The names of the types and traits that a part with a syntax error declares only by name.
    /// Every use of them, in any module, has the error type (errors.declarations-with-errors and
    /// errors.unknown-names).
    pub unknown_types: HashSet<Name>,
    /// The same for functions and constants.
    pub unknown_values: HashSet<Name>,
    /// The shape of each trait it declares (traits.trait-parameters and traits.receiver-types).
    pub traits: HashMap<Name, crate::items::TraitShape>,
    /// The value parameters of each type it declares that has some (generics.value-parameters).
    pub value_params: HashMap<Name, crate::items::ValueParams>,
    /// The modules that its `meta use` declarations name, by the names they bind, whose
    /// procedural macros alone they make available (macros.meta-use).
    pub metas: HashMap<Name, Name>,
}

impl Scope {
    /// Whether the scope declares `name` only by name, in `namespace` or, for a name that
    /// more names follow, in either (errors.unknown-names and errors.declarations-with-errors).
    #[must_use]
    pub fn unknown(&self, namespace: Namespace, name: &str) -> bool {
        match namespace {
            Namespace::Types => {
                self.unknown_types.contains(name) || self.unknown_values.contains(name)
            }
            Namespace::Values => self.unknown_values.contains(name),
        }
    }

    /// The item `name` in one namespace, if the scope declares one.
    #[must_use]
    pub fn find(&self, namespace: Namespace, name: &str) -> Option<Entry> {
        match namespace {
            Namespace::Types => self.types.get(name).copied(),
            Namespace::Values => match self.values.get(name) {
                Some(Value::Item(entry)) => Some(*entry),
                Some(Value::Import(_) | Value::ImportError) | None => None,
            },
        }
    }
}

/// A namespace of a scope (program.namespaces).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Namespace {
    /// Types, traits and effects.
    Types,
    /// Functions, constants, variants, macros and namespaces.
    Values,
}

impl Namespace {
    /// The other namespace.
    #[must_use]
    pub fn other(self) -> Self {
        match self {
            Self::Types => Self::Values,
            Self::Values => Self::Types,
        }
    }
}

/// A diagnostic found without positions, at a part of its module's items that the module's
/// resolution places.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Problem {
    pub(crate) code: Code,
    pub(crate) at: Anchor,
    pub(crate) message: String,
    /// Each fix's title, and the text that replaces the span it is placed at.
    pub(crate) fixes: Vec<(String, String)>,
}

/// A module of the program or of the standard library.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Module {
    /// The module's dotted name in the program, or its file's path when the name is invalid
    /// (program.report-paths and program.module-names).
    pub name: Name,
    /// Its dotted name in its package, which its header writes (packages.modules-of-dependencies).
    pub local: Name,
    /// Its file.
    pub file: SourceFile,
    /// Whether other modules can name it, which they can when its name is valid.
    pub valid: bool,
    /// Whether it is a module of the standard library.
    pub std: bool,
    /// The error in its name, if it has one.
    pub(crate) problems: Vec<Problem>,
}

/// A module's scope, with its errors.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ModuleScope {
    /// The names it declares and imports.
    pub scope: Scope,
    pub(crate) problems: Vec<Problem>,
}

/// The modules of a program and of the standard library, by name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefMap {
    /// The standard library's modules, then the program's, each in the order of their files.
    pub modules: Vec<Module>,
    /// The modules that a program can name, by name.
    by_name: HashMap<Name, usize>,
    /// Their names, and every prefix of one.
    namespaces: HashSet<Name>,
    /// The names, and their prefixes, of modules whose names are invalid and that aren't
    /// namespaces. Naming one is no further error (program.module-names).
    unnamed: HashSet<Name>,
}

impl DefMap {
    /// The module of this name, if a program can name it.
    #[must_use]
    pub fn module(&self, name: &str) -> Option<&Module> {
        self.by_name.get(name).map(|&i| &self.modules[i])
    }

    /// Whether a program can name a module of this name.
    #[must_use]
    pub fn is_module(&self, name: &str) -> bool {
        self.by_name.contains_key(name)
    }

    /// Whether `name` is a module's name, or a prefix of one.
    #[must_use]
    pub fn is_namespace(&self, name: &str) -> bool {
        self.namespaces.contains(name)
    }

    /// Whether `name` is the name, or a prefix of it, of a module whose name is invalid.
    #[must_use]
    pub fn is_unnamed(&self, name: &str) -> bool {
        self.unnamed.contains(name)
    }

    /// The module of a file.
    #[must_use]
    pub fn of_file(&self, file: SourceFile) -> Option<&Module> {
        self.modules.iter().find(|m| m.file == file)
    }
}

/// The standard library's modules, which every program has.
#[salsa::tracked(returns(ref))]
pub fn std_def_map(db: &dyn Db, program: Program) -> DefMap {
    let mut map = DefMap {
        modules: Vec::new(),
        by_name: HashMap::new(),
        namespaces: HashSet::new(),
        unnamed: HashSet::new(),
    };
    for &file in program.std(db) {
        let name = Name::from(dotted(file.module_path(db)));
        map.namespaces.extend(prefixes(&name));
        map.by_name.insert(name, map.modules.len());
        map.modules.push(Module {
            local: name,
            name,
            file,
            valid: true,
            std: true,
            problems: Vec::new(),
        });
    }
    map
}

/// The modules of a program and of the standard library.
#[salsa::tracked(returns(ref))]
pub fn def_map(db: &dyn Db, program: Program) -> DefMap {
    let mut map = std_def_map(db, program).clone();
    let mut unnamed = Vec::new();
    for &file in program.files(db) {
        let path = file.module_path(db);
        let segments = local_segments(db, program, file);
        let local = Name::from(dotted(&segments));
        let first = segments.first().map_or("", String::as_str);
        let dependency = dependency_named(db, program, file, first);
        let named = valid_module_path(&segments) && !dependency;
        // The module of a file that isn't lexed can't be named either, which is no error of its
        // name (errors.invalid-source-text).
        let valid = named && !stilt_db::unreadable(db, file);
        let mut problems = Vec::new();
        let name = if valid {
            let name = Name::from(dotted(path));
            map.namespaces.extend(prefixes(&name));
            map.by_name.insert(name, map.modules.len());
            name
        } else {
            if !named {
                let message = if dependency {
                    format!(
                        "`{local}` is not a valid module name: the package depends on a package \
                     `{first}`"
                    )
                } else {
                    format!("`{local}` is not a valid module name")
                };
                problems.push(Problem {
                    fixes: Vec::new(),
                    code: codes::E0200,
                    at: Anchor::FileStart,
                    message,
                });
            }
            unnamed.extend(prefixes(&dotted(path)).collect::<Vec<_>>());
            Name::from(file.path(db).as_str())
        };
        map.modules.push(Module {
            local,
            name,
            file,
            valid,
            std: false,
            problems,
        });
    }
    map.unnamed = unnamed
        .into_iter()
        .filter(|name| !map.namespaces.contains(name))
        .collect();
    map
}

/// The dotted name of a file's module in its package: its name in the program without the
/// package's prefix, `main` for a dependency's root module (packages.modules-of-dependencies).
pub fn local_path(db: &dyn Db, program: Program, file: SourceFile) -> Name {
    Name::from(dotted(&local_segments(db, program, file)))
}

/// The segments of [`local_path`], which may not be valid names.
fn local_segments(db: &dyn Db, program: Program, file: SourceFile) -> Vec<String> {
    let path = file.module_path(db);
    let package = stilt_db::package_of(db, program, file);
    let prefix = program
        .packages(db)
        .list
        .get(package)
        .and_then(|p| p.prefix.as_deref());
    match (prefix, path.split_first()) {
        (Some(prefix), Some((first, rest))) if first == prefix => {
            if rest.is_empty() {
                vec!["main".to_owned()]
            } else {
                rest.to_vec()
            }
        }
        _ => path.clone(),
    }
}

/// Whether `first` is the name of a dependency that the manifest of `file`'s package names, so
/// that no module of the package can have it as its first segment (packages.imports).
fn dependency_named(db: &dyn Db, program: Program, file: SourceFile, first: &str) -> bool {
    let package = stilt_db::package_of(db, program, file);
    program
        .packages(db)
        .list
        .get(package)
        .is_some_and(|p| p.deps.iter().any(|d| d.name == first))
}

/// The modules that `file` of `program` resolves among: the standard library's alone for one
/// of its files, since it names no module of a program.
pub(crate) fn modules_of(db: &dyn Db, program: Program, file: SourceFile) -> &DefMap {
    if program.std(db).contains(&file) {
        std_def_map(db, program)
    } else {
        def_map(db, program)
    }
}

/// The scope of the module of a file of the program or of the standard library.
#[salsa::tracked(returns(ref))]
pub fn module_scope(db: &dyn Db, program: Program, file: SourceFile) -> ModuleScope {
    let map = modules_of(db, program, file);
    let module = map
        .of_file(file)
        .expect("every file of the program has a module");
    let tree = item_tree(db, file);
    let view = view_of(db, program, file);
    // Read only for a `use` that names no namespace, so an edit of another module's items
    // checks this one again only when one of its imports has that error (E0230).
    let items_of = |module: &str, name: &str| {
        map.module(module)
            .is_some_and(|m| imports::declares(item_tree(db, m.file), name))
    };
    let (scope, problems) = if module.std {
        let none = PreludeNames::default();
        let found = build_scope(map, view, &none, &*module.name == PRELUDE, tree, &items_of);
        debug_assert_eq!(found.1, [], "the standard library has errors");
        found
    } else {
        build_scope(
            map,
            view,
            prelude_names(db, program),
            false,
            tree,
            &items_of,
        )
    };
    ModuleScope { scope, problems }
}

/// The public names of the prelude in each namespace, which a program's own items can't take
/// in the same namespace (program.prelude-names).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct PreludeNames {
    /// Its types and traits.
    pub(crate) types: HashSet<Name>,
    /// Its variants and functions.
    pub(crate) values: HashSet<Name>,
}

impl PreludeNames {
    /// The names of one namespace.
    pub(crate) fn of(&self, namespace: Namespace) -> &HashSet<Name> {
        match namespace {
            Namespace::Types => &self.types,
            Namespace::Values => &self.values,
        }
    }
}

#[salsa::tracked(returns(ref))]
fn prelude_names(db: &dyn Db, program: Program) -> PreludeNames {
    let Some(prelude) = std_def_map(db, program).module(PRELUDE) else {
        return PreludeNames::default();
    };
    let scope = &module_scope(db, program, prelude.file).scope;
    let types = scope.types.iter().filter(|(_, e)| e.is_pub);
    let values = scope.values.iter().filter_map(|(name, v)| match v {
        Value::Item(e) if e.is_pub => Some(*name),
        _ => None,
    });
    PreludeNames {
        types: types.map(|(name, _)| *name).collect(),
        values: values.collect(),
    }
}
