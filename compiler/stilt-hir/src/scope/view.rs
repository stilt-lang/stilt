//! What the `use` declarations of a package's modules can name (packages.modules-of-dependencies,
//! packages.imports and packages.manifests-with-errors): the package's own modules, by their names
//! in it; `std`; and the packages its manifest names as dependencies, by their names. A module of
//! another package of the program is E0218.
//!
//! A path written in a package is translated, once, into the name of a namespace of the program
//! (packages.modules-of-dependencies), so that everything after a `use` reads the program's names.

use std::collections::{HashMap, HashSet};

use stilt_db::{Db, Program, SourceFile};

use super::DefMap;
use super::paths::prefixes;
use crate::hir::Name;

/// What a package's modules can name.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct View {
    /// The names, in the package, of its own modules and their prefixes, with their names in
    /// the program.
    own: HashMap<Name, Name>,
    /// The names, and their prefixes, of its own modules whose names are invalid and that
    /// aren't namespaces.
    own_unnamed: HashSet<Name>,
    /// Its dependencies by name, each with the first segment of its modules' names in the
    /// program, or `None` when its entry has an error.
    deps: HashMap<Name, Option<Name>>,
    /// Whether its manifest declares its dependencies (packages.manifests-with-errors).
    declares: bool,
    /// The other packages of the program that it doesn't depend on, by name.
    others: HashMap<Name, Other>,
    /// Whether the view names what the program does: the standard library's modules, or a
    /// program without a manifest.
    whole: bool,
}

/// A package of the program that a package doesn't depend on.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Other {
    /// The first segment of its modules' names.
    prefix: Name,
    /// The first package that depends on it.
    pub by: Name,
    /// The value of the entry that would make it a dependency (packages.imports):
    /// `{ path = "deps/bytes" }`, or `{ from = "…", version = "…" }` for a fetched package.
    pub entry: String,
}

/// What a `use` names.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Lookup {
    /// The namespace of this name in the program.
    Found(Name),
    /// Nothing, because of an error elsewhere: the use has the error type, and no error of its
    /// own.
    Unnamed,
    /// A module of the package of this name, which isn't a dependency (E0218).
    Foreign(Name),
    /// No module (E0205).
    Missing,
}

impl View {
    /// The view of the whole program, for the standard library and programs without packages.
    pub(crate) fn whole() -> Self {
        Self {
            declares: true,
            whole: true,
            ..Self::default()
        }
    }

    /// What `written`, a dotted path in a `use`, names.
    #[must_use]
    pub fn lookup(&self, map: &DefMap, written: &str) -> Lookup {
        let in_program = |name: &str| {
            if map.is_namespace(name) {
                Lookup::Found(Name::from(name))
            } else if map.is_unnamed(name) {
                Lookup::Unnamed
            } else {
                Lookup::Missing
            }
        };
        let (first, rest) = written.split_once('.').unwrap_or((written, ""));
        if self.whole || first == "std" {
            return in_program(written);
        }
        if let Some(dep) = self.deps.get(first) {
            let Some(prefix) = dep else {
                return Lookup::Unnamed;
            };
            return in_program(&joined(prefix, rest));
        }
        if let Some(name) = self.own.get(written) {
            return Lookup::Found(*name);
        }
        if self.own_unnamed.contains(written) || !self.declares {
            return Lookup::Unnamed;
        }
        if let Some(other) = self.others.get(first)
            && map.is_namespace(&joined(&other.prefix, rest))
        {
            return Lookup::Foreign(Name::from(first));
        }
        Lookup::Missing
    }

    /// The package of the program named `name` that this one doesn't depend on.
    #[must_use]
    pub fn other(&self, name: &str) -> Option<&Other> {
        self.others.get(name)
    }

    /// The names of the dependencies, in order, as the message of E0205 lists them.
    #[must_use]
    pub fn dependencies(&self) -> Vec<Name> {
        let mut names: Vec<Name> = self.deps.keys().copied().collect();
        names.sort();
        names
    }

    /// The modules that a `use` of the package can name, by the names it writes them with.
    #[must_use]
    pub fn named_modules(&self, map: &DefMap) -> Vec<Name> {
        let modules = map.modules.iter().filter(|m| m.valid);
        if self.whole {
            return modules.map(|m| m.name).collect();
        }
        let mut names: Vec<Name> = self
            .own
            .iter()
            .filter(|(_, global)| map.is_module(global))
            .map(|(local, _)| *local)
            .collect();
        for m in modules {
            let (first, rest) = m.name.split_once('.').unwrap_or((&m.name, ""));
            if m.std {
                names.push(m.name);
            } else if let Some((written, _)) = self
                .deps
                .iter()
                .find(|(_, prefix)| prefix.as_deref() == Some(first))
            {
                names.push(Name::from(joined(written, rest)));
            }
        }
        names.sort();
        names
    }

    /// Whether `first` is the name of one of the package's dependencies, which no module of the
    /// package can have as its first segment (packages.imports).
    #[must_use]
    pub fn is_dependency(&self, first: &str) -> bool {
        self.deps.contains_key(first)
    }
}

fn joined(prefix: &str, rest: &str) -> String {
    if rest.is_empty() {
        prefix.to_owned()
    } else {
        format!("{prefix}.{rest}")
    }
}

/// The view of the package `package` of a program with packages.
#[salsa::tracked(returns(ref))]
pub fn package_view(db: &dyn Db, program: Program, package: u32) -> View {
    let packages = program.packages(db);
    let Some(info) = packages.list.get(package as usize) else {
        return View::whole();
    };
    if info.manifest.is_none() {
        return View::whole();
    }
    let prefix_of = |i: usize| -> Name {
        let p = &packages.list[i];
        Name::from(p.prefix.as_deref().or(p.name.as_deref()).unwrap_or(""))
    };
    let deps: HashMap<Name, Option<Name>> = info
        .deps
        .iter()
        .map(|d| (Name::from(d.name.as_str()), d.package.map(prefix_of)))
        .collect();
    let mut view = View {
        declares: info.declares,
        ..View::default()
    };
    let map = super::def_map(db, program);
    let mut unnamed = Vec::new();
    for &file in &info.files {
        let Some(module) = map.of_file(file) else {
            continue;
        };
        let local = super::local_path(db, program, file);
        if module.valid {
            for local in prefixes(&local) {
                let global = match info.prefix.as_deref() {
                    None => local,
                    Some(prefix) if &*local == "main" => Name::from(prefix),
                    Some(prefix) => Name::from(joined(prefix, &local)),
                };
                view.own.insert(local, global);
            }
        } else {
            unnamed.extend(prefixes(&local).collect::<Vec<_>>());
        }
    }
    view.own_unnamed = unnamed
        .into_iter()
        .filter(|n| !view.own.contains_key(n))
        .collect();
    view.others = others(packages, package as usize, &deps);
    view.deps = deps;
    view
}

/// The packages of the program other than the root that the package `package` doesn't depend
/// on, by name.
fn others(
    packages: &stilt_db::Packages,
    package: usize,
    deps: &HashMap<Name, Option<Name>>,
) -> HashMap<Name, Other> {
    let info = &packages.list[package];
    let mut found = HashMap::new();
    for (i, other) in packages.list.iter().enumerate() {
        let name = other.name.as_deref().unwrap_or("");
        if i == package || i == 0 || name.is_empty() || deps.contains_key(name) {
            continue;
        }
        let by = (packages.list.iter())
            .find(|p| p.deps.iter().any(|d| d.package == Some(i)))
            .and_then(|p| p.name.as_deref())
            .unwrap_or("");
        let other = Other {
            prefix: Name::from(other.prefix.as_deref().unwrap_or(name)),
            by: Name::from(by),
            entry: entry(&info.shown, other),
        };
        found.insert(Name::from(name), other);
    }
    found
}

/// The view of the module of a file: its package's, or the whole program's for the standard
/// library.
pub fn view_of(db: &dyn Db, program: Program, file: SourceFile) -> &View {
    if program.std(db).contains(&file) {
        return std_view();
    }
    let package = stilt_db::package_of(db, program, file);
    package_view(db, program, u32::try_from(package).unwrap_or(u32::MAX))
}

fn std_view() -> &'static View {
    static WHOLE: std::sync::OnceLock<View> = std::sync::OnceLock::new();
    WHOLE.get_or_init(View::whole)
}

/// The value of the entry, in the manifest of the package at `from`, that names `target`: its
/// path from there, or its repository and version.
fn entry(from: &str, target: &stilt_db::PackageInfo) -> String {
    if target.fetched
        && let Some((repo, version)) = target.shown.rsplit_once('@')
    {
        return format!("{{ from = \"{repo}\", version = \"{version}\" }}");
    }
    let from: Vec<&str> = from.split('/').filter(|s| !s.is_empty()).collect();
    let to: Vec<&str> = target.shown.split('/').filter(|s| !s.is_empty()).collect();
    let common = from.iter().zip(&to).take_while(|(a, b)| a == b).count();
    let path: Vec<&str> = std::iter::repeat_n("..", from.len() - common)
        .chain(to[common..].iter().copied())
        .collect();
    format!("{{ path = \"{}\" }}", path.join("/"))
}
