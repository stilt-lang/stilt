//! The packages of a program: the root package, and those that its manifest names, directly or
//! through the manifests of the packages it names (packages.path-dependencies, versions.selection
//! and packages.one-name-one-package).
//!
//! Each entry of the root's manifest brings the packages that it reaches through entries without
//! errors. An entry whose packages hold a cycle (E0609), or a second package of a name already in
//! the program (E0606), brings none of them, and its name stands for nothing
//! (packages.manifests-with-errors). The packages that only such an entry reaches aren't part of
//! the program, so none of their diagnostics is reported.

mod walk;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use stilt_diag::{Diagnostic, codes};

use crate::fill::Unfilled;
use stilt_syntax::TextRange;

use crate::manifest::{self, Manifest};
pub use walk::Fetcher;

/// A package of the program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Package {
    /// Its directory on disk.
    pub dir: PathBuf,
    /// Its directory as reports name it, relative to the root's, with `/` as the separator:
    /// empty for the root.
    pub shown: String,
    /// The package's manifest.
    pub manifest: Manifest,
    /// The manifest's bytes, which its diagnostics are placed in.
    pub bytes: Vec<u8>,
    /// Whether it was fetched, rather than read from a directory of the user's.
    pub fetched: bool,
    /// What each entry of its manifest names, in order: the package, or `None` when the entry
    /// has an error.
    pub deps: Vec<Option<usize>>,
}

impl Package {
    /// The path that reports give its manifest.
    #[must_use]
    pub fn manifest_path(&self) -> String {
        joined(&self.shown, "stilt.toml")
    }

    /// The path that reports give a file of its `src/` folder, `a/b.lt`.
    #[must_use]
    pub fn source_path(&self, file: &str) -> String {
        joined(&self.shown, &format!("src/{file}"))
    }
}

fn joined(dir: &str, file: &str) -> String {
    if dir.is_empty() {
        file.to_owned()
    } else {
        format!("{dir}/{file}")
    }
}

/// A program's packages, the root first, and the diagnostics of their manifests, each with the
/// package whose manifest it is in.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Graph {
    /// The packages.
    pub packages: Vec<Package>,
    /// The diagnostics, each with the index of the package whose manifest it is in.
    pub problems: Vec<(usize, Diagnostic)>,
}

/// Reads the packages of the program whose root package is at `root`. Each entry that `broken`
/// names has the error it gives, and names no package.
///
/// # Errors
///
/// A message for people, when the root's manifest can't be read.
pub fn read(root: &Path, fetcher: &mut dyn Fetcher, broken: &[Unfilled]) -> Result<Graph, String> {
    let mut walk = walk::Walk::new(root, fetcher, broken)?;
    let entries = walk.loaded[0].manifest.entries.len();
    let mut graph = Graph::default();
    let mut included = vec![0];
    let mut deps: BTreeMap<usize, Vec<Option<usize>>> = BTreeMap::new();
    for e in 0..entries {
        let key = walk.loaded[0].manifest.entries[e].key;
        let Some(target) = walk.target(0, e) else {
            continue;
        };
        let closure = walk.closure(target);
        if closure.unbuildable {
            let name = &walk.loaded[0].manifest.entries[e].name;
            let message = format!(
                "`{name}` brings a fetched package whose manifest has a `path` entry or an \
                 entry without its `version` and `hash`, so it can't be built from its content"
            );
            walk.problem(0, Diagnostic::new(codes::E0601, key, message));
            walk.broken(0, e);
        } else if closure.cycle {
            let message = cycle_message(&walk, target);
            walk.problem(0, Diagnostic::new(codes::E0609, key, message));
            walk.broken(0, e);
        } else if let Some(message) = clash(&walk, &included, &closure.members) {
            walk.problem(0, Diagnostic::new(codes::E0606, key, message));
            walk.broken(0, e);
        } else {
            for m in closure.members {
                if !included.contains(&m) {
                    included.push(m);
                }
            }
        }
    }
    let index: BTreeMap<usize, usize> = (0..).zip(&included).map(|(i, &l)| (l, i)).collect();
    for &l in &included {
        let named = walk
            .targets(l)
            .map(|t| t.and_then(|t| index.get(&t).copied()));
        deps.insert(l, named.collect());
    }
    for (l, p) in std::mem::take(&mut walk.problems) {
        if let Some(&i) = index.get(&l) {
            graph.problems.push((i, p));
        }
    }
    for l in included {
        let mut package = walk.loaded[l].clone();
        package.deps = deps.remove(&l).unwrap_or_default();
        graph.packages.push(package);
    }
    Ok(graph)
}

/// Why the closure of `target` clashes with the packages in the program, if it does: two
/// packages of one name in different directories (packages.one-name-one-package).
fn clash(walk: &walk::Walk, included: &[usize], members: &[usize]) -> Option<String> {
    let mut seen: BTreeMap<&str, usize> = BTreeMap::new();
    for &m in included.iter().chain(members) {
        let Some(name) = walk.loaded[m].manifest.name.as_deref() else {
            continue;
        };
        match seen.get(name) {
            Some(&other) if other != m => {
                return Some(format!(
                    "this entry brings a second package `{name}`, in {}, beside the one in {}",
                    place(&walk.loaded[m]),
                    place(&walk.loaded[other])
                ));
            }
            _ => {
                seen.insert(name, m);
            }
        }
    }
    None
}

fn place(package: &Package) -> String {
    if package.shown.is_empty() {
        "the root directory".to_owned()
    } else {
        package.shown.clone()
    }
}

fn cycle_message(walk: &walk::Walk, target: usize) -> String {
    let name = walk.loaded[target].manifest.name.as_deref().unwrap_or("?");
    format!("`{name}` depends on itself, through the manifests of its dependencies")
}

/// The span that names a package's entry, for the errors that packages.path-dependencies,
/// versions.selection and packages.one-name-one-package place there.
#[must_use]
pub fn entry_key(graph: &Graph, package: usize, entry: usize) -> Option<TextRange> {
    let p = graph.packages.get(package)?;
    Some(p.manifest.entries.get(entry)?.key)
}

/// Reads the manifest of the package in `dir`, if it has one.
pub(crate) fn manifest_in(dir: &Path) -> Option<(Manifest, Vec<u8>)> {
    let bytes = std::fs::read(dir.join("stilt.toml")).ok()?;
    Some((manifest::read(&bytes), bytes))
}
