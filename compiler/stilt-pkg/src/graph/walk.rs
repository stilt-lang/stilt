//! Reading the packages that manifests name, each once, and the packages that an entry reaches.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Component, Path, PathBuf};

use stilt_diag::{Code, Diagnostic, Edit, Fix, codes};

use super::{Package, manifest_in};
use crate::fill::Unfilled;
use crate::manifest::{Entry, Manifest, Source};

/// Where fetched packages come from (packages.versions, packages.fetching and versions.selection).
pub trait Fetcher {
    /// The directory of the package that a `from` entry names, at the version that the program
    /// selects, and the path that reports give it; or the code and message of why it can't be
    /// had.
    ///
    /// # Errors
    ///
    /// The code and message of why the package can't be had.
    fn fetch(
        &mut self,
        from: &str,
        version: Option<&str>,
        hash: Option<&str>,
    ) -> Result<(PathBuf, String), (Code, String)>;
}

/// The packages read so far, the root first.
pub(super) struct Walk<'f> {
    pub(super) loaded: Vec<Package>,
    by_dir: BTreeMap<PathBuf, usize>,
    /// What each entry of each package names, once resolved.
    resolved: BTreeMap<(usize, usize), Option<usize>>,
    /// The fetched packages that can't be built from their content alone
    /// (packages.path-dependencies).
    unbuildable: BTreeSet<usize>,
    pub(super) problems: Vec<(usize, Diagnostic)>,
    fetcher: &'f mut dyn Fetcher,
    /// The entries with errors found before the walk, by their manifests' directories.
    broken: &'f [Unfilled],
}

/// The packages that an entry reaches, and whether they hold a cycle or one that can't be built.
pub(super) struct Closure {
    pub(super) members: Vec<usize>,
    pub(super) cycle: bool,
    pub(super) unbuildable: bool,
}

impl<'f> Walk<'f> {
    pub(super) fn new(
        root: &Path,
        fetcher: &'f mut dyn Fetcher,
        broken: &'f [Unfilled],
    ) -> Result<Self, String> {
        let (manifest, bytes) = manifest_in(root)
            .ok_or_else(|| format!("cannot read {}", root.join("stilt.toml").display()))?;
        let mut walk = Self {
            loaded: Vec::new(),
            by_dir: BTreeMap::new(),
            resolved: BTreeMap::new(),
            unbuildable: BTreeSet::new(),
            problems: Vec::new(),
            fetcher,
            broken,
        };
        walk.add(root, String::new(), manifest, bytes, false);
        Ok(walk)
    }

    fn add(
        &mut self,
        dir: &Path,
        shown: String,
        manifest: Manifest,
        bytes: Vec<u8>,
        fetched: bool,
    ) {
        let index = self.loaded.len();
        if !fetched {
            for problem in &manifest.problems {
                self.problems.push((index, problem.clone()));
            }
        }
        self.by_dir.insert(identity(dir), index);
        self.loaded.push(Package {
            dir: dir.to_path_buf(),
            shown,
            manifest,
            bytes,
            fetched,
            deps: Vec::new(),
        });
    }

    pub(super) fn problem(&mut self, package: usize, d: Diagnostic) {
        self.problems.push((package, d));
    }

    pub(super) fn broken(&mut self, package: usize, entry: usize) {
        self.resolved.insert((package, entry), None);
    }

    /// What each entry of `package` names, as far as the walk resolved it.
    pub(super) fn targets(&self, package: usize) -> impl Iterator<Item = Option<usize>> + '_ {
        let entries = self.loaded[package].manifest.entries.len();
        (0..entries).map(move |e| self.resolved.get(&(package, e)).copied().flatten())
    }

    /// The package that entry `e` of `package` names, read the first time it is asked for.
    pub(super) fn target(&mut self, package: usize, e: usize) -> Option<usize> {
        if let Some(&found) = self.resolved.get(&(package, e)) {
            return found;
        }
        let found = self.resolve(package, e);
        self.resolved.insert((package, e), found);
        found
    }

    fn resolve(&mut self, package: usize, e: usize) -> Option<usize> {
        let entry = self.loaded[package].manifest.entries[e].clone();
        let fetched = self.loaded[package].fetched;
        let dir = identity(&self.loaded[package].dir);
        let errors: Vec<Diagnostic> = (self.broken.iter())
            .filter(|b| b.entry == e && identity(&b.dir) == dir)
            .map(|b| Diagnostic::new(b.code, entry.key, b.message.clone()))
            .collect();
        if !errors.is_empty() {
            for d in errors {
                self.problem(package, d);
            }
            return None;
        }
        let (dir, shown, from_repo) = match entry.source.as_ref()? {
            Source::Path(_) if fetched => {
                self.unbuildable.insert(package);
                return None;
            }
            Source::Path(path) => {
                let dir = self.loaded[package].dir.join(path);
                let shown = normalized(&join(&self.loaded[package].shown, path));
                (dir, shown, false)
            }
            Source::From { version, hash, .. }
                if fetched && (version.is_none() || hash.is_none()) =>
            {
                self.unbuildable.insert(package);
                return None;
            }
            Source::From {
                from,
                version,
                hash,
            } => {
                let version = version.as_ref().map(|v| v.value.as_str());
                let hash = hash.as_ref().map(|h| h.value.as_str());
                let pinned = hash.map(|_| ());
                match self.fetcher.fetch(from, version, hash) {
                    Ok((dir, shown)) => (dir, shown, true),
                    Err((code, message)) => {
                        // Content that doesn't match its hash is reported at the hash.
                        let at = match (&entry.source, pinned) {
                            (Some(Source::From { hash: Some(h), .. }), Some(()))
                                if code == codes::E0602 =>
                            {
                                h.at
                            }
                            _ => entry.key,
                        };
                        if !fetched {
                            self.problem(package, Diagnostic::new(code, at, message));
                        }
                        return None;
                    }
                }
            }
        };
        let target = self.load(&dir, shown, from_repo, package, &entry)?;
        self.named(package, &entry, target)
    }

    /// The package in `dir`, read once.
    fn load(
        &mut self,
        dir: &Path,
        shown: String,
        fetched: bool,
        package: usize,
        entry: &Entry,
    ) -> Option<usize> {
        if let Some(&known) = self.by_dir.get(&identity(dir)) {
            return Some(known);
        }
        let Some((manifest, bytes)) = manifest_in(dir) else {
            let message = format!("`{}` names {shown}, which holds no stilt.toml", entry.name);
            if !self.loaded[package].fetched {
                self.problem(package, Diagnostic::new(codes::E0601, entry.key, message));
            }
            return None;
        };
        self.add(dir, shown, manifest, bytes, fetched);
        Some(self.loaded.len() - 1)
    }

    /// The target of an entry, when the target's manifest names its package as the entry does
    /// (packages.dependency-names).
    fn named(&mut self, package: usize, entry: &Entry, target: usize) -> Option<usize> {
        let found = self.loaded[target].manifest.name.clone();
        if found.as_deref() == Some(entry.name.as_str()) {
            return Some(target);
        }
        if self.loaded[package].fetched {
            self.unbuildable.insert(package);
            return None;
        }
        let manifest = self.loaded[target].manifest_path();
        let d = if let Some(name) = found {
            let message = format!(
                "this entry names `{}`, but {manifest} names its package `{name}`",
                entry.name
            );
            let fix = Fix::new(
                format!("name the entry `{name}`"),
                vec![Edit::replace(entry.key, name.clone())],
            );
            Diagnostic::new(codes::E0603, entry.key, message).with_fix(fix)
        } else {
            let message = format!(
                "this entry names `{}`, but {manifest} gives its package no name",
                entry.name
            );
            Diagnostic::new(codes::E0603, entry.key, message)
        };
        self.problem(package, d);
        None
    }

    /// The packages that `start` reaches, `start` included, and whether a package among them
    /// depends on itself or on the root.
    pub(super) fn closure(&mut self, start: usize) -> Closure {
        let mut closure = Closure {
            members: Vec::new(),
            cycle: false,
            unbuildable: false,
        };
        let mut stack = vec![0];
        self.visit(start, &mut stack, &mut closure);
        closure.unbuildable = closure.members.iter().any(|m| self.unbuildable.contains(m));
        closure
    }

    fn visit(&mut self, node: usize, stack: &mut Vec<usize>, closure: &mut Closure) {
        if stack.contains(&node) {
            closure.cycle = true;
            return;
        }
        if closure.members.contains(&node) {
            return;
        }
        closure.members.push(node);
        stack.push(node);
        for e in 0..self.loaded[node].manifest.entries.len() {
            if let Some(target) = self.target(node, e) {
                self.visit(target, stack, closure);
            }
        }
        stack.pop();
    }
}

/// A directory's identity: its canonical path, or the path itself when it has none.
fn identity(dir: &Path) -> PathBuf {
    dir.canonicalize().unwrap_or_else(|_| dir.to_path_buf())
}

fn join(dir: &str, path: &str) -> String {
    if dir.is_empty() {
        path.to_owned()
    } else {
        format!("{dir}/{path}")
    }
}

/// A relative path with its `.` and `..` segments resolved, as far as they can be: those that
/// climb above the root stay.
pub(crate) fn normalized(path: &str) -> String {
    let mut parts: Vec<&str> = Vec::new();
    for component in Path::new(path).components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir if parts.last().is_some_and(|p| *p != "..") => {
                parts.pop();
            }
            Component::Normal(name) => parts.push(name.to_str().unwrap_or("")),
            _ => parts.push(".."),
        }
    }
    parts.join("/")
}
