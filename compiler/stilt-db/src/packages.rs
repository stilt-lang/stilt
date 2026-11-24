//! The packages of a program, as its manifests give them (packages.manifest and
//! packages.package-table): which package each file belongs to, the dependencies each package's
//! manifest names, and the diagnostics found when the manifests were read.

use std::collections::HashMap;

use stilt_diag::Diagnostic;
use stilt_pkg::fetch::Fetched;
pub use stilt_pkg::manifest::Grant;
use stilt_pkg::select::Served;
use stilt_syntax::{TextRange, TextSize};

use crate::{Db, Program, SourceFile};

/// The packages of a program, the root's first. A program without a manifest, a single file or
/// a directory program, is one package that names no dependency.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Packages {
    /// The packages, the root first.
    pub list: Vec<PackageInfo>,
    /// The diagnostics of the manifests that reading the program found, each in its manifest.
    pub problems: Vec<(SourceFile, Diagnostic)>,
    /// The requests for versions that a higher version serves, whose API changes are checked
    /// (versions.compatible-selections).
    pub served: Vec<Served>,
    /// The packages that reading the program fetched, which commands report
    /// (packages.fetch-report).
    pub fetched: Vec<Fetched>,
}

/// A package of a program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageInfo {
    /// Its name, as its manifest gives it.
    pub name: Option<String>,
    /// Its edition, which its files are read with: the one its manifest names, or the first
    /// (editions.edition).
    pub edition: &'static str,
    /// The first segment of its modules' names in the program (packages.modules-of-dependencies):
    /// `None` for the root, whose modules keep their own names, and the package's name for a
    /// dependency.
    pub prefix: Option<String>,
    /// Its manifest, when it has one.
    pub manifest: Option<SourceFile>,
    /// The `docs.lock` beside a manifest that wasn't fetched, empty when there is none, which
    /// pins the package's docs (docs.lock-file).
    pub pins: Option<SourceFile>,
    /// Its modules' files, in the order of their paths.
    pub files: Vec<SourceFile>,
    /// The entries of its manifest's `[dependencies]`, in order.
    pub deps: Vec<Dependency>,
    /// The C libraries of its manifest's `link`, each with the span of its string (c.linking, rule
    /// 13).
    pub links: Vec<(String, TextRange)>,
    /// Whether its manifest declares dependencies: it is TOML 1.0 and its `[dependencies]`,
    /// when it has one, is a table (packages.manifest).
    pub declares: bool,
    /// Whether it was fetched: its files' diagnostics aren't reported
    /// (packages.dependencies-with-errors).
    pub fetched: bool,
    /// The version selected of a fetched package.
    pub version: Option<String>,
    /// Where it is: its directory relative to the root's, or for a fetched package, its
    /// repository and version as `FROM@VERSION`.
    pub shown: String,
    /// Its directory on disk, from which the files that procedural macros' uses name are read:
    /// its manifest's, or for a program without one, its root file's (macros.named-files). `None`
    /// for a program that isn't on disk.
    pub dir: Option<std::path::PathBuf>,
}

/// An entry of a manifest's `[dependencies]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Dependency {
    /// The name of the package the dependency names.
    pub name: String,
    /// The package it names, or `None` when the entry has an error, so that what names its
    /// modules has the error type (packages.manifests-with-errors).
    pub package: Option<usize>,
    /// What the entry grants (facts.capability-grants).
    pub may: Grant,
    /// The span of the entry's key in the manifest.
    pub key: TextRange,
    /// Where a fix writes the list of what the entry grants.
    pub grant: Option<Granting>,
}

/// Where a fix writes the list of what an entry grants (packages.ungranted-effects;
/// facts.ungranted-capabilities).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Granting {
    /// In place of the value of the entry's `may`.
    Replace(TextRange),
    /// After the entry's last value, with the text before the list: `, may = ` in an inline
    /// table, and a line of its own otherwise.
    Insert(TextSize, String),
}

impl Packages {
    /// The root package, if the program has a manifest.
    #[must_use]
    pub fn root(&self) -> Option<&PackageInfo> {
        self.list.first()
    }

    /// The C libraries of every package, each with its package and the span of its string, in
    /// the order the program loads them: the root's first, then each dependency of a manifest
    /// in the order of its entries, depth first, each package once (c.linking).
    #[must_use]
    pub fn libraries(&self) -> Vec<(usize, &str, TextRange)> {
        fn visit<'a>(
            list: &'a [PackageInfo],
            i: usize,
            seen: &mut Vec<bool>,
            out: &mut Vec<(usize, &'a str, TextRange)>,
        ) {
            if seen.get(i).is_none_or(|&s| s) {
                return;
            }
            seen[i] = true;
            out.extend(
                list[i]
                    .links
                    .iter()
                    .map(|(name, at)| (i, name.as_str(), *at)),
            );
            for d in &list[i].deps {
                if let Some(p) = d.package {
                    visit(list, p, seen, out);
                }
            }
        }
        let mut out = Vec::new();
        visit(&self.list, 0, &mut vec![false; self.list.len()], &mut out);
        out
    }
}

/// The index of the package of each of a program's files, in [`Packages::list`]. A program
/// without packages has its files in package 0.
#[salsa::tracked(returns(ref))]
pub fn file_packages(db: &dyn Db, program: Program) -> HashMap<SourceFile, usize> {
    let mut map = HashMap::new();
    for (i, package) in program.packages(db).list.iter().enumerate() {
        for &file in &package.files {
            map.insert(file, i);
        }
    }
    map
}

/// The package of a file of the program: 0, the root, for a file of a program without packages.
pub fn package_of(db: &dyn Db, program: Program, file: SourceFile) -> usize {
    file_packages(db, program).get(&file).copied().unwrap_or(0)
}

/// The files whose diagnostics a program reports: all but those of fetched packages, whose
/// errors each give one E0607 instead (packages.dependencies-with-errors).
#[salsa::tracked(returns(ref))]
pub fn reported_files(db: &dyn Db, program: Program) -> Vec<SourceFile> {
    let packages = program.packages(db);
    program
        .files(db)
        .iter()
        .copied()
        .filter(|&file| {
            let package = package_of(db, program, file);
            !packages.list.get(package).is_some_and(|p| p.fetched)
        })
        .collect()
}
