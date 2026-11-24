//! Reading a program from disk (program.forms; packages.path-dependencies and
//! packages.modules-of-dependencies).

use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use stilt_diag::{Diagnostic, codes};
use stilt_pkg::Graph;
use stilt_pkg::api::{Apis, Unchecked};
use stilt_pkg::fetch::{Cache, Fetched};
use stilt_pkg::manifest::Fill;
use stilt_pkg::select::Served;
use stilt_syntax::TextSize;

use crate::packages::{Dependency, Granting, PackageInfo, Packages};
use crate::{Db, Program, program_of_packages, source_file};

/// The file beside a package's manifest that pins its docs (docs.lock-file).
pub const PINS: &str = "docs.lock";

/// A source file of a program on disk: the path reports name it by, the names its place gives
/// its module in the program, where it is, and the index of its package.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Source {
    /// The path the file is reported by.
    pub path: String,
    /// The module path the file stands for.
    pub module_path: Vec<String>,
    /// The file on disk.
    pub file: PathBuf,
    /// The index of the file's package.
    pub package: usize,
}

/// A program as it is on disk: its source files, sorted by path, and for a package, the
/// packages its manifests name with the first segment of their modules' names.
#[derive(Debug)]
pub struct Read {
    pub sources: Vec<Source>,
    pub graph: Option<Graph>,
    pub prefixes: Vec<Option<String>>,
    /// The requests that a higher version serves (versions.selection).
    pub served: Vec<Served>,
    /// The packages that reading the program fetched (packages.fetch-report).
    pub fetched: Vec<Fetched>,
    /// The manifests on disk of the root package and of its path dependencies, which an edit
    /// can change, in the order of the packages.
    pub manifests: Vec<PathBuf>,
}

/// Reads the program at `path`. The program is a single file, which is module `main` whatever
/// its name; a package, which is a directory holding `stilt.toml`, whose modules are the `.lt`
/// files under its `src/`, and which has none without one, with the packages its manifest names;
/// or a directory program, which is any other directory holding `main.lt`, whose modules are
/// its `.lt` files. It reaches no repository over the network: a command that reads the program
/// to look for edits takes fetched packages from the cache, where the command that loaded the
/// program put them.
///
/// # Errors
///
/// A message for people, when `path` is no program or can't be read.
pub fn read(path: &Path) -> Result<Read, String> {
    read_with(
        path,
        &mut Unchecked,
        &mut Cache::from_env().offline(),
        false,
    )
}

/// Reads the program at `path` as [`read`] does, fetching into `cache`, with the APIs that
/// `apis` gives checking each request that a higher version serves (versions.selection), and with
/// `fill` filling in the manifests first (packages.filling-in).
///
/// # Errors
///
/// A message for people, when `path` is no program or can't be read.
pub fn read_with(
    path: &Path,
    apis: &mut dyn Apis,
    cache: &mut Cache,
    fill: bool,
) -> Result<Read, String> {
    let shown = path.display();
    if !path.exists() {
        return Err(format!("{shown} doesn't exist"));
    }
    if !path.is_dir() {
        let name = path
            .file_name()
            .map_or_else(String::new, |name| name.to_string_lossy().into_owned());
        let source = Source {
            path: name,
            module_path: vec!["main".to_owned()],
            file: path.to_path_buf(),
            package: 0,
        };
        return Ok(Read {
            sources: vec![source],
            graph: None,
            prefixes: vec![None],
            served: Vec::new(),
            fetched: Vec::new(),
            manifests: Vec::new(),
        });
    }
    if path.join("stilt.toml").exists() {
        return read_package(path, apis, cache, fill);
    }
    if !path.join("main.lt").exists() {
        return Err(format!(
            "{shown} is a directory without a main.lt, so not a program"
        ));
    }
    let sources = modules(path, "", 0, None)?;
    Ok(Read {
        sources,
        graph: None,
        prefixes: vec![None],
        served: Vec::new(),
        fetched: Vec::new(),
        manifests: Vec::new(),
    })
}

/// The source files of the program at `path`, sorted by path, as [`read`] finds them.
///
/// # Errors
///
/// A message for people, when `path` is no program or can't be read.
pub fn sources(path: &Path) -> Result<Vec<Source>, String> {
    read(path).map(|read| read.sources)
}

fn read_package(
    path: &Path,
    apis: &mut dyn Apis,
    cache: &mut Cache,
    fill: bool,
) -> Result<Read, String> {
    let (graph, selection) = graph(path, apis, cache, fill)?;
    let mut sources = Vec::new();
    let mut prefixes = vec![None];
    let root_src = path.join("src");
    let root_files = if root_src.is_dir() {
        modules(&root_src, "src/", 0, None)?
    } else {
        Vec::new()
    };
    let firsts: HashSet<&str> = root_files
        .iter()
        .filter_map(|s| s.module_path.first().map(String::as_str))
        .collect();
    let direct: HashSet<&str> = graph.packages[0]
        .manifest
        .entries
        .iter()
        .map(|e| e.name.as_str())
        .collect();
    for (i, package) in graph.packages.iter().enumerate().skip(1) {
        let name = package.manifest.name.clone().unwrap_or_default();
        // A root module named like a package that the root doesn't depend on would take its
        // modules' names; a prefix that no module can have keeps the two apart.
        let prefix = if firsts.contains(name.as_str()) && !direct.contains(name.as_str()) {
            format!("{name}~")
        } else {
            name
        };
        let src = package.dir.join("src");
        if src.is_dir() {
            let shown = package.source_path("");
            sources.extend(modules(&src, &shown, i, Some(&prefix))?);
        }
        prefixes.push(Some(prefix));
    }
    sources.extend(root_files);
    sources.sort_by(|a, b| a.path.cmp(&b.path));
    let manifests = (graph.packages.iter())
        .filter(|package| !package.fetched)
        .map(|package| package.dir.join("stilt.toml"))
        .collect();
    Ok(Read {
        sources,
        graph: Some(graph),
        prefixes,
        served: selection.served,
        fetched: std::mem::take(&mut cache.fetched),
        manifests,
    })
}

/// The packages of the program whose root package is at `path`, after filling in its manifests
/// with `fill`, and the versions selected.
fn graph(
    path: &Path,
    apis: &mut dyn Apis,
    cache: &mut Cache,
    fill: bool,
) -> Result<(Graph, stilt_pkg::select::Selection), String> {
    let mut broken = if fill {
        stilt_pkg::fill::fill(path, cache, apis)
    } else {
        Vec::new()
    };
    let selection = stilt_pkg::select::select(path, cache);
    broken.extend(selection.broken.iter().cloned());
    broken.extend(stilt_pkg::compat::incompatible(
        path,
        &selection.served,
        apis,
    ));
    let mut fetcher = stilt_pkg::select::Selected {
        cache,
        selection: &selection,
    };
    let graph = stilt_pkg::graph::read(path, &mut fetcher, &broken)?;
    Ok((graph, selection))
}

/// The modules below the module root `root`, whose files are reported with `shown` before their
/// paths from `root`, and whose names start with `prefix` (packages.modules-of-dependencies).
fn modules(
    root: &Path,
    shown: &str,
    package: usize,
    prefix: Option<&str>,
) -> Result<Vec<Source>, String> {
    let names = stilt_pkg::files::module_files(root)
        .map_err(|error| format!("cannot read {}: {error}", root.display()))?;
    Ok(names
        .into_iter()
        .map(|name| {
            let local: Vec<String> = name
                .trim_end_matches(".lt")
                .split('/')
                .map(str::to_owned)
                .collect();
            Source {
                path: format!("{shown}{name}"),
                module_path: named(prefix, local),
                file: root.join(&name),
                package,
            }
        })
        .collect())
}

/// A module's name in the program, from its name in its package: in a dependency `D`, its
/// `main` is `D` and its `a.b` is `D.a.b`.
fn named(prefix: Option<&str>, local: Vec<String>) -> Vec<String> {
    match prefix {
        None => local,
        Some(prefix) if local == ["main"] => vec![prefix.to_owned()],
        Some(prefix) => std::iter::once(prefix.to_owned()).chain(local).collect(),
    }
}

/// Reads the program at `path` into the database, with the standard library, as [`read`] finds
/// its files.
///
/// # Errors
///
/// A message for people, when `path` is no program or can't be read.
pub fn load(db: &dyn Db, path: &Path) -> Result<Program, String> {
    load_with(db, path, &mut Unchecked, false)
}

/// Reads the program at `path` into the database as [`read_with`] does.
///
/// # Errors
///
/// A message for people, when `path` is no program or can't be read.
pub fn load_with(
    db: &dyn Db,
    path: &Path,
    apis: &mut dyn Apis,
    filled: bool,
) -> Result<Program, String> {
    let read = read_with(path, apis, &mut Cache::from_env(), filled)?;
    let mut files = Vec::new();
    let mut by_package: Vec<Vec<_>> = vec![Vec::new(); read.prefixes.len()];
    for source in &read.sources {
        let bytes = fs::read(&source.file)
            .map_err(|error| format!("cannot read {}: {error}", source.file.display()))?;
        let file = source_file(db, source.path.clone(), source.module_path.clone(), bytes);
        files.push(file);
        by_package[source.package].push(file);
    }
    let packages = match read.graph {
        Some(graph) => Packages {
            served: read.served,
            fetched: read.fetched,
            ..packages(db, graph, read.prefixes, by_package)
        },
        None => Packages {
            list: vec![PackageInfo {
                name: None,
                edition: stilt_pkg::edition::first().name,
                prefix: None,
                manifest: None,
                pins: None,
                files: files.clone(),
                deps: Vec::new(),
                links: Vec::new(),
                declares: true,
                fetched: false,
                version: None,
                shown: String::new(),
                dir: Some(root_dir(path)),
            }],
            ..Packages::default()
        },
    };
    Ok(program_of_packages(db, files, packages))
}

/// The directory of a program without a manifest: the file's, or the directory itself.
fn root_dir(path: &Path) -> std::path::PathBuf {
    if path.is_dir() {
        return path.to_path_buf();
    }
    match path.parent() {
        Some(p) if !p.as_os_str().is_empty() => p.to_path_buf(),
        _ => std::path::PathBuf::from("."),
    }
}

fn packages(
    db: &dyn Db,
    graph: Graph,
    prefixes: Vec<Option<String>>,
    by_package: Vec<Vec<crate::SourceFile>>,
) -> Packages {
    let mut list = Vec::new();
    for ((package, prefix), files) in graph.packages.into_iter().zip(prefixes).zip(by_package) {
        let deps = (package.manifest.entries.iter().zip(&package.deps))
            .map(|(entry, &target)| Dependency {
                name: entry.name.clone(),
                package: target,
                may: entry.may,
                key: entry.key,
                grant: match entry.may_at {
                    Some(at) => Some(Granting::Replace(at)),
                    None => grant(&entry.fill, &package.bytes),
                },
            })
            .collect();
        let version = package
            .fetched
            .then(|| package.shown.rsplit_once('@').map(|(_, v)| v.to_owned()))
            .flatten();
        let pins = (!package.fetched).then(|| {
            let bytes = fs::read(package.dir.join(PINS)).unwrap_or_default();
            let path = package.manifest_path().replace("stilt.toml", PINS);
            source_file(db, path, Vec::new(), bytes)
        });
        let manifest = source_file(db, package.manifest_path(), Vec::new(), package.bytes);
        let links = package.manifest.links;
        list.push(PackageInfo {
            edition: (package.manifest.edition).unwrap_or(stilt_pkg::edition::first().name),
            name: package.manifest.name,
            prefix,
            manifest: Some(manifest),
            pins,
            files,
            deps,
            links,
            declares: package.manifest.declares,
            fetched: package.fetched,
            version,
            shown: package.shown,
            dir: Some(package.dir),
        });
    }
    let mut problems: Vec<_> = graph
        .problems
        .into_iter()
        .filter_map(|(i, d)| Some((list.get(i)?.manifest?, d)))
        .collect();
    problems.extend(missing_libraries(&list));
    Packages {
        list,
        problems,
        ..Packages::default()
    }
}

/// c.finding-libraries: E0611 at each C library of a package's manifest that the system's dynamic
/// loader doesn't find.
fn missing_libraries(list: &[PackageInfo]) -> Vec<(crate::SourceFile, Diagnostic)> {
    let mut found = Vec::new();
    for p in list {
        let Some(manifest) = p.manifest else { continue };
        for (name, at) in &p.links {
            if !loads(name) {
                let message = format!(
                    "the C library `{name}` isn't found: the system's loader finds no lib{name}"
                );
                found.push((manifest, Diagnostic::new(codes::E0611, *at, message)));
            }
        }
    }
    found
}

/// What asks the system's dynamic loader whether it finds a C library, which the host installs:
/// the runtime asks it, and `stilt-db` doesn't depend on the runtime.
static FINDER: OnceLock<fn(&str) -> bool> = OnceLock::new();

/// Installs `finder`, which tells whether the system's dynamic loader finds the C library it is
/// given, asked without loading it (c.finding-libraries). A host that installs none, as the
/// compiler built for WebAssembly that the playground runs, finds no C library: it has no
/// loader.
pub fn install_library_finder(finder: fn(&str) -> bool) {
    let _ = FINDER.set(finder);
}

/// Whether the system's dynamic loader finds the C library `name`.
fn loads(name: &str) -> bool {
    FINDER.get().is_some_and(|finds| finds(name))
}

/// Where a grant goes in an entry without `may`, and the text before its list: after the last value
/// of an inline table, or on a line of its own after the entry's last line (packages.grants, rule
/// 18).
fn grant(fill: &Fill, bytes: &[u8]) -> Option<Granting> {
    match fill {
        Fill::Inline(at) => Some(Granting::Insert(*at, ", may = ".to_owned())),
        Fill::Lines(at, prefix) => {
            let start = usize::from(*at);
            let end = bytes
                .get(start..)?
                .iter()
                .position(|&b| b == b'\n')
                .map_or(bytes.len(), |n| start + n);
            let end = TextSize::from(u32::try_from(end).ok()?);
            Some(Granting::Insert(end, format!("\n{prefix}may = ")))
        }
    }
}
