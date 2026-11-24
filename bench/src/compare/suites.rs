//! The programs of the comparisons on disk: the Perceus paper's under `compare/perceus/`, each
//! with its version in every language; the benchmark suite's, whose Stilt program and Rust
//! baseline are under `programs/` and whose versions in other languages are under
//! `compare/programs/`; the programs of `std.par` under `compare/par/`, each in Stilt and in
//! Rust with Rayon, a binary of the Cargo package there, run on each number of threads; the
//! programs that allocate most against their Rust versions linked with mimalloc, the binaries of
//! the Cargo package of `compare/alloc/`; and `examples/pick` against jq and jaq, on the queries
//! of `compare/tools/pick.queries`.

use std::ffi::OsString;
use std::path::{Path, PathBuf};

use super::input;
use super::toolchains::Language;

/// A program, with its version in each language that has one.
#[derive(Debug)]
pub(crate) struct Program {
    pub(crate) name: String,
    /// Each version's source, or nothing for a tool, which runs as it is.
    pub(crate) sources: Vec<(Language, PathBuf)>,
    /// The Cargo package whose binary of the program's name is its Rust version, which Cargo
    /// builds, rather than `rustc` alone.
    pub(crate) manifest: Option<PathBuf>,
    /// The ways it runs, each a row of its own, or none for a program that runs as it is.
    pub(crate) settings: Vec<Setting>,
}

/// One way a program runs: what it adds to the program's name in the report, the environment
/// it runs in, and its arguments.
#[derive(Debug)]
pub(crate) struct Setting {
    pub(crate) label: String,
    pub(crate) env: Vec<(String, String)>,
    pub(crate) args: Vec<OsString>,
}

/// A set of programs, measured and reported together.
#[derive(Debug)]
pub(crate) struct Suite {
    /// The suite's name in paths and in the JSON results.
    pub(crate) key: &'static str,
    /// Its heading in the report.
    pub(crate) title: &'static str,
    /// The version whose output the others must print, and whose times they are measured
    /// against.
    pub(crate) reference: Language,
    pub(crate) programs: Vec<Program>,
}

/// The five suites under `dir`, with only the programs whose name contains `filter`, if one is
/// given. The input of the tools is written under `out`.
pub(crate) fn load(dir: &Path, filter: Option<&str>, out: &Path) -> Result<Vec<Suite>, String> {
    Ok(vec![
        Suite {
            key: "perceus",
            title: "The Perceus paper's programs",
            reference: Language::Rust,
            programs: perceus(&dir.join("compare").join("perceus"), filter)?,
        },
        Suite {
            key: "programs",
            title: "The benchmark suite",
            reference: Language::Rust,
            programs: suite(dir, filter)?,
        },
        Suite {
            key: "par",
            title: "`std.par` against Rayon, on each number of threads",
            reference: Language::Rust,
            programs: par(&dir.join("compare").join("par"), filter)?,
        },
        Suite {
            key: "alloc",
            title: "The programs that allocate most, against Rust with mimalloc",
            reference: Language::Rust,
            programs: alloc(dir, filter)?,
        },
        Suite {
            key: "tools",
            title: "`examples/pick` against jq and jaq",
            reference: Language::Jq,
            programs: tools(dir, filter, out)?,
        },
    ])
}

/// The Perceus paper's programs under `dir`, each with its version in every language that has one.
fn perceus(dir: &Path, filter: Option<&str>) -> Result<Vec<Program>, String> {
    let mut programs = Vec::new();
    for (name, path) in folders(dir, filter)? {
        let sources = Language::ALL
            .into_iter()
            .filter_map(|l| Some((l, path.join(l.source()?))))
            .filter(|(_, p)| p.is_file())
            .collect();
        programs.push(plain(name, sources));
    }
    Ok(programs)
}

/// The benchmark suite's programs: each Stilt program and Rust baseline under `programs/`, and
/// its versions in other languages under `compare/programs/`.
fn suite(dir: &Path, filter: Option<&str>) -> Result<Vec<Program>, String> {
    let suite = dir.join("programs");
    let mut programs = Vec::new();
    for (name, path) in folders(&dir.join("compare").join("programs"), filter)? {
        let mut sources = vec![
            (Language::Stilt, suite.join(&name).join("main.lt")),
            (Language::Rust, suite.join(&name).join("baseline.rs")),
        ];
        sources.extend(
            Language::ALL
                .into_iter()
                .filter(|l| !matches!(l, Language::Stilt | Language::Rust))
                .filter_map(|l| Some((l, path.join(l.source()?))))
                .filter(|(_, p)| p.is_file()),
        );
        if let Some((_, missing)) = sources.iter().find(|(_, p)| !p.is_file()) {
            return Err(format!("{} doesn't exist", missing.display()));
        }
        programs.push(plain(name, sources));
    }
    Ok(programs)
}

fn plain(name: String, sources: Vec<(Language, PathBuf)>) -> Program {
    Program {
        name,
        sources,
        manifest: None,
        settings: Vec::new(),
    }
}

/// The programs of `std.par` under `dir`, each run on 1 thread and on every number up to one per
/// core: those that `STILT_THREADS` and `RAYON_NUM_THREADS` give.
fn par(dir: &Path, filter: Option<&str>) -> Result<Vec<Program>, String> {
    let cores = std::thread::available_parallelism().map_or(1, usize::from);
    let manifest = dir.join("Cargo.toml");
    let mut programs = Vec::new();
    for (name, path) in folders(dir, filter)? {
        let sources = vec![
            (Language::Stilt, path.join("main.lt")),
            (Language::Rust, path.join("main.rs")),
        ];
        if !sources.iter().all(|(_, p)| p.is_file()) {
            continue;
        }
        let settings = (1..=cores)
            .map(|n| Setting {
                label: if n == 1 {
                    "1 thread".to_owned()
                } else {
                    format!("{n} threads")
                },
                env: vec![
                    ("STILT_THREADS".to_owned(), n.to_string()),
                    ("RAYON_NUM_THREADS".to_owned(), n.to_string()),
                ],
                args: Vec::new(),
            })
            .collect();
        programs.push(Program {
            name,
            sources,
            manifest: Some(manifest.clone()),
            settings,
        });
    }
    Ok(programs)
}

/// The programs whose Rust versions `compare/alloc/` links with mimalloc, each a binary of the
/// program's name, beside its Stilt program: the Perceus paper's, or the suite's.
fn alloc(dir: &Path, filter: Option<&str>) -> Result<Vec<Program>, String> {
    let package = dir.join("compare").join("alloc");
    let entries = std::fs::read_dir(&package)
        .map_err(|e| format!("cannot read {}: {e}", package.display()))?;
    let mut names: Vec<String> = entries
        .filter_map(Result::ok)
        .filter_map(|e| {
            e.file_name()
                .to_str()?
                .strip_suffix(".rs")
                .map(str::to_owned)
        })
        .filter(|name| name != "build" && filter.is_none_or(|f| name.contains(f)))
        .collect();
    names.sort();
    let mut programs = Vec::new();
    for name in names {
        let perceus = dir
            .join("compare")
            .join("perceus")
            .join(&name)
            .join("main.lt");
        let stilt = if perceus.is_file() {
            perceus
        } else {
            dir.join("programs").join(&name).join("main.lt")
        };
        if !stilt.is_file() {
            return Err(format!(
                "{} has no Stilt program",
                package.join(&name).display()
            ));
        }
        programs.push(Program {
            sources: vec![
                (Language::Stilt, stilt),
                (Language::Rust, package.join(format!("{name}.rs"))),
            ],
            name,
            manifest: Some(package.join("Cargo.toml")),
            settings: Vec::new(),
        });
    }
    Ok(programs)
}

/// `examples/pick` beside jq and jaq, each query of `compare/tools/pick.queries` a row, run on
/// the document [`input::books`] writes under `out`.
fn tools(dir: &Path, filter: Option<&str>, out: &Path) -> Result<Vec<Program>, String> {
    if filter.is_some_and(|f| !"pick".contains(f)) {
        return Ok(Vec::new());
    }
    let queries = dir.join("compare").join("tools").join("pick.queries");
    let text = std::fs::read_to_string(&queries)
        .map_err(|e| format!("cannot read {}: {e}", queries.display()))?;
    let document = out.join("tools").join("books.json");
    input::books(&document)?;
    let settings = (text.lines())
        .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
        .map(|query| Setting {
            label: format!("`{query}`"),
            env: Vec::new(),
            args: vec!["-c".into(), query.into(), document.clone().into()],
        })
        .collect();
    let examples = dir.parent().unwrap_or(dir).join("examples").join("pick");
    Ok(vec![Program {
        name: "pick".to_owned(),
        sources: vec![
            (Language::Stilt, examples),
            (Language::Jq, PathBuf::new()),
            (Language::Jaq, PathBuf::new()),
        ],
        manifest: None,
        settings,
    }])
}

/// The directories under `dir` whose name contains `filter`, by name, in the order of their
/// names.
fn folders(dir: &Path, filter: Option<&str>) -> Result<Vec<(String, PathBuf)>, String> {
    let entries =
        std::fs::read_dir(dir).map_err(|e| format!("cannot read {}: {e}", dir.display()))?;
    let mut folders: Vec<(String, PathBuf)> = entries
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.is_dir())
        .filter_map(|p| Some((p.file_name()?.to_str()?.to_owned(), p)))
        .filter(|(name, _)| filter.is_none_or(|f| name.contains(f)))
        .collect();
    folders.sort();
    Ok(folders)
}
