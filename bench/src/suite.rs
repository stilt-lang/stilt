//! The benchmark suite on disk (Goals, Workloads): `programs/`, each with a Stilt program, its
//! raising variant, its wrapping variant and its Rust baseline; `micro/`, microbenchmarks with
//! their raising variants; and `empty/`, the empty program in each language.

use std::path::{Path, PathBuf};

/// A program of the suite.
#[derive(Debug)]
pub(crate) struct Program {
    pub(crate) name: String,
    /// The Stilt program, `main.lt`.
    pub(crate) plain: PathBuf,
    /// Its raising variant, `raising.lt`.
    pub(crate) raising: PathBuf,
    /// Its wrapping variant, `wrapping.lt`, whose integer `+`, `-` and `*` wrap, so that its
    /// release build checks no overflow (cheap-checks), of a program; none of a microbenchmark.
    pub(crate) wrapping: PathBuf,
    /// Its Rust baseline, `baseline.rs`, which prints the same output.
    pub(crate) baseline: PathBuf,
    /// The arguments every version is run with: none, so that each runs at the size it writes as
    /// its default, or with `--long` its size of `long.toml`.
    pub(crate) args: Vec<String>,
}

/// The suite, or the part of it a filter selects.
#[derive(Debug)]
pub(crate) struct Suite {
    pub(crate) programs: Vec<Program>,
    /// The microbenchmarks, whose baselines are unused, since only their raising variants are
    /// compared with them (free-success).
    pub(crate) micro: Vec<Program>,
    /// The empty program, whose baseline is the empty Rust program (small-runtime).
    pub(crate) empty: Program,
}

/// The suite under `dir`, with only the programs and microbenchmarks whose name contains
/// `filter`, if one is given.
pub(crate) fn load(dir: &Path, filter: Option<&str>, long: bool) -> Result<Suite, String> {
    let mut suite = programs(&dir.join("programs"), filter, true)?;
    if long {
        let sizes = sizes(&dir.join("long.toml"))?;
        for p in &mut suite {
            let size = sizes.iter().find(|(name, _)| *name == p.name);
            let (_, size) = size.ok_or_else(|| format!("long.toml gives {} no size", p.name))?;
            p.args = vec![size.clone()];
        }
    }
    Ok(Suite {
        programs: suite,
        micro: programs(&dir.join("micro"), filter, false)?,
        empty: Program {
            name: "empty".to_owned(),
            plain: file(&dir.join("empty"), "main.lt")?,
            raising: PathBuf::new(),
            wrapping: PathBuf::new(),
            baseline: file(&dir.join("empty"), "baseline.rs")?,
            args: Vec::new(),
        },
    })
}

/// The programs in the directories under `dir`, in the order of their names.
fn programs(dir: &Path, filter: Option<&str>, baselines: bool) -> Result<Vec<Program>, String> {
    let entries =
        std::fs::read_dir(dir).map_err(|e| format!("cannot read {}: {e}", dir.display()))?;
    let mut dirs: Vec<PathBuf> = entries
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.is_dir())
        .collect();
    dirs.sort();
    let mut programs = Vec::new();
    for dir in dirs {
        let name = dir
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_default();
        if filter.is_some_and(|f| !name.contains(f)) {
            continue;
        }
        programs.push(Program {
            plain: file(&dir, "main.lt")?,
            raising: file(&dir, "raising.lt")?,
            wrapping: if baselines {
                file(&dir, "wrapping.lt")?
            } else {
                PathBuf::new()
            },
            baseline: if baselines {
                file(&dir, "baseline.rs")?
            } else {
                PathBuf::new()
            },
            args: Vec::new(),
            name,
        });
    }
    Ok(programs)
}

/// The sizes of `long.toml`, by program: `name = size` lines, and comments after `#`.
fn sizes(path: &Path) -> Result<Vec<(String, String)>, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
    let mut sizes = Vec::new();
    for (n, line) in text.lines().enumerate() {
        let line = line.split('#').next().unwrap_or_default().trim();
        if line.is_empty() {
            continue;
        }
        let (name, size) = (line.split_once('='))
            .filter(|(_, size)| size.trim().parse::<u64>().is_ok())
            .ok_or_else(|| format!("long.toml, line {}: expected `program = size`", n + 1))?;
        sizes.push((name.trim().to_owned(), size.trim().to_owned()));
    }
    Ok(sizes)
}

fn file(dir: &Path, name: &str) -> Result<PathBuf, String> {
    let path = dir.join(name);
    if path.is_file() {
        Ok(path)
    } else {
        Err(format!("{} has no {name}", dir.display()))
    }
}
