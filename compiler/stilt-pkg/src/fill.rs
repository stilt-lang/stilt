//! Filling in manifests (packages.filling-in and versions.checked-versions): every command that
//! reads a package's dependencies writes the `version` and `hash` that the root's manifest and its
//! path dependencies' lack, once the version is checked against the change in the API since the
//! repository's previous version.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use stilt_diag::{Code, codes};

use crate::api::{Apis, changes, needed};
use crate::fetch::{Cache, Failure};
use crate::graph::manifest_in;
use crate::manifest::{Entry, Fill, Source};
use crate::version::{Change, Version};

/// An entry that can't be filled in, by its manifest's directory and its place in the manifest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Unfilled {
    /// The directory of the entry's manifest.
    pub dir: PathBuf,
    /// The entry's place in the manifest.
    pub entry: usize,
    /// The code of the error that stops the filling.
    pub code: Code,
    /// What the error says.
    pub message: String,
}

/// Fills in the manifests of the root package at `root` and of its path dependencies, writing
/// each that changes, and gives the entries that can't be filled in.
pub fn fill(root: &Path, cache: &mut Cache, apis: &mut dyn Apis) -> Vec<Unfilled> {
    let mut unfilled = Vec::new();
    let mut todo = vec![root.to_path_buf()];
    let mut seen = Vec::new();
    while let Some(dir) = todo.pop() {
        let id = dir.canonicalize().unwrap_or_else(|_| dir.clone());
        if seen.contains(&id) {
            continue;
        }
        seen.push(id);
        let Some((manifest, bytes)) = manifest_in(&dir) else {
            continue;
        };
        let mut edits = Vec::new();
        for (i, entry) in manifest.entries.iter().enumerate() {
            match &entry.source {
                Some(Source::Path(path)) => todo.push(dir.join(path)),
                Some(Source::From {
                    from,
                    version,
                    hash,
                }) if hash.is_none() => {
                    let asked = version.as_ref().and_then(|v| Version::parse(&v.value));
                    match pin(from, asked, &entry.name, cache, apis) {
                        Ok((v, h)) => edits.push(written(entry, asked.is_none(), v, &h, &bytes)),
                        Err((code, message)) => unfilled.push(Unfilled {
                            dir: dir.clone(),
                            entry: i,
                            code,
                            message,
                        }),
                    }
                }
                _ => {}
            }
        }
        if !edits.is_empty() {
            let _ = std::fs::write(dir.join("stilt.toml"), apply(&bytes, edits));
        }
    }
    unfilled
}

/// The version and hash to write for an entry: its `version`, or the repository's highest,
/// once checked.
fn pin(
    from: &str,
    asked: Option<Version>,
    name: &str,
    cache: &mut Cache,
    apis: &mut dyn Apis,
) -> Result<(Version, String), Failure> {
    let versions: Vec<Version> = cache.versions(from)?.into_iter().map(|(v, _)| v).collect();
    let version = match asked {
        Some(v) => v,
        None => *versions.last().expect("a repository with versions has one"),
    };
    let (dir, hash) = cache.package(from, version, None)?;
    if !from_content(&dir) {
        let message = format!(
            "`{name}` {version} has a manifest with a `path` entry or an entry without its \
             `version` and `hash`, so it can't be built from its content"
        );
        return Err((codes::E0601, message));
    }
    let mut checker = Checker {
        from,
        cache,
        apis,
        versions: &versions,
    };
    match checker.check(version, &dir) {
        Ok(()) => Ok((version, hash)),
        Err(problem) => Err(checker.refusal(name, version, problem, asked.is_none())),
    }
}

/// Whether the fetched package in `dir` can be built from its content: each entry of its
/// manifest gives `from`, `version` and `hash` (packages.path-dependencies).
fn from_content(dir: &Path) -> bool {
    manifest_in(dir).is_none_or(|(manifest, _)| {
        manifest.entries.iter().all(|e| {
            matches!(
                &e.source,
                Some(Source::From {
                    version: Some(_),
                    hash: Some(_),
                    ..
                })
            )
        })
    })
}

/// Why a version can't be written.
enum Problem {
    Errors(String),
    Understates {
        previous: Version,
        needs: Change,
        what: String,
    },
}

struct Checker<'c> {
    from: &'c str,
    cache: &'c mut Cache,
    apis: &'c mut dyn Apis,
    versions: &'c [Version],
}

impl Checker<'_> {
    fn dir(&mut self, version: Version) -> Option<PathBuf> {
        self.cache
            .package(self.from, version, None)
            .ok()
            .map(|(d, _)| d)
    }

    /// versions.checked-versions: the version has no error, and its number changes at least as the
    /// change in the API since the highest lower version without errors asks.
    fn check(&mut self, version: Version, dir: &Path) -> Result<(), Problem> {
        let api = self.apis.api(dir).map_err(Problem::Errors)?;
        let lower: Vec<Version> = self
            .versions
            .iter()
            .copied()
            .filter(|v| *v < version)
            .collect();
        for previous in lower.into_iter().rev() {
            let Some(old_dir) = self.dir(previous) else {
                continue;
            };
            let Ok(old) = self.apis.api(&old_dir) else {
                continue;
            };
            let steps = changes(&old, &api);
            let needs = needed(&steps);
            if previous.change_to(version) >= needs {
                return Ok(());
            }
            let first = steps
                .iter()
                .find(|s| s.needs == needs)
                .expect("a step needs it");
            return Err(Problem::Understates {
                previous,
                needs,
                what: first.described(),
            });
        }
        Ok(())
    }

    /// The highest version that has no error and passes its check.
    fn highest_passing(&mut self) -> Option<Version> {
        for version in self.versions.iter().rev().copied().collect::<Vec<_>>() {
            if let Some(dir) = self.dir(version)
                && self.check(version, &dir).is_ok()
            {
                return Some(version);
            }
        }
        None
    }

    fn refusal(
        &mut self,
        name: &str,
        version: Version,
        problem: Problem,
        highest: bool,
    ) -> Failure {
        let which = if highest {
            format!("the highest version of `{name}`, {version},")
        } else {
            format!("`{name}` {version}")
        };
        let offer = match self.highest_passing() {
            Some(v) => format!("; {v} is the highest version that checks"),
            None => String::new(),
        };
        match problem {
            Problem::Errors(first) => (
                codes::E0607,
                format!("{which} has errors, the first an {first}{offer}"),
            ),
            Problem::Understates {
                previous,
                needs,
                what,
            } => {
                let kind = if needs == Change::Major {
                    "major"
                } else {
                    "minor"
                };
                let message = format!(
                    "{which} {what}, which {previous} has, so it needs a new {kind} version, \
                     {}{offer}",
                    previous.next(needs)
                );
                (codes::E0604, message)
            }
        }
    }
}

/// The text that fills in an entry, and where it goes.
fn written(entry: &Entry, version: bool, v: Version, hash: &str, bytes: &[u8]) -> (usize, String) {
    let mut keys = Vec::new();
    if version {
        keys.push(("version", v.to_string()));
    }
    keys.push(("hash", hash.to_owned()));
    let text = |before: &str| {
        keys.iter().fold(String::new(), |mut text, (k, v)| {
            let _ = write!(text, "{before}{k} = \"{v}\"");
            text
        })
    };
    match &entry.fill {
        Fill::Inline(at) => (usize::from(*at), text(", ")),
        Fill::Lines(at, prefix) => {
            let start = usize::from(*at);
            let end = bytes[start..]
                .iter()
                .position(|&b| b == b'\n')
                .map_or(bytes.len(), |n| start + n);
            (end, text(&format!("\n{prefix}")))
        }
    }
}

/// The manifest with each insertion made, the later first so that earlier offsets hold.
fn apply(bytes: &[u8], mut edits: Vec<(usize, String)>) -> Vec<u8> {
    edits.sort_by_key(|(at, _)| std::cmp::Reverse(*at));
    let mut out = bytes.to_vec();
    for (at, text) in edits {
        out.splice(at..at, text.into_bytes());
    }
    out
}
