//! Minimal version selection (versions.selection): every version of every repository that the
//! program's manifests ask for, transitively, and for each repository the highest of them. The
//! manifests alone decide it, so two machines given the same manifests select the same versions.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use stilt_diag::{Code, codes};

use crate::fetch::{Cache, Failure};
use crate::fill::Unfilled;
use crate::graph::{Fetcher, manifest_in};
use crate::manifest::{Entry, Source};
use crate::version::Version;

/// What the program selects, and the requests that a higher version serves.
#[derive(Debug, Default)]
pub struct Selection {
    /// For each repository, the version selected and its hash.
    pub selected: BTreeMap<String, (Version, String)>,
    /// The errors of selection, each at the root's entry through which its requests arrive.
    pub broken: Vec<Unfilled>,
    /// The requests that a higher version serves.
    pub served: Vec<Served>,
}

/// A request for a version of a repository that a higher version serves, whose API change must
/// need no new major version (versions.compatible-selections).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Served {
    /// The root's entry through which the request arrives.
    pub entry: usize,
    /// The package whose manifest asks, as messages name it, or `None` for the root's.
    pub asker: Option<String>,
    /// The package whose manifest asks for the selected version, likewise.
    pub selector: Option<String>,
    /// The repository requested.
    pub from: String,
    /// The version asked for.
    pub asked: Version,
    /// The directory of the version asked for.
    pub asked_dir: PathBuf,
    /// The version selected.
    pub selected: Version,
    /// The directory of the version selected.
    pub selected_dir: PathBuf,
}

/// A request for a version, and what it found.
struct Request {
    from: String,
    version: Version,
    hash: Option<String>,
    found: String,
    dir: PathBuf,
    entry: usize,
    asker: Option<String>,
}

struct Collect<'c> {
    root: PathBuf,
    cache: &'c mut Cache,
    dirs: BTreeSet<PathBuf>,
    requests: Vec<Request>,
    broken: Vec<Unfilled>,
}

/// The selection of the program whose root package is at `root`.
pub fn select(root: &Path, cache: &mut Cache) -> Selection {
    let mut collect = Collect {
        root: root.to_path_buf(),
        cache,
        dirs: BTreeSet::new(),
        requests: Vec::new(),
        broken: Vec::new(),
    };
    let Some((manifest, _)) = manifest_in(root) else {
        return Selection::default();
    };
    collect.dirs.insert(identity(root));
    for (r, entry) in manifest.entries.iter().enumerate() {
        collect.entry(root, entry, r, false, None);
    }
    collect.finish()
}

impl Collect<'_> {
    fn entry(&mut self, dir: &Path, entry: &Entry, r: usize, fetched: bool, asker: Option<&str>) {
        match &entry.source {
            Some(Source::Path(path)) if !fetched => self.dir(&dir.join(path), r),
            Some(Source::From {
                from,
                version: Some(version),
                hash,
            }) => {
                let Some(version) = Version::parse(&version.value) else {
                    return;
                };
                let hash = hash.as_ref().map(|h| h.value.clone());
                self.request(from, version, hash, r, fetched, asker);
            }
            _ => {}
        }
    }

    fn dir(&mut self, dir: &Path, r: usize) {
        if !self.dirs.insert(identity(dir)) {
            return;
        }
        let Some((manifest, _)) = manifest_in(dir) else {
            return;
        };
        let asker = format!("`{}`", manifest.name.clone().unwrap_or_default());
        for entry in &manifest.entries {
            self.entry(dir, entry, r, false, Some(&asker));
        }
    }

    fn request(
        &mut self,
        from: &str,
        version: Version,
        hash: Option<String>,
        r: usize,
        fetched: bool,
        asker: Option<&str>,
    ) {
        let walked = self
            .requests
            .iter()
            .any(|q| q.from == from && q.version == version);
        let (dir, found) = match self.cache.package(from, version, hash.as_deref()) {
            Ok(found) => found,
            Err((code, message)) => {
                // An entry of the root's manifest or of a path dependency's reports its own
                // failure, when the program's packages are read.
                if fetched {
                    self.broken(r, code, message);
                }
                return;
            }
        };
        self.requests.push(Request {
            from: from.to_owned(),
            version,
            hash,
            found,
            dir: dir.clone(),
            entry: r,
            asker: asker.map(str::to_owned),
        });
        if walked {
            return;
        }
        if let Some((manifest, _)) = manifest_in(&dir) {
            let name = manifest.name.clone().unwrap_or_default();
            let asker = format!("`{name}` {version}");
            for entry in &manifest.entries {
                self.entry(&dir, entry, r, true, Some(&asker));
            }
        }
    }

    fn broken(&mut self, entry: usize, code: Code, message: String) {
        self.broken.push(Unfilled {
            dir: self.root.clone(),
            entry,
            code,
            message,
        });
    }

    fn finish(mut self) -> Selection {
        let requests = std::mem::take(&mut self.requests);
        let mut selection = Selection::default();
        let mut by_repo: BTreeMap<&str, Vec<&Request>> = BTreeMap::new();
        for q in &requests {
            by_repo.entry(&q.from).or_default().push(q);
        }
        for (from, requests) in by_repo {
            let first = requests.iter().map(|q| q.entry).min().unwrap_or(0);
            let highest = *requests
                .iter()
                .max_by_key(|q| q.version)
                .expect("a request");
            let majors: BTreeSet<u64> = requests.iter().map(|q| q.version.major).collect();
            if majors.len() > 1 {
                let versions: BTreeSet<String> =
                    requests.iter().map(|q| q.version.to_string()).collect();
                let message = format!(
                    "the manifests ask for {from} at {}, of {} major versions, and a program \
                     holds one",
                    versions.into_iter().collect::<Vec<_>>().join(", "),
                    majors.len()
                );
                self.broken(first, codes::E0605, message);
            }
            if let Some(message) = two_hashes(from, &requests) {
                self.broken(first, codes::E0602, message);
            }
            selection
                .selected
                .insert(from.to_owned(), (highest.version, highest.found.clone()));
            for q in requests.iter().filter(|q| q.version < highest.version) {
                selection.served.push(Served {
                    entry: q.entry,
                    asker: q.asker.clone(),
                    selector: highest.asker.clone(),
                    from: from.to_owned(),
                    asked: q.version,
                    asked_dir: q.dir.clone(),
                    selected: highest.version,
                    selected_dir: highest.dir.clone(),
                });
            }
        }
        selection.broken = self.broken;
        selection
    }
}

/// The error of two manifests that give one version two hashes, if two do.
fn two_hashes(from: &str, requests: &[&Request]) -> Option<String> {
    for (i, a) in requests.iter().enumerate() {
        for b in &requests[i + 1..] {
            if a.version == b.version
                && let (Some(x), Some(y)) = (&a.hash, &b.hash)
                && x != y
            {
                return Some(format!(
                    "two manifests pin {from} {} by two hashes, {x} and {y}",
                    a.version
                ));
            }
        }
    }
    None
}

fn identity(dir: &Path) -> PathBuf {
    dir.canonicalize().unwrap_or_else(|_| dir.to_path_buf())
}

/// The fetcher that gives each repository at the version the program selects.
#[derive(Debug)]
pub struct Selected<'c> {
    /// The cache the versions are fetched from.
    pub cache: &'c mut Cache,
    /// The selection the program made.
    pub selection: &'c Selection,
}

impl Fetcher for Selected<'_> {
    fn fetch(
        &mut self,
        from: &str,
        version: Option<&str>,
        hash: Option<&str>,
    ) -> Result<(PathBuf, String), Failure> {
        let Some(asked) = version.and_then(Version::parse) else {
            let message = format!(
                "the entry gives no `version` of {from}, so the program can't be built: a \
                 command that writes its manifest fills it in"
            );
            return Err((codes::E0601, message));
        };
        let (dir, version) = match self.selection.selected.get(from) {
            Some(&(selected, ref found)) if selected != asked => {
                let (dir, _) = self.cache.package(from, selected, Some(found))?;
                (dir, selected)
            }
            _ => (self.cache.package(from, asked, hash)?.0, asked),
        };
        Ok((dir, format!("{from}@{version}")))
    }
}
