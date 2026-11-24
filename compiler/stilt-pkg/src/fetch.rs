//! Fetched packages (packages.versions, packages.content-hash and packages.fetching): the versions
//! of a repository, the package at a version, and the cache that keeps packages by their content
//! hashes, in the directory that `STILT_HOME` names, or else in `.stilt` in the user's home
//! directory.
//!
//! A package read from the cache or from its repository has its hash computed each time, and
//! content whose hash isn't the one a manifest gives it is E0602.

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use stilt_diag::{Code, codes};

use crate::git::remote::Remote;
use crate::git::{Id, Repo};
use crate::hash::{Files, content_hash, read_dir};
use crate::version::Version;

/// What a command fetched, which it reports (packages.fetch-report).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fetched {
    /// The name of the package.
    pub name: String,
    /// The repository it was fetched from.
    pub from: String,
    /// The version that was fetched.
    pub version: Version,
    /// The hash of the fetched files.
    pub hash: String,
}

/// The cache of fetched packages, and what this command fetched into it.
#[derive(Debug)]
pub struct Cache {
    /// The cache's directory, `None` when neither `STILT_HOME` nor a home directory is set.
    home: Option<PathBuf>,
    /// What this command fetched.
    pub fetched: Vec<Fetched>,
    /// Whether it reaches repositories over the network, or only those on the machine.
    network: bool,
}

/// Why a package can't be had, as the code and the message of its error.
pub type Failure = (Code, String);

impl Cache {
    /// The cache that the environment names.
    #[must_use]
    pub fn from_env() -> Self {
        let home = std::env::var_os("STILT_HOME")
            .map(PathBuf::from)
            .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".stilt")));
        Self {
            home,
            fetched: Vec::new(),
            network: true,
        }
    }

    /// The cache in `home`.
    #[must_use]
    pub fn at(home: &Path) -> Self {
        Self {
            home: Some(home.to_path_buf()),
            fetched: Vec::new(),
            network: true,
        }
    }

    /// The cache, reaching no repository over the network: what it doesn't hold, and no
    /// repository on the machine has, can't be had.
    #[must_use]
    pub fn offline(self) -> Self {
        Self {
            network: false,
            ..self
        }
    }

    /// The versions of the repository `from`, lowest first, each with its tag.
    ///
    /// # Errors
    ///
    /// E0601, when the repository can't be reached or has no version.
    pub fn versions(&self, from: &str) -> Result<Vec<(Version, String)>, Failure> {
        let tags = open(from, self.network)?
            .tags()
            .map_err(|e| unreachable_repo(from, &e))?;
        let mut versions: Vec<(Version, String)> = tags
            .into_iter()
            .filter_map(|(tag, _)| Some((Version::of_tag(&tag)?, tag)))
            .collect();
        versions.sort();
        if versions.is_empty() {
            let message = format!(
                "the repository {} has no version: no tag `vMAJOR.MINOR.PATCH`",
                url(from)
            );
            return Err((codes::E0601, message));
        }
        Ok(versions)
    }

    /// The package at `version` of `from`: from the cache when `hash` is given and the cache
    /// holds it, and otherwise from its repository, into the cache. Gives its directory and its
    /// hash.
    ///
    /// # Errors
    ///
    /// E0601 when the version can't be had, E0602 when its content's hash isn't `hash`.
    pub fn package(
        &mut self,
        from: &str,
        version: Version,
        hash: Option<&str>,
    ) -> Result<(PathBuf, String), Failure> {
        if let (Some(hash), Some(home)) = (hash, &self.home) {
            let dir = packages(home).join(hash.trim_start_matches("b3:"));
            if dir.is_dir() {
                let files = read_dir(&dir).map_err(|e| (codes::E0602, e))?;
                return check(version, Some(hash), &files, "the cache holds it")
                    .map(|found| (dir, found));
            }
        }
        let repo = open(from, self.network)?;
        let tag = format!("v{version}");
        let id = repo
            .tags()
            .map_err(|e| unreachable_repo(from, &e))?
            .into_iter()
            .find(|(t, _)| *t == tag)
            .map(|(_, id)| id)
            .ok_or_else(|| {
                (
                    codes::E0601,
                    format!("the repository {} has no version {version}", url(from)),
                )
            })?;
        let files = repo
            .files_at(id)
            .map_err(|e| unreachable_repo(from, &e))?
            .ok_or_else(|| {
                let message = format!("the tree of {version} holds no stilt.toml at its root");
                (codes::E0601, message)
            })?;
        let found = check(version, hash, &files, &format!("{} serves it", url(from)))?;
        let (dir, stored) = self.store(&found, &files)?;
        if stored {
            let name = (files.iter().find(|(path, _)| path == "stilt.toml"))
                .and_then(|(_, bytes)| crate::manifest::read(bytes).name)
                .unwrap_or_default();
            self.fetched.push(Fetched {
                name,
                from: from.to_owned(),
                version,
                hash: found.clone(),
            });
        }
        Ok((dir, found))
    }

    /// Writes a package's files into the cache, under its hash, unless the cache holds it, and
    /// tells whether it wrote them: whether the package was fetched (packages.fetching).
    fn store(&self, hash: &str, files: &Files) -> Result<(PathBuf, bool), Failure> {
        let home = self.home.as_ref().ok_or_else(|| {
            let message = "there is no cache to fetch into: set STILT_HOME or HOME".to_owned();
            (codes::E0601, message)
        })?;
        let dir = packages(home).join(hash.trim_start_matches("b3:"));
        if dir.is_dir() {
            return Ok((dir, false));
        }
        let n = WRITES.fetch_add(1, Ordering::Relaxed);
        let temporary = packages(home).join(format!(".{}-{n}", std::process::id()));
        let failed = |e: std::io::Error| (codes::E0601, format!("cannot write the cache: {e}"));
        for (path, bytes) in files {
            let file = temporary.join(path);
            fs::create_dir_all(file.parent().expect("a file has a folder")).map_err(failed)?;
            fs::write(&file, bytes).map_err(failed)?;
        }
        if fs::rename(&temporary, &dir).is_err() {
            // Another command stored the same content first.
            let _ = fs::remove_dir_all(&temporary);
        }
        Ok((dir, true))
    }
}

/// How many packages this process has written, which names each write's temporary folder.
static WRITES: AtomicUsize = AtomicUsize::new(0);

fn packages(home: &Path) -> PathBuf {
    home.join("packages")
}

/// The content's hash, when it is `hash` or no hash is asked for.
fn check(
    version: Version,
    hash: Option<&str>,
    files: &Files,
    source: &str,
) -> Result<String, Failure> {
    let found = content_hash(files);
    match hash {
        Some(wanted) if wanted != found => {
            let name = (files.iter().find(|(path, _)| path == "stilt.toml"))
                .and_then(|(_, bytes)| crate::manifest::read(bytes).name)
                .unwrap_or_default();
            let message = format!(
                "`{name}` {version}, as {source}, has the hash {found}, not the one pinned here"
            );
            Err((codes::E0602, message))
        }
        _ => Ok(found),
    }
}

/// A repository, on the machine or over HTTPS.
enum Origin {
    Local(Repo),
    Remote(Remote),
}

impl Origin {
    fn tags(&self) -> Result<Vec<(String, Id)>, String> {
        match self {
            Self::Local(repo) => repo.tags(),
            Self::Remote(remote) => Ok(remote.tags()),
        }
    }

    fn files_at(&self, id: Id) -> Result<Option<Files>, String> {
        match self {
            Self::Local(repo) => repo.files_at(id),
            Self::Remote(remote) => remote.files_at(id),
        }
    }
}

/// The repository that `from` names: a `file://` URL on the machine, or `HOST/PATH`, fetched from
/// `https://HOST/PATH`.
fn open(from: &str, network: bool) -> Result<Origin, Failure> {
    let opened = match from.strip_prefix("file://") {
        Some(path) => Repo::open(Path::new(path)).map(Origin::Local),
        None if network => Remote::open(&url(from)).map(Origin::Remote),
        None => Err("this reading reaches no network".to_owned()),
    };
    opened.map_err(|e| unreachable_repo(from, &e))
}

/// The URL that `from` is fetched from.
#[must_use]
pub fn url(from: &str) -> String {
    if from.starts_with("file://") {
        from.to_owned()
    } else {
        format!("https://{from}")
    }
}

fn unreachable_repo(from: &str, why: &str) -> Failure {
    (
        codes::E0601,
        format!("the repository {} can't be reached: {why}", url(from)),
    )
}
