//! What the tests of fetched packages share (packages.fetching and packages.checked-content): git
//! repositories that a test makes, reached through `file://` URLs, and a cache of its own, so that
//! no test reaches the network or another test's packages. Each command runs with an empty `PATH`,
//! so it fetches on a machine where only `stilt` is installed. The snapshots of diagnostics build
//! their repositories from fixtures with the same writer ([`build`]).

#![allow(dead_code, reason = "each test uses some of these")]

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use serde_json::Value;

/// A test's directory: its repositories, its program and its cache.
pub(crate) struct Place {
    pub(crate) dir: PathBuf,
}

impl Place {
    /// A directory of the test's own, emptied.
    pub(crate) fn new(name: &str) -> Self {
        let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
            .join("packages")
            .join(name);
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("the directory can be made");
        Self { dir }
    }

    /// A git repository named `name`, with no commit.
    pub(crate) fn repo(&self, name: &str) -> Repo {
        Repo::at(&self.dir.join("repos").join(name))
    }

    /// The program `app`, whose files are `files`.
    pub(crate) fn program(&self, files: &[(&str, &str)]) -> PathBuf {
        let dir = self.dir.join("app");
        write(&dir, files);
        dir
    }

    /// Runs `stilt` with `args` and `path` last, with the place's cache, `home` under it, and
    /// stops the engine the command may have started.
    pub(crate) fn stilt(&self, home: &str, args: &[&str], path: &Path) -> Output {
        self.stilt_trusting(home, args, path, None)
    }

    /// Runs `stilt` as [`Place::stilt`] does, trusting the certificates of the file `roots`
    /// as well as the usual ones, or only the usual ones without it.
    pub(crate) fn stilt_trusting(
        &self,
        home: &str,
        args: &[&str],
        path: &Path,
        roots: Option<&Path>,
    ) -> Output {
        let mut command = Command::new(env!("CARGO_BIN_EXE_stilt"));
        command.args(args).arg(path);
        command
            .env("STILT_HOME", self.dir.join(home))
            .env("PATH", "");
        match roots {
            Some(roots) => command.env("SSL_CERT_FILE", roots),
            None => command.env_remove("SSL_CERT_FILE"),
        };
        let output = command.output().expect("stilt runs");
        let _ = Command::new(env!("CARGO_BIN_EXE_stilt"))
            .args(["engine", "--stop"])
            .arg(path)
            .output();
        output
    }

    /// The JSON object that `stilt check --json` writes for the program at `path`.
    pub(crate) fn check(&self, home: &str, path: &Path) -> Value {
        let output = self.stilt(home, &["check", "--json"], path);
        serde_json::from_slice(&output.stdout).unwrap_or_else(|_| {
            panic!(
                "check writes JSON: {}",
                String::from_utf8_lossy(&output.stderr)
            )
        })
    }
}

/// The codes of the diagnostics of a `check --json`, in order.
pub(crate) fn codes(checked: &Value) -> Vec<String> {
    checked["diagnostics"]
        .as_array()
        .map(|all| {
            (all.iter())
                .filter_map(|d| d["code"].as_str().map(str::to_owned))
                .collect()
        })
        .unwrap_or_default()
}

/// The message of the diagnostic of a `check --json` with `code`.
pub(crate) fn message(checked: &Value, code: &str) -> String {
    let all = checked["diagnostics"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    let found = all.iter().find(|d| d["code"] == code);
    let found = found.unwrap_or_else(|| panic!("a diagnostic {code} in {checked}"));
    found["message"].as_str().unwrap_or_default().to_owned()
}

/// A git repository of a test.
pub(crate) struct Repo {
    pub(crate) dir: PathBuf,
}

impl Repo {
    /// A git repository at `dir`, emptied, with no commit.
    pub(crate) fn at(dir: &Path) -> Self {
        let _ = fs::remove_dir_all(dir);
        fs::create_dir_all(dir).expect("the repository can be made");
        git(dir, &["init", "--quiet"]);
        Self {
            dir: dir.to_path_buf(),
        }
    }

    /// Commits `files` as the repository's whole tree, and tags the commit `v` and `version`.
    pub(crate) fn tag(&self, version: &str, files: &[(&str, &str)]) {
        for entry in fs::read_dir(&self.dir).expect("the repository is a directory") {
            let path = entry.expect("an entry").path();
            if path.file_name().is_some_and(|name| name != ".git") {
                let _ = fs::remove_dir_all(&path).or_else(|_| fs::remove_file(&path));
            }
        }
        write(&self.dir, files);
        git(&self.dir, &["add", "--all"]);
        git(
            &self.dir,
            &["commit", "--quiet", "--allow-empty", "-m", version],
        );
        git(&self.dir, &["tag", "--force", &format!("v{version}")]);
    }

    /// Packs the repository's objects, so that a fetch reads them from a pack.
    pub(crate) fn pack(&self) {
        git(&self.dir, &["gc", "--quiet", "--aggressive"]);
    }

    /// The URL that a manifest gives the repository by.
    pub(crate) fn url(&self) -> String {
        format!("file://{}", self.dir.display())
    }
}

/// Builds under `to` a repository for each directory of `fixture`, whose directories, each named
/// by a version such as `1.4.0`, hold the trees that it tags, in the order of their versions.
pub(crate) fn build(fixture: &Path, to: &Path) {
    for repo in entries(fixture).into_iter().filter(|path| path.is_dir()) {
        let name = repo.file_name().expect("a repository has a name");
        let built = Repo::at(&to.join(name));
        let mut versions: Vec<(Vec<u64>, PathBuf)> = entries(&repo)
            .into_iter()
            .map(|tree| {
                let name = tree.file_name().unwrap_or_default().to_string_lossy();
                let numbers = name.split('.').filter_map(|n| n.parse().ok()).collect();
                (numbers, tree)
            })
            .collect();
        versions.sort();
        for (_, tree) in versions {
            let mut files = Vec::new();
            read_tree(&tree, "", &mut files);
            let files: Vec<(&str, &str)> = files
                .iter()
                .map(|(p, t)| (p.as_str(), t.as_str()))
                .collect();
            let version = tree.file_name().unwrap_or_default().to_string_lossy();
            built.tag(&version, &files);
        }
    }
}

fn entries(dir: &Path) -> Vec<PathBuf> {
    let mut all: Vec<PathBuf> = fs::read_dir(dir)
        .expect("the fixture is readable")
        .map(|e| e.expect("an entry").path())
        .collect();
    all.sort();
    all
}

/// The files under `dir`, each by its path from the tree's root and its text.
fn read_tree(dir: &Path, prefix: &str, files: &mut Vec<(String, String)>) {
    for path in entries(dir) {
        let name = path.file_name().unwrap_or_default().to_string_lossy();
        let relative = format!("{prefix}{name}");
        if path.is_dir() {
            read_tree(&path, &format!("{relative}/"), files);
        } else {
            files.push((
                relative,
                fs::read_to_string(&path).expect("the fixture is text"),
            ));
        }
    }
}

/// The content hash of a package whose files are `files`, as packages.content-hash defines it.
pub(crate) fn content_hash(files: &[(&str, &str)]) -> String {
    let mut built: Vec<&(&str, &str)> = files
        .iter()
        .filter(|(path, _)| {
            *path == "stilt.toml" || (path.starts_with("src/") && path.as_bytes().ends_with(b".lt"))
        })
        .collect();
    built.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
    let lines = built.iter().fold(String::new(), |mut lines, (path, text)| {
        let _ = writeln!(lines, "{}  {path}", blake3::hash(text.as_bytes()).to_hex());
        lines
    });
    format!("b3:{}", blake3::hash(lines.as_bytes()).to_hex())
}

fn write(dir: &Path, files: &[(&str, &str)]) {
    for (path, text) in files {
        let path = dir.join(path);
        fs::create_dir_all(path.parent().expect("a parent")).expect("the directory can be made");
        fs::write(path, text).expect("the file can be written");
    }
}

fn git(dir: &Path, args: &[&str]) {
    let output = Command::new("git")
        .args([
            "-c",
            "user.name=stilt",
            "-c",
            "user.email=stilt@example.com",
        ])
        .args(["-c", "commit.gpgsign=false", "-c", "tag.gpgsign=false"])
        .args(["-c", "init.defaultBranch=main"])
        .args(args)
        .current_dir(dir)
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .output()
        .expect("git runs");
    assert!(output.status.success(), "git {args:?}: {output:?}");
}
