//! The packages a command reads (packages.manifest): it fills in the manifests of the root package
//! and of its path dependencies (packages.filling-in), checking each version it writes against the
//! change in the API since the repository's previous version (versions.checked-versions), checks
//! each request that a higher version serves (versions.selection), and reports each package it
//! fetched.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::{LazyLock, Mutex};

use serde_json::{Value, json};
use stilt_db::{Database, Program};
use stilt_diag::File;
use stilt_pkg::api::{Api, Apis};
use stilt_pkg::fetch::{Cache, Fetched};

use crate::report::{Report, text};

pub(crate) mod api;

/// The APIs of packages, each found by checking the package as a program of its own
/// (packages.dependencies-with-errors). A fetched package's directory in the cache holds the
/// content its hash names, so what is found for it holds for as long as the process runs.
pub(crate) struct Checked;

static FOUND: LazyLock<Mutex<HashMap<PathBuf, Result<Api, String>>>> =
    LazyLock::new(Mutex::default);

impl Apis for Checked {
    fn api(&mut self, dir: &Path) -> Result<Api, String> {
        let id = dir.canonicalize().unwrap_or_else(|_| dir.to_path_buf());
        if let Some(found) = FOUND.lock().map_or(None, |found| found.get(&id).cloned()) {
            return found;
        }
        let found = checked(dir);
        if let Ok(mut all) = FOUND.lock() {
            all.insert(id, found.clone());
        }
        found
    }
}

/// The API of the package in `dir`, or the code and the place of its first error.
fn checked(dir: &Path) -> Result<Api, String> {
    let db = Database::default();
    let program = stilt_db::load(&db, dir)?;
    let name = (program.packages(&db).root())
        .and_then(|root| root.name.clone())
        .unwrap_or_default();
    let diagnostics = stilt_rc::check_in_parallel(&db, program);
    let found = match diagnostics.iter().find(|d| d.diagnostic.is_error()) {
        Some(d) => {
            let text = text(&db, d.file);
            let position = File::new(d.file.path(&db), &text).position(d.diagnostic.range.start());
            Err(format!(
                "{} at {name}/{}:{position}",
                d.diagnostic.code,
                d.file.path(&db)
            ))
        }
        None => Ok(api::extract(&db, program, &name)),
    };
    crate::end(db);
    found
}

/// Reads the program at `path` into `db`, filling in its manifests.
///
/// # Errors
///
/// A message for people, when `path` is no program or can't be read.
pub(crate) fn load(db: &Database, path: &Path) -> Result<Program, String> {
    stilt_db::load_with(db, path, &mut Checked, true)
}

/// Fills in the manifests of the program at `path` and fetches the packages it needs, before a
/// command reads it in this process or in its engine, and gives the packages fetched.
pub(crate) fn prepare(path: &Path) -> Vec<Fetched> {
    if !path.join("stilt.toml").is_file() {
        return Vec::new();
    }
    let mut cache = Cache::from_env();
    stilt_db::read_with(path, &mut Checked, &mut cache, true)
        .map_or_else(|_| Vec::new(), |read| read.fetched)
}

/// The report of `f`, after preparing the program at `path`, with each package fetched on
/// stderr before it, and with `json` in the list `fetched` of the object it writes.
pub(crate) fn reported(path: &Path, json: bool, f: impl FnOnce() -> Report) -> Report {
    let fetched = prepare(path);
    let mut report = f();
    if fetched.is_empty() {
        return report;
    }
    report.stderr = format!("{}{}", lines(&fetched), report.stderr);
    if json {
        let mut object: Value = serde_json::from_str(&report.stdout).unwrap_or_else(|_| json!({}));
        object["fetched"] = fetched
            .iter()
            .map(|f| {
                json!({
                    "name": f.name,
                    "from": f.from,
                    "version": f.version.to_string(),
                    "hash": f.hash,
                })
            })
            .collect();
        report.stdout = format!("{object}\n");
    }
    report
}

/// Each package fetched, as a line for people: `fetched csv 2.1.0 from REPOSITORY, b3:HASH`.
pub(crate) fn lines(fetched: &[Fetched]) -> String {
    fetched.iter().fold(String::new(), |mut lines, f| {
        let _ = writeln!(
            lines,
            "fetched {} {} from {}, {}",
            f.name, f.version, f.from, f.hash
        );
        lines
    })
}
