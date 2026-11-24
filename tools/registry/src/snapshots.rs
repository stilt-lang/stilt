//! The snapshots of `tests/diagnostics/`: each program, whose name starts with the code it
//! makes the compiler report, with the rendering of `stilt check` that was reviewed for it.

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

/// Where the snapshots are, from the repository's root.
pub(crate) const DIR: &str = "tests/diagnostics";

/// A program of the snapshots and its rendering.
#[derive(Debug)]
pub(crate) struct Snapshot {
    /// Its name, such as `E0311_mismatched_types.lt` or `E0213_private_item`.
    pub(crate) name: String,
    /// Its files, each by its path within the program, or the one file that it is.
    pub(crate) files: Vec<(String, String)>,
    /// The files beside it that its check reads, each by its name: the edits of its command,
    /// for the refusal of an edit (edits.refusals), and its profile (builds.profile-form).
    pub(crate) fixtures: Vec<(String, String)>,
    /// Whether the repositories it fetches from are beside it (packages.fetching).
    pub(crate) repos: bool,
    /// What `stilt check` prints for it.
    pub(crate) rendering: String,
}

impl Snapshot {
    /// Whether it is a program of one file, which the error index can show as an example.
    pub(crate) fn is_one_file(&self) -> bool {
        is_source(&self.name) && self.fixtures.is_empty() && !self.repos
    }
}

/// The snapshots under `dir`, by the code each is of, each code's in the order of their names.
pub(crate) fn read(dir: &Path) -> Result<BTreeMap<String, Vec<Snapshot>>, String> {
    let unreadable = |path: &Path, e: std::io::Error| format!("{}: {e}", path.display());
    let mut names: Vec<String> = fs::read_dir(dir)
        .map_err(|e| unreadable(dir, e))?
        .filter_map(Result::ok)
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .filter(|name| name.ends_with(".stderr"))
        .collect();
    names.sort();
    let mut out: BTreeMap<String, Vec<Snapshot>> = BTreeMap::new();
    for stderr in names {
        let base = stderr.trim_end_matches(".stderr");
        let rendering = fs::read_to_string(dir.join(&stderr)).map_err(|e| unreadable(dir, e))?;
        let file = dir.join(format!("{base}.lt"));
        let (name, files) = if file.is_file() {
            let text = fs::read_to_string(&file).map_err(|e| unreadable(&file, e))?;
            let name = format!("{base}.lt");
            (name.clone(), vec![(name, text)])
        } else {
            let mut files = Vec::new();
            program_files(&dir.join(base), "", &mut files)?;
            (base.to_owned(), files)
        };
        let mut fixtures = Vec::new();
        for extension in ["edits", "profile"] {
            let fixture = format!("{base}.{extension}");
            if let Ok(text) = fs::read_to_string(dir.join(&fixture)) {
                fixtures.push((fixture, text));
            }
        }
        let repos = dir.join(format!("{base}.repos")).is_dir();
        let code = base.split('_').next().unwrap_or(base).to_owned();
        let snapshot = Snapshot {
            name,
            files,
            fixtures,
            repos,
            rendering,
        };
        out.entry(code).or_default().push(snapshot);
    }
    Ok(out)
}

/// Adds the files under `dir`, a directory of a program, with their paths after `prefix`, in
/// the order of their paths.
fn program_files(
    dir: &Path,
    prefix: &str,
    files: &mut Vec<(String, String)>,
) -> Result<(), String> {
    let unreadable = |e: std::io::Error| format!("{}: {e}", dir.display());
    let mut entries: Vec<_> = fs::read_dir(dir)
        .map_err(unreadable)?
        .filter_map(Result::ok)
        .map(|e| e.path())
        .collect();
    entries.sort();
    for path in entries {
        let name = path.file_name().unwrap_or_default().to_string_lossy();
        let inner = format!("{prefix}{name}");
        if path.is_dir() {
            program_files(&path, &format!("{inner}/"), files)?;
        } else {
            files.push((inner, fs::read_to_string(&path).map_err(unreadable)?));
        }
    }
    Ok(())
}

/// Whether `path` names a source file of Stilt.
pub(crate) fn is_source(path: &str) -> bool {
    Path::new(path).extension().is_some_and(|e| e == "lt")
}
