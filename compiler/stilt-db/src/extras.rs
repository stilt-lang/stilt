//! The inputs that checking a program makes as it goes, which a database keeps so that the
//! same request finds the same input again: the programs that check procedural macros' modules on
//! their own, and the files that macros' uses name (macros.expansion-order and macros.named-files).
//!
//! A procedural macro's module is checked with the modules it imports as a program of its own,
//! whose files are the program's, so that what is computed of them is shared, and whose checking
//! never reaches the module that uses the macro. A file that a use names is an input of its own,
//! which [`refresh_named_files`] reads again, so that an edit of it expands only the uses that
//! name it again (sandboxed-compile-time-code).

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, PoisonError};

use salsa::{Durability, Setter};

use crate::{Db, Packages, Program, SourceFile, program_of_packages};

pub use named::NamedFile;

// Apart because salsa's input macro writes the constructor, builder and setters with no docs,
// outside the struct, where only a module's lint level reaches.
#[allow(missing_docs)]
mod named {
    use super::Unread;

    /// A file that a procedural macro's use names: what reading it gave, its text, or why it
    /// can't be given to a macro (macros.named-files).
    #[salsa::input(debug)]
    pub struct NamedFile {
        /// The file's text, or why it can't be given to the macro.
        #[returns(ref)]
        pub read: Result<String, Unread>,
    }
}

/// Why a file can't be given to a macro, as E0229 says, and the path that names the entries
/// whose names differ from the path's only in case, when there are such entries.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Unread {
    /// Why the file can't be read, as E0229 gives it.
    pub why: String,
    /// The path that names the entries differing from the path only in case, if any.
    pub meant: Option<String>,
}

impl Unread {
    fn new(why: String) -> Self {
        Self { why, meant: None }
    }
}

/// What a database keeps of the inputs made while checking.
#[derive(Clone, Default)]
pub struct Extras(Arc<Mutex<Kept>>);

#[derive(Default)]
struct Kept {
    programs: Vec<((Vec<SourceFile>, Packages), Program)>,
    named: HashMap<(PathBuf, String), NamedFile>,
}

impl Extras {
    fn kept(&self) -> std::sync::MutexGuard<'_, Kept> {
        self.0.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

impl std::fmt::Debug for Extras {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Extras").finish_non_exhaustive()
    }
}

/// The program of `files`, sorted by path, with the standard library and `packages`: the same
/// input for the same files and packages.
pub fn program_of(db: &dyn Db, files: Vec<SourceFile>, packages: Packages) -> Program {
    let key = (files, packages);
    let found = |kept: &Kept| {
        kept.programs
            .iter()
            .find(|(k, _)| *k == key)
            .map(|(_, p)| *p)
    };
    if let Some(p) = found(&db.extras().kept()) {
        return p;
    }
    let program = program_of_packages(db, key.0.clone(), key.1.clone());
    let mut kept = db.extras().kept();
    if let Some(p) = found(&kept) {
        return p;
    }
    kept.programs.push((key, program));
    program
}

/// The file at `path` from `dir`, as a macro's use names it, read once and then kept.
pub fn named_file(db: &dyn Db, dir: &Path, path: &str) -> NamedFile {
    let key = (dir.to_path_buf(), path.to_owned());
    if let Some(&f) = db.extras().kept().named.get(&key) {
        return f;
    }
    let file = NamedFile::builder(read_named(dir, path))
        .durability(Durability::LOW)
        .new(db);
    *db.extras().kept().named.entry(key).or_insert(file)
}

/// Reads again each file that a use named, changes those whose reading changed, and tells whether
/// any did, so that the uses that name them expand again (macros.named-files;
/// sandboxed-compile-time-code).
pub fn refresh_named_files(db: &mut dyn Db) -> bool {
    let named: Vec<((PathBuf, String), NamedFile)> = db
        .extras()
        .kept()
        .named
        .iter()
        .map(|(k, f)| (k.clone(), *f))
        .collect();
    let mut changed = false;
    for ((dir, path), file) in named {
        let read = read_named(&dir, &path);
        if *file.read(db) != read {
            let _old = file.set_read(db).to(read);
            changed = true;
        }
    }
    changed
}

/// Reads the file `path` from `dir` (macros.named-files): names separated by `/`, none empty, `.`
/// or `..`, none starting with `.`, each matching an entry of its directory byte for byte,
/// naming a regular file whose real path lies inside `dir` and whose contents are UTF-8.
///
/// # Errors
///
/// Why the path can't be given to a macro, as E0229 says, with the directories named as the path
/// names them.
pub fn read_named(dir: &Path, path: &str) -> Result<String, Unread> {
    let names: Vec<&str> = path.split('/').collect();
    if names
        .iter()
        .any(|n| n.is_empty() || *n == "." || *n == ".." || n.starts_with('.'))
    {
        return Err(Unread::new(format!(
            "`{path}` isn't a path a macro can be given: its names are separated by `/`, and \
             none is empty, `.` or `..`, or starts with `.`"
        )));
    }
    let at = walk(dir, &names)?;
    let unreadable = || Unread::new(format!("`{path}` can't be read"));
    let meta = fs::metadata(&at).map_err(|_| unreadable())?;
    if !meta.is_file() {
        return Err(Unread::new(format!("`{path}` isn't a regular file")));
    }
    let inside = match (fs::canonicalize(dir), fs::canonicalize(&at)) {
        (Ok(d), Ok(f)) => f.starts_with(&d) && f != d,
        _ => false,
    };
    if !inside {
        return Err(Unread::new(format!(
            "`{path}` lies outside the package's directory"
        )));
    }
    let bytes = fs::read(&at).map_err(|_| unreadable())?;
    String::from_utf8(bytes).map_err(|_| Unread::new(format!("`{path}` isn't UTF-8")))
}

/// The entry that `names` name from `dir`, each matching an entry of its directory byte for
/// byte, or why one doesn't, with the path the entries that match without case would give.
fn walk(dir: &Path, names: &[&str]) -> Result<PathBuf, Unread> {
    let mut at = dir.to_path_buf();
    for (k, name) in names.iter().enumerate() {
        let written = names[..k].join("/");
        let shown = if k == 0 {
            "the package's directory".to_owned()
        } else {
            format!("`{written}`")
        };
        let Ok(entries) = fs::read_dir(&at) else {
            return Err(Unread::new(format!("{shown} isn't a directory")));
        };
        let entries: Vec<String> = entries
            .filter_map(Result::ok)
            .map(|e| e.file_name().to_string_lossy().into_owned())
            .collect();
        if !entries.iter().any(|e| e == name) {
            let close = entries.iter().find(|e| e.eq_ignore_ascii_case(name));
            let why = match close {
                Some(e) => format!("{shown} has no entry named `{name}`, but one named `{e}`"),
                None => format!("{shown} has no entry named `{name}`"),
            };
            let meant = close.and_then(|e| {
                let mut fixed: Vec<&str> = names.to_vec();
                fixed[k] = e;
                let fixed = fixed.join("/");
                match walk(dir, &fixed.split('/').collect::<Vec<_>>()) {
                    Ok(_) => Some(fixed),
                    Err(later) => later.meant,
                }
            });
            return Err(Unread { why, meant });
        }
        at.push(name);
    }
    Ok(at)
}
