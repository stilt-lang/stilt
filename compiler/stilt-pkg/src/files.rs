//! The files below a module root that are modules (program.module-names): each regular file
//! whose name ends in `.lt`, found through symbolic links, at the link's path, but for the
//! entries whose names start with `.` and the links that would make a cycle.

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

/// The paths, from `root` and written with `/`, of the files below `root` that are modules,
/// sorted.
///
/// # Errors
///
/// When a directory can't be read.
pub fn module_files(root: &Path) -> io::Result<Vec<String>> {
    let mut files = Vec::new();
    let mut through = vec![fs::canonicalize(root)?];
    walk(root, "", &mut through, &mut files)?;
    files.sort();
    Ok(files)
}

/// Adds the modules' files below `dir`, whose path from the module root is `relative`, to
/// `files`; `through` holds the real paths of the directories that the walk passes through to
/// reach `dir`, `dir`'s last.
fn walk(
    dir: &Path,
    relative: &str,
    through: &mut Vec<PathBuf>,
    files: &mut Vec<String>,
) -> io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let name = entry.file_name().to_string_lossy().into_owned();
        if name.starts_with('.') {
            continue;
        }
        let path = if relative.is_empty() {
            name.clone()
        } else {
            format!("{relative}/{name}")
        };
        let own = entry.file_type()?;
        // A link that names nothing, or a chain of links that never ends, names no file.
        let Ok(named) = (if own.is_symlink() {
            fs::metadata(entry.path()).map(|m| m.file_type())
        } else {
            Ok(own)
        }) else {
            continue;
        };
        if named.is_dir() {
            let real = fs::canonicalize(entry.path())?;
            if own.is_symlink() && through.iter().any(|d| d.starts_with(&real)) {
                continue;
            }
            through.push(real);
            walk(&entry.path(), &path, through, files)?;
            through.pop();
        } else if named.is_file() && Path::new(&name).extension().is_some_and(|e| e == "lt") {
            files.push(path);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
