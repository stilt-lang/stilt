//! The project that every language's version of the shootout is: `modules` modules, each a
//! record type and `functions` functions, function `j` of module `i` calling function `j` of
//! module `i - 1`, so that each module depends on the one before it, as a layered program's
//! do, and `main` calls the last module's. Every version computes the same numbers, written as
//! its language's programmers write them, and prints what the others print.
//!
//! An edit rewrites the module in the middle: its first function adds another constant, which
//! changes what `main` prints, or the edit breaks its first line with a type error.

use std::path::{Path, PathBuf};

use super::Language;

/// The size of a project.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Shape {
    pub(crate) modules: usize,
    pub(crate) functions: usize,
}

impl Shape {
    /// The shape whose versions hold about `lines` lines.
    pub(crate) fn of_lines(lines: usize) -> Self {
        let functions = 20;
        Self {
            modules: (lines / (functions * 10)).max(2),
            functions,
        }
    }

    /// The module that edits rewrite.
    pub(crate) fn edited(self) -> usize {
        self.modules / 2
    }
}

/// What an edit makes of the first function of the middle module.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Edit {
    /// It adds this to the constant it adds.
    Plus(usize),
    /// Its first line is a type error.
    Broken,
}

/// The constant that function `j` of module `i` adds, which no other function adds, so that no
/// two functions have the same body.
fn constant(i: usize, j: usize) -> usize {
    i * 100 + j + 1
}

/// The text of one function: its constant, the call of the module before it, and whether it is
/// broken.
pub(crate) struct Function {
    pub(crate) i: usize,
    pub(crate) j: usize,
    pub(crate) constant: usize,
    pub(crate) broken: bool,
}

impl Function {
    fn new(i: usize, j: usize, edit: Option<Edit>) -> Self {
        let edited = if j == 0 { edit } else { None };
        Self {
            i,
            j,
            constant: constant(i, j)
                + if let Some(Edit::Plus(n)) = edited {
                    n
                } else {
                    0
                },
            broken: edited == Some(Edit::Broken),
        }
    }
}

/// Writes the project in `language` into the empty directory `dir`.
pub(crate) fn write(language: Language, dir: &Path, shape: Shape) -> Result<(), String> {
    for (path, text) in language.scaffold(shape) {
        put(&dir.join(path), &text)?;
    }
    for i in 0..shape.modules {
        rewrite(language, dir, shape, i, None)?;
    }
    Ok(())
}

/// Writes module `i` again, with `edit` made to its first function.
pub(crate) fn rewrite(
    language: Language,
    dir: &Path,
    shape: Shape,
    i: usize,
    edit: Option<Edit>,
) -> Result<(), String> {
    let functions: Vec<Function> = (0..shape.functions)
        .map(|j| Function::new(i, j, edit))
        .collect();
    put(
        &dir.join(language.module_path(i)),
        &language.module(i, &functions),
    )
}

/// The number of lines of a version.
pub(crate) fn lines(dir: &Path) -> usize {
    let mut count = 0;
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        for entry in std::fs::read_dir(&d).into_iter().flatten().flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if is_source(&path) {
                count += std::fs::read_to_string(&path).map_or(0, |t| t.lines().count());
            }
        }
    }
    count
}

fn is_source(path: &Path) -> bool {
    path.extension()
        .is_some_and(|e| ["lt", "rs", "go", "ml", "swift"].iter().any(|s| e == *s))
}

fn put(path: &PathBuf, text: &str) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)
            .map_err(|e| format!("cannot write {}: {e}", parent.display()))?;
    }
    std::fs::write(path, text).map_err(|e| format!("cannot write {}: {e}", path.display()))
}
