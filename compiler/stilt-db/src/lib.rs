//! The query database of Stilt's compiler. Every phase is a query: a pure function of its
//! inputs, whose result the database keeps, and computes again only when an input it read has
//! changed (Compiler architecture). The inputs are the source files of a program and of the
//! standard library.
//!
//! Each input has the durability of how often it changes, so that an edit never checks again
//! the queries that read only inputs that change less often (goal edit-to-diagnostics): a program
//! file's contents change with each edit; the list of a program's files when a file is added or
//! removed; and a file's place, the standard library and the list of its files never, a moved
//! file being a new input. The contents of the files a session hasn't edited yet keep the low
//! durability of the others: salsa can't backdate a query whose inputs lost durability, so their
//! first edit would check every body that reads them again (goal body-edits-recheck-one-body).
//!
//! Its place among the crates (`compiler/README.md`): it depends on `stilt-diag`, `stilt-syntax`
//! and `stilt-pkg`, and on none of the phases that run as its queries. The host installs what
//! asks the system's loader for a package's C libraries (`install_library_finder`).
#![warn(missing_docs)]

mod database;
mod extras;
mod packages;
pub mod parallel;
mod program;

use salsa::Durability;

pub use database::Database;
pub use extras::{
    Extras, NamedFile, Unread, named_file, program_of, read_named, refresh_named_files,
};
pub use packages::{
    Dependency, Grant, Granting, PackageInfo, Packages, file_packages, package_of, reported_files,
};
pub use program::{
    PINS, Source, install_library_finder, load, load_with, read, read_with, sources,
};

mod embedded {
    include!(concat!(env!("OUT_DIR"), "/std.rs"));
}

pub use inputs::{Program, SourceFile};

// The program's inputs, apart because salsa's input macro writes their constructors, builders
// and setters with no docs, outside the structs, where only a module's lint level reaches.
#[allow(missing_docs)]
mod inputs {
    use crate::Packages;

    /// A source file of a program or of the standard library.
    #[salsa::input(debug)]
    pub struct SourceFile {
        /// The path that reports name the file by: relative to the program's root directory, with
        /// `/` as the separator. The standard library's files are under `std/`.
        #[returns(ref)]
        pub path: String,
        /// The names that the file's place gives its module (program.module-names), which may not be
        /// valid names: `["orders", "store"]` for `src/orders/store.lt` in a package.
        #[returns(ref)]
        pub module_path: Vec<String>,
        /// The file's contents, which may break lexical.source-text.
        #[returns(ref)]
        pub bytes: Vec<u8>,
    }

    /// A program: its source files, sorted by path (program.forms), the standard library's, and
    /// its packages (packages.manifest).
    #[salsa::input(debug)]
    pub struct Program {
        /// The program's own source files.
        #[returns(ref)]
        pub files: Vec<SourceFile>,
        /// The standard library's source files.
        #[returns(ref)]
        pub std: Vec<SourceFile>,
        /// The program's packages, the root first.
        #[returns(ref)]
        pub packages: Packages,
    }
}

/// The standard library's files, which every program of a database shares.
#[salsa::input(singleton, debug)]
struct StandardLibrary {
    #[returns(ref)]
    files: Vec<SourceFile>,
}

/// Whether the standard library's files are read with their doc examples, which only
/// `stilt test --std` runs (std.examples). Every other command reads them with each
/// `/// ex:` line left as an empty `///`, which keeps every position and spares each program
/// the parsing and checking of the library's own tests.
static STD_EXAMPLES: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Makes the databases that this process creates from now on read the standard library with
/// its doc examples.
pub fn read_std_examples() {
    STD_EXAMPLES.store(true, std::sync::atomic::Ordering::Relaxed);
}

/// `text` with each line that holds a doc example, `/// ex:` after any indentation, cut to its
/// `///`, so that the line stays and holds no example.
fn without_examples(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for line in text.split_inclusive('\n') {
        let rest = line.trim_start_matches(' ');
        if rest
            .strip_prefix("///")
            .is_some_and(|doc| doc.trim_start().starts_with("ex:"))
        {
            out.push_str(&line[..line.len() - rest.len()]);
            out.push_str("///");
            if line.ends_with('\n') {
                out.push('\n');
            }
        } else {
            out.push_str(line);
        }
    }
    out
}

/// The standard library's source files, which are built into the compiler, sorted by path.
/// They change only with the compiler, so their durability is high, and an edit to a program
/// never checks whether a query that read only them must run again. A database makes them
/// once, so that every program it holds, and every version of a program's list of files,
/// shares what was computed of them.
pub fn standard_library(db: &dyn Db) -> Vec<SourceFile> {
    if let Some(std) = StandardLibrary::try_get(db) {
        return std.files(db).clone();
    }
    let examples = STD_EXAMPLES.load(std::sync::atomic::Ordering::Relaxed);
    let files: Vec<SourceFile> = embedded::STD
        .iter()
        .map(|&(path, text)| {
            let mut module_path = vec!["std".to_owned()];
            module_path.extend(path.trim_end_matches(".lt").split('/').map(str::to_owned));
            let text = if examples {
                text.to_owned()
            } else {
                without_examples(text)
            };
            SourceFile::builder(format!("std/{path}"), module_path, text.into_bytes())
                .durability(Durability::HIGH)
                .new(db)
        })
        .collect();
    let _ = StandardLibrary::builder(files.clone())
        .durability(Durability::HIGH)
        .new(db);
    files
}

/// A source file of a program, whose place never changes: only its contents do.
pub fn source_file(
    db: &dyn Db,
    path: String,
    module_path: Vec<String>,
    bytes: Vec<u8>,
) -> SourceFile {
    SourceFile::builder(path, module_path, bytes)
        .path_durability(Durability::HIGH)
        .module_path_durability(Durability::HIGH)
        .new(db)
}

/// A program of `files`, sorted by path, with the standard library, and no manifest. Its list of
/// files changes only when a file is added or removed.
pub fn program(db: &dyn Db, files: Vec<SourceFile>) -> Program {
    program_of_packages(db, files, Packages::default())
}

/// A program of `files`, sorted by path, with the standard library, whose manifests give
/// `packages`. They change only when a file is added or removed, or a manifest changes.
pub fn program_of_packages(db: &dyn Db, files: Vec<SourceFile>, packages: Packages) -> Program {
    Program::builder(files, standard_library(db), packages)
        .files_durability(Durability::MEDIUM)
        .std_durability(Durability::HIGH)
        .packages_durability(Durability::MEDIUM)
        .new(db)
}

/// A database that queries run in.
#[salsa::db]
pub trait Db: salsa::Database {
    /// The inputs made while checking, which the database keeps ([`Extras`]).
    fn extras(&self) -> &Extras;
}

/// The parse of a source file. Its tree is the largest result the database keeps of a file,
/// and the queries after it read what they need of it once, so an engine keeps only the
/// trees it read last ([`syntax_error`], [`syntax_warnings`]; goal bounded-cache).
#[salsa::tracked(returns(ref), lru = 0)]
pub fn parse(db: &dyn Db, file: SourceFile) -> stilt_syntax::Parse {
    if is_std_file(db, file) {
        stilt_syntax::parse_native_bytes(file.bytes(db))
    } else {
        stilt_syntax::parse_bytes(file.bytes(db))
    }
}

/// Whether a file is the standard library's, whose path and module both start at `std`.
fn is_std_file(db: &dyn Db, file: SourceFile) -> bool {
    file.path(db).starts_with("std/") && file.module_path(db).first().is_some_and(|m| m == "std")
}

/// Keeps the trees of only the `n` files parsed last, from the next revision on, or every
/// tree when `n` is 0, as a database does unless told otherwise.
pub fn keep_trees(db: &mut dyn Db, n: usize) {
    parse::set_lru_capacity(db, n);
}

/// The first syntax error of a source file, if it has one.
#[salsa::tracked(returns(ref))]
pub fn syntax_error(db: &dyn Db, file: SourceFile) -> Option<stilt_diag::Diagnostic> {
    parse(db, file).error().cloned()
}

/// What the syntax errors of a source file make of it: the first syntax error of each part
/// that has one, the text of each such part, in which no other diagnostic is reported, and
/// whether the file breaks lexical.source-text, so that every path into its module has the error
/// type (errors.invalid-source-text and errors.error-type).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SyntaxErrors {
    /// The syntax errors, each as a diagnostic.
    pub errors: Vec<stilt_diag::Diagnostic>,
    /// The ranges of the text that the errors hold.
    pub held: Vec<stilt_syntax::TextRange>,
    /// Whether the file breaks lexical.source-text.
    pub unreadable: bool,
}

impl SyntaxErrors {
    /// Whether a part with a syntax error holds back `d`: one whose text holds its primary
    /// span, but for E0200, which is about the file's name.
    #[must_use]
    pub fn holds_back(&self, d: &stilt_diag::Diagnostic) -> bool {
        let at = d.range.start();
        d.code != stilt_diag::codes::E0200
            && self.held.iter().any(|r| r.start() <= at && at < r.end())
    }
}

/// Whether a source file breaks lexical.source-text, so that it declares nothing and every path
/// into its module has the error type (errors.invalid-source-text).
#[salsa::tracked]
pub fn unreadable(db: &dyn Db, file: SourceFile) -> bool {
    parse(db, file).unreadable()
}

/// The syntax errors of a source file.
#[salsa::tracked(returns(ref))]
pub fn syntax_errors(db: &dyn Db, file: SourceFile) -> SyntaxErrors {
    let parse = parse(db, file);
    SyntaxErrors {
        errors: parse.errors().to_vec(),
        held: parse.held().to_vec(),
        unreadable: parse.unreadable(),
    }
}

/// The warnings of a source file's syntax, about commented-out code.
#[salsa::tracked(returns(ref))]
pub fn syntax_warnings(db: &dyn Db, file: SourceFile) -> Vec<stilt_diag::Diagnostic> {
    parse(db, file).warnings().to_vec()
}

#[cfg(test)]
mod tests;
