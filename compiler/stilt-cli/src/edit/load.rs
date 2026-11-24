//! The program's own files as `check --edit` and `show` read them: each with its module, its
//! text and its parts (edits.parts).

use std::fs::File;
use std::io::{self, Read as _};
use std::path::{Path, PathBuf};

use stilt_edit::{Part, canonical, hash, parts};

/// A source file of the program, read from disk.
#[derive(Debug)]
pub(crate) struct LoadedFile {
    /// The path that reports name the file by.
    pub(crate) path: String,
    /// Where it is.
    pub(crate) disk: PathBuf,
    pub(crate) module: String,
    /// The index of its package, and its module's name in that package, as the package names
    /// it when it is the root (docs.lock-file).
    pub(crate) package: usize,
    pub(crate) local: String,
    pub(crate) bytes: Vec<u8>,
    /// Its text, when it is UTF-8, and the parts of that text. A file that isn't has no parts.
    pub(crate) text: String,
    pub(crate) parts: Vec<Part>,
}

impl LoadedFile {
    /// The hash of part `i`: of its canonical text (edits.hash).
    pub(crate) fn hash(&self, i: usize) -> String {
        let part = &self.parts[i];
        hash(&canonical(part, &self.text[part.extent.clone()]))
    }

    /// The address of part `i` with its hash.
    pub(crate) fn address(&self, i: usize) -> String {
        format!("{}#{}", self.parts[i].address(), self.hash(i))
    }
}

/// The program at `path`: its files, in the order of their paths.
#[derive(Debug)]
pub(crate) struct Loaded {
    pub(crate) files: Vec<LoadedFile>,
    /// The directory of each package that has a manifest and wasn't fetched, by its index.
    pub(crate) dirs: Vec<Option<PathBuf>>,
}

impl Loaded {
    /// Reads the program at `path` from disk.
    ///
    /// # Errors
    ///
    /// A message for people, when `path` is no program or a file can't be read.
    pub(crate) fn read(path: &Path) -> Result<Self, String> {
        let read = stilt_db::read(path)?;
        let dirs = match &read.graph {
            Some(graph) => (graph.packages.iter())
                .map(|p| (!p.fetched).then(|| p.dir.clone()))
                .collect(),
            None => vec![None],
        };
        let prefixes = read.prefixes;
        let files = read
            .sources
            .into_iter()
            .map(|source| {
                let local = local(prefixes.get(source.package).cloned().flatten(), &source);
                let bytes = read_whole(&source.file)
                    .map_err(|e| format!("cannot read {}: {e}", source.file.display()))?;
                let module = source.module_path.join(".");
                let (text, found) = match String::from_utf8(bytes.clone()) {
                    Ok(text) => {
                        let found = parts(&module, &stilt_syntax::parse(&text), &text);
                        (text, found)
                    }
                    Err(_) => (String::new(), Vec::new()),
                };
                Ok(LoadedFile {
                    path: source.path,
                    disk: source.file,
                    module,
                    package: source.package,
                    local,
                    bytes,
                    text,
                    parts: found,
                })
            })
            .collect::<Result<_, String>>()?;
        Ok(Self { files, dirs })
    }

    /// Every part with the address `address` (a path, with `/body` for a body), as the index
    /// of its file and of the part.
    pub(crate) fn find(&self, address: &str) -> Vec<(usize, usize)> {
        self.files
            .iter()
            .enumerate()
            .flat_map(|(f, file)| {
                file.parts
                    .iter()
                    .enumerate()
                    .filter(|(_, p)| p.address() == address)
                    .map(move |(i, _)| (f, i))
            })
            .collect()
    }
}

/// A module's name in its package, without the first segment that a dependency's modules take
/// in the program (packages.modules-of-dependencies): a dependency's root module is `main` in it.
fn local(prefix: Option<String>, source: &stilt_db::Source) -> String {
    match (prefix, source.module_path.as_slice()) {
        (Some(_), [_]) => "main".to_owned(),
        (Some(_), [_, rest @ ..]) => rest.join("."),
        _ => source.module_path.join("."),
    }
}

/// The bytes of the file at `path`, read under a shared lock, so that a command that writes
/// edits, which holds the file's lock from its check to the end of its write, is never seen
/// midway (edits.concurrent-edits).
fn read_whole(path: &Path) -> io::Result<Vec<u8>> {
    let mut file = File::open(path)?;
    file.lock_shared()?;
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes)?;
    Ok(bytes)
}
