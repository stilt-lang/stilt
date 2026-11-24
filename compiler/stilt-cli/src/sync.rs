//! A program's files as a database holds them, kept as they are on disk. Each look takes in the
//! edits made since the last, a file being read again only when its time of change or its size
//! differs; a file added or removed reads the program again, and so does an edit of a manifest, the
//! root's or a path dependency's, which decides the program's packages (packages.manifest,
//! packages.dependencies and packages.path-dependencies; goal one-engine). Each package's
//! `docs.lock` is read again as a file is (docs.lock-file), and so is each file that a macro's use
//! names (macros.named-files). A file whose buffer an editor has open holds the buffer's text in
//! place of the disk's, until the editor closes it (Compiler architecture, "The engine").

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::SystemTime;

use salsa::Setter as _;
use stilt_db::{Database, Program, SourceFile};

/// When a file last changed, and its size.
type Stamp = Option<(SystemTime, u64)>;

/// A file of the program, with its stamp when it was last read.
struct Watched {
    input: SourceFile,
    file: PathBuf,
    /// Its canonical path, by which an editor's buffer names it.
    canonical: PathBuf,
    stamp: Stamp,
}

/// The program at a path, held in a database.
pub(crate) struct Synced {
    path: PathBuf,
    pub(crate) program: Program,
    files: Vec<Watched>,
    /// The manifests read, each with its stamp when the program was read.
    manifests: Vec<(PathBuf, Stamp)>,
    /// The `docs.lock` of each package that has a manifest and wasn't fetched.
    pins: Vec<Watched>,
    /// The texts of the buffers an editor has open, by their files' canonical paths.
    buffers: HashMap<PathBuf, Vec<u8>>,
}

impl Synced {
    /// Reads the program at `path` into `db`.
    pub(crate) fn load(db: &Database, path: &Path) -> Result<Self, String> {
        let program = crate::packages::load(db, path)?;
        let (files, manifests) = watched(db, program, path)?;
        Ok(Self {
            path: path.to_path_buf(),
            pins: pins(db, program, &manifests),
            files,
            manifests,
            program,
            buffers: HashMap::new(),
        })
    }

    /// Holds `text` as the contents of the file whose canonical path is `file`, from the next
    /// look on, or, with `None`, reads the disk's again.
    pub(crate) fn buffer(&mut self, file: &Path, text: Option<String>) {
        if let Some(text) = text {
            self.buffers.insert(file.to_path_buf(), text.into_bytes());
        } else {
            self.buffers.remove(file);
            for w in self.files.iter_mut().filter(|w| w.canonical == file) {
                w.stamp = None;
            }
        }
    }

    /// The text of the buffer held for the file whose canonical path is `file`, if one is.
    pub(crate) fn buffered(&self, file: &Path) -> Option<String> {
        let bytes = self.buffers.get(file)?;
        Some(String::from_utf8_lossy(bytes).into_owned())
    }

    /// Each file of the program with its canonical path.
    pub(crate) fn paths(&self) -> Vec<(SourceFile, PathBuf)> {
        (self.files.iter())
            .map(|w| (w.input, w.canonical.clone()))
            .collect()
    }

    /// Takes in the edits made since the last look, and tells whether there were any.
    pub(crate) fn sync(&mut self, db: &mut Database) -> Result<bool, String> {
        let read = stilt_db::read(&self.path)?;
        let same_files = read.sources.len() == self.files.len()
            && (read.sources.iter())
                .zip(&self.files)
                .all(|(s, w)| s.file == w.file);
        let same_manifests = read.manifests.len() == self.manifests.len()
            && (read.manifests.iter())
                .zip(&self.manifests)
                .all(|(m, (file, at))| m == file && stamp(m) == *at);
        let mut any = false;
        if !same_files || !same_manifests {
            self.program = crate::packages::load(db, &self.path)?;
            (self.files, self.manifests) = watched(db, self.program, &self.path)?;
            self.pins = pins(db, self.program, &self.manifests);
            any = true;
        }
        for w in &mut self.pins {
            let stamp = stamp(&w.file);
            if stamp != w.stamp {
                w.stamp = stamp;
                let bytes = fs::read(&w.file).unwrap_or_default();
                if *w.input.bytes(db) != bytes {
                    w.input.set_bytes(db).to(bytes);
                    any = true;
                }
            }
        }
        for w in &mut self.files {
            if let Some(text) = self.buffers.get(&w.canonical) {
                if w.input.bytes(db) != text {
                    w.input.set_bytes(db).to(text.clone());
                    any = true;
                }
                continue;
            }
            let stamp = stamp(&w.file);
            if stamp == w.stamp {
                continue;
            }
            w.stamp = stamp;
            let bytes =
                fs::read(&w.file).map_err(|e| format!("cannot read {}: {e}", w.file.display()))?;
            if *w.input.bytes(db) != bytes {
                w.input.set_bytes(db).to(bytes);
                any = true;
            }
        }
        any |= stilt_db::refresh_named_files(db);
        Ok(any)
    }
}

/// The program's files, each with where it is and its stamp, and its manifests with theirs.
type Watching = (Vec<Watched>, Vec<(PathBuf, Stamp)>);

fn watched(db: &Database, program: Program, path: &Path) -> Result<Watching, String> {
    let read = stilt_db::read(path)?;
    let files = (program.files(db).iter())
        .zip(read.sources)
        .map(|(&input, source)| Watched {
            input,
            stamp: stamp(&source.file),
            canonical: source
                .file
                .canonicalize()
                .unwrap_or_else(|_| source.file.clone()),
            file: source.file,
        })
        .collect();
    let manifests = (read.manifests.into_iter())
        .map(|file| {
            let at = stamp(&file);
            (file, at)
        })
        .collect();
    Ok((files, manifests))
}

/// The `docs.lock` of each package with a manifest that wasn't fetched, which are those of
/// `manifests`, in their order.
fn pins(db: &Database, program: Program, manifests: &[(PathBuf, Stamp)]) -> Vec<Watched> {
    let packages = program.packages(db).list.iter();
    (packages.filter_map(|p| p.pins).zip(manifests))
        .map(|(input, (manifest, _))| {
            let file = manifest.with_file_name(stilt_db::PINS);
            Watched {
                input,
                stamp: stamp(&file),
                canonical: file.clone(),
                file,
            }
        })
        .collect()
}

fn stamp(file: &Path) -> Stamp {
    let metadata = fs::metadata(file).ok()?;
    Some((metadata.modified().ok()?, metadata.len()))
}
