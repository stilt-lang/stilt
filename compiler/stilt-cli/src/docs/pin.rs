//! Writing pins (docs.writing-pins): once a command has written source, each doc of each package
//! whose files it wrote is pinned, under the lock of the package's `docs.lock`.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::fs::{self, OpenOptions};
use std::io::{self, Read as _, Seek as _, SeekFrom, Write as _};
use std::path::Path;

use stilt_edit::{Doc, Pin, docs, read_lock, write_lock};

use crate::edit::Loaded;

/// A doc as it was before an edit replaced its declaration, in the package `package`: when the
/// declaration that the edit leaves has the same signature and doc, the doc is pinned again.
pub(crate) struct Before {
    package: usize,
    doc: Doc,
}

/// The docs of the declarations that edits replace, as `loaded` holds them before the edits:
/// each target is a file of `loaded` and one of its parts, of which bodies are left out.
pub(crate) fn before(loaded: &Loaded, targets: &[(usize, usize)]) -> Vec<Before> {
    let mut found = Vec::new();
    for &(f, i) in targets {
        let file = &loaded.files[f];
        let part = &file.parts[i];
        if part.body {
            continue;
        }
        let path = format!("{}{}", file.local, &part.path[file.module.len()..]);
        let parse = stilt_syntax::parse(&file.text);
        if let Some(doc) = docs(&file.local, &parse, &file.text)
            .into_iter()
            .find(|d| d.path == path)
        {
            found.push(Before {
                package: file.package,
                doc,
            });
        }
    }
    found
}

/// Pins the docs of the packages `packages` of the program at `path`, as its files are now,
/// each declaration that `confirmed` holds pinned again when it is as it was.
///
/// # Errors
///
/// A message for people, when the program or a `docs.lock` can't be read or written.
pub(crate) fn pin(
    path: &Path,
    packages: &BTreeSet<usize>,
    confirmed: &[Before],
) -> Result<(), String> {
    let loaded = Loaded::read(path)?;
    for &package in packages {
        let Some(dir) = loaded.dirs.get(package).cloned().flatten() else {
            continue;
        };
        let (found, kept) = package_docs(&loaded, package);
        let same: Vec<&Doc> = (confirmed.iter())
            .filter(|c| c.package == package)
            .map(|c| &c.doc)
            .collect();
        let lock = dir.join(stilt_db::PINS);
        update(&lock, &found, &kept, &same)
            .map_err(|e| format!("cannot write {}: {e}", lock.display()))?;
    }
    Ok(())
}

/// The docs of a package's files that can be pinned, and the paths of declarations with a doc
/// and a syntax error, whose pins stay as they are.
fn package_docs(loaded: &Loaded, package: usize) -> (Vec<Doc>, HashSet<String>) {
    let mut found = Vec::new();
    let mut kept = HashSet::new();
    let mut paths: HashMap<String, usize> = HashMap::new();
    for file in loaded.files.iter().filter(|f| f.package == package) {
        let parse = stilt_syntax::parse(&file.text);
        for part in stilt_edit::parts(&file.local, &parse, &file.text) {
            if part.body {
                continue;
            }
            if part.broken && file.text[part.extent.clone()].starts_with("///") {
                kept.insert(part.path.clone());
            }
            *paths.entry(part.path).or_default() += 1;
        }
        found.extend(docs(&file.local, &parse, &file.text));
    }
    found.retain(|d| paths.get(&d.path) == Some(&1));
    (found, kept)
}

/// Writes the pins of `found` into the `docs.lock` at `lock` (docs.writing-pins): a new doc and a
/// changed doc are pinned, a doc of `same` that is as it was is pinned again, every other pin
/// stays, and the pins of no declaration with a doc go, but those of `kept`.
fn update(lock: &Path, found: &[Doc], kept: &HashSet<String>, same: &[&Doc]) -> io::Result<()> {
    if found.is_empty() && !lock.exists() {
        return Ok(());
    }
    let mut file = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(lock)?;
    file.lock()?;
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes)?;
    let text = String::from_utf8_lossy(&bytes).into_owned();
    let old = read_lock(&text);
    let by_path: HashMap<&str, &Pin> = old.iter().map(|p| (p.path.as_str(), p)).collect();
    let mut pins: Vec<Pin> = found
        .iter()
        .map(|doc| match by_path.get(doc.path.as_str()) {
            Some(pin) if pin.doc == doc.doc && !same.iter().any(|s| Pin::of(s) == Pin::of(doc)) => {
                (*pin).clone()
            }
            _ => Pin::of(doc),
        })
        .collect();
    pins.extend(old.iter().filter(|p| kept.contains(&p.path)).cloned());
    if pins.is_empty() {
        drop(file);
        return fs::remove_file(lock);
    }
    let written = write_lock(&pins);
    if written != text {
        file.set_len(0)?;
        file.seek(SeekFrom::Start(0))?;
        file.write_all(written.as_bytes())?;
        file.flush()?;
    }
    Ok(())
}
