//! The objects of a release build: each C file compiled by clang across the
//! machine's cores, the largest first, and kept in the cache of objects, `objects/` in the
//! directory that `STILT_HOME` names, under the hash of its C, the clang and the flags, so
//! that a build compiles again only the files whose C changed. An object unused for a week
//! goes, at the first build of a day, so that the cache keeps what is built often and stays
//! bounded. Without a cache, every file is compiled.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, PoisonError};
use std::time::{Duration, SystemTime};

use stilt_codegen_c::Source;

use super::compiler::Compiler;

/// How long an object stays in the cache unused.
const KEPT: Duration = Duration::from_hours(7 * 24);

/// The objects of `sources`, in their order, compiled for `triple`: those in the cache, and
/// the others compiled in `dir` and put in the cache.
pub(crate) fn compile(
    cc: &Compiler,
    sources: &[Source],
    triple: &str,
    cache: Option<&Path>,
    dir: &Path,
) -> Result<Vec<PathBuf>, String> {
    let flags = flags(triple);
    let mut paths = Vec::with_capacity(sources.len());
    let mut missing = Vec::new();
    for (i, s) in sources.iter().enumerate() {
        let key = key(cc, &flags, s);
        let cached = cache.map(|c| c.join(&key[..2]).join(format!("{key}.o")));
        match cached {
            Some(path) if path.exists() => {
                touch(&path);
                paths.push(path);
            }
            _ => {
                missing.push((i, key));
                paths.push(dir.join(format!("{}.o", s.name)));
            }
        }
    }
    missing.sort_by_key(|(i, _)| std::cmp::Reverse(sources[*i].text.len()));
    let compiled = Mutex::new(Vec::with_capacity(missing.len()));
    let next = AtomicUsize::new(0);
    let threads = std::thread::available_parallelism().map_or(1, usize::from);
    std::thread::scope(|scope| {
        for _ in 0..threads.min(missing.len()) {
            scope.spawn(|| {
                while let Some((i, key)) = missing.get(next.fetch_add(1, Ordering::Relaxed)) {
                    let object = (one(cc, &flags, &sources[*i], dir))
                        .map(|object| keep(&object, cache, key));
                    let mut compiled = compiled.lock().unwrap_or_else(PoisonError::into_inner);
                    compiled.push((*i, object));
                }
            });
        }
    });
    let mut compiled = compiled
        .into_inner()
        .unwrap_or_else(PoisonError::into_inner);
    compiled.sort_by_key(|(i, _)| *i);
    for (i, object) in compiled {
        paths[i] = object?;
    }
    if let Some(cache) = cache {
        sweep(cache);
    }
    Ok(paths)
}

/// Every flag of a target's compilation.
fn flags(triple: &str) -> Vec<&str> {
    let mut flags = vec!["-target", triple, "-c"];
    flags.extend_from_slice(stilt_codegen_c::FLAGS);
    flags.extend_from_slice(stilt_codegen_c::target_flags(triple));
    flags
}

/// The key of a file's object: the hash of the clang, the flags, the file's name, which its
/// line tables hold, and its C.
fn key(cc: &Compiler, flags: &[&str], source: &Source) -> String {
    let mut hasher = blake3::Hasher::new();
    for part in [cc.identity.as_str(), &flags.join(" "), &source.name] {
        hasher.update(part.as_bytes());
        hasher.update(&[0]);
    }
    hasher.update(source.text.as_bytes());
    hasher.finalize().to_hex().to_string()
}

/// Compiles one file in `dir`, given by its name alone, so that its line tables name no
/// directory of the machine (builds.same-bytes).
fn one(cc: &Compiler, flags: &[&str], source: &Source, dir: &Path) -> Result<PathBuf, String> {
    let c = dir.join(&source.name);
    std::fs::write(&c, &source.text).map_err(|e| format!("cannot write {}: {e}", c.display()))?;
    let object = format!("{}.o", source.name);
    let output = Command::new(&cc.path)
        .current_dir(dir)
        .args(flags)
        .arg(&source.name)
        .arg("-o")
        .arg(&object)
        .output()
        .map_err(|e| format!("cannot run the C compiler, {}: {e}", cc.path.display()))?;
    if output.status.success() {
        Ok(dir.join(object))
    } else {
        Err(format!(
            "the C compiler, {}, failed on {}:\n{}",
            cc.path.display(),
            source.name,
            String::from_utf8_lossy(&output.stderr).trim_end()
        ))
    }
}

/// Puts a compiled object in the cache, whole or not at all, since builds run at once.
fn keep(object: &Path, cache: Option<&Path>, key: &str) -> PathBuf {
    let Some(cache) = cache else {
        return object.to_path_buf();
    };
    let dir = cache.join(&key[..2]);
    let to = dir.join(format!("{key}.o"));
    let fresh = dir.join(format!(".{key}-{}.o", std::process::id()));
    let kept = std::fs::create_dir_all(&dir)
        .and_then(|()| std::fs::copy(object, &fresh))
        .and_then(|_| std::fs::rename(&fresh, &to));
    if kept.is_err() {
        let _ = std::fs::remove_file(&fresh);
        return object.to_path_buf();
    }
    to
}

/// Marks a cached object used now.
fn touch(path: &Path) {
    if let Ok(file) = std::fs::File::options().write(true).open(path) {
        let _ = file.set_modified(SystemTime::now());
    }
}

/// Removes the cache's objects unused for [`KEPT`], once a day.
fn sweep(cache: &Path) {
    let stamp = cache.join(".swept");
    let day = Duration::from_hours(24);
    let recent = std::fs::metadata(&stamp)
        .and_then(|m| m.modified())
        .is_ok_and(|t| t.elapsed().is_ok_and(|e| e < day));
    if recent || std::fs::write(&stamp, b"").is_err() {
        return;
    }
    let Ok(dirs) = std::fs::read_dir(cache) else {
        return;
    };
    for dir in dirs.flatten().filter(|d| d.path().is_dir()) {
        for object in std::fs::read_dir(dir.path())
            .into_iter()
            .flatten()
            .flatten()
        {
            let old = (object.metadata().and_then(|m| m.modified()))
                .is_ok_and(|t| t.elapsed().is_ok_and(|e| e > KEPT));
            if old {
                let _ = std::fs::remove_file(object.path());
            }
        }
    }
}
