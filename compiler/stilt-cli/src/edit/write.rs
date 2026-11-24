//! Writing the edits that apply (edits.writing and edits.concurrent-edits): the files they change
//! are locked, found as they were read, and written, so that of two commands that edit one part
//! from one hash, one applies and the other finds the file changed.

use std::fs::{File, OpenOptions};
use std::io::{self, Read as _, Seek as _, SeekFrom, Write as _};

use stilt_edit::{canonical, hash, parts, splice};

use super::load::Loaded;
use super::resolve::Ready;

/// The address with the hash after the write of each edit of `ready`, in its order, or `None`
/// when a file is no longer as it was read, and nothing was written.
///
/// # Errors
///
/// The error of locking, reading or writing a file.
pub(super) fn commit(loaded: &Loaded, ready: &[&Ready]) -> io::Result<Option<Vec<Option<String>>>> {
    let changed: Vec<usize> = (0..loaded.files.len())
        .filter(|&f| ready.iter().any(|r| r.target.file == f))
        .collect();
    // The locks are held until every file is written, in the order of the files.
    let mut held: Vec<(usize, File)> = Vec::new();
    for &f in &changed {
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(&loaded.files[f].disk)?;
        file.lock()?;
        let mut bytes = Vec::new();
        file.read_to_end(&mut bytes)?;
        if bytes != loaded.files[f].bytes {
            return Ok(None);
        }
        held.push((f, file));
    }
    let mut now = vec![None; ready.len()];
    for (f, mut file) in held {
        let loaded_file = &loaded.files[f];
        let edits: Vec<(usize, &str)> = ready
            .iter()
            .filter(|r| r.target.file == f)
            .map(|r| (r.target.part, r.text.as_str()))
            .collect();
        let text = splice(
            &loaded_file.module,
            &loaded_file.text,
            &loaded_file.parts,
            &edits,
        );
        file.set_len(0)?;
        file.seek(SeekFrom::Start(0))?;
        file.write_all(text.as_bytes())?;
        file.flush()?;
        let after = parts(&loaded_file.module, &stilt_syntax::parse(&text), &text);
        for (k, r) in ready.iter().enumerate().filter(|(_, r)| r.target.file == f) {
            let before = &loaded_file.parts[r.target.part];
            now[k] = after
                .get(r.target.part)
                .filter(|p| (p.kind, p.body) == (before.kind, before.body))
                .map(|p| {
                    let digest = hash(&canonical(p, &text[p.extent.clone()]));
                    format!("{}#{digest}", p.address())
                });
        }
    }
    Ok(Some(now))
}
