//! Release toolchains (builds.release-toolchain and builds.fetching-toolchain): an archive that a
//! version of `stilt` names by its URL and its SHA-256, fetched once over HTTPS, or from a
//! `file://` URL, into the cache that `STILT_HOME` names ([`crate::fetch`]), checked against its
//! hash, and unpacked there. A later build finds it unpacked. An archive is unpacked into a
//! directory of its own and moved into place whole, after its hash was checked, so that an
//! interrupted fetch leaves nothing a build would use.

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

pub mod archive;

/// An archive of a toolchain: where it is published, and the SHA-256 of its bytes, in
/// lowercase hexadecimal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Archive {
    /// The name of its directory in the cache.
    pub name: String,
    /// The URL of the archive.
    pub url: String,
    /// The SHA-256 of its bytes, in lowercase hexadecimal.
    pub sha256: String,
}

/// The SHA-256 of `bytes`, in lowercase hexadecimal.
#[must_use]
pub fn sha256(bytes: &[u8]) -> String {
    let digest = ring::digest::digest(&ring::digest::SHA256, bytes);
    digest.as_ref().iter().fold(String::new(), |mut hex, b| {
        let _ = write!(hex, "{b:02x}");
        hex
    })
}

/// The directory of the toolchain `archive` in the cache at `home`, fetched and unpacked
/// there first if it isn't, with whether this call fetched it.
///
/// # Errors
///
/// Fails, naming the archive, when it can't be fetched, when its bytes' hash isn't the one
/// `archive` gives, which the message names with the hash found, and when it can't be
/// unpacked.
pub fn install(archive: &Archive, home: &Path) -> Result<(PathBuf, bool), String> {
    let dir = home.join("toolchains").join(&archive.name);
    if complete(&dir, archive) {
        return Ok((dir, false));
    }
    let bytes = download(&archive.url).map_err(|e| format!("cannot fetch {}: {e}", archive.url))?;
    let found = sha256(&bytes);
    if found != archive.sha256 {
        return Err(format!(
            "the archive at {} has the SHA-256 {found}, not {}, so nothing is built",
            archive.url, archive.sha256
        ));
    }
    let n = UNPACKS.fetch_add(1, Ordering::Relaxed);
    let fresh =
        home.join("toolchains")
            .join(format!(".{}-{}-{n}", archive.name, std::process::id()));
    let _ = fs::remove_dir_all(&fresh);
    archive::unpack(&bytes, &fresh).map_err(|e| format!("cannot unpack {}: {e}", archive.url))?;
    fs::write(fresh.join(STAMP), &archive.sha256).map_err(|e| e.to_string())?;
    let _ = fs::remove_dir_all(&dir);
    if let Err(e) = fs::rename(&fresh, &dir) {
        let _ = fs::remove_dir_all(&fresh);
        // Another build may have put the same toolchain in place first.
        if !complete(&dir, archive) {
            return Err(format!("cannot write {}: {e}", dir.display()));
        }
    }
    Ok((dir, true))
}

/// How many archives this process has unpacked, which names each one's directory.
static UNPACKS: AtomicUsize = AtomicUsize::new(0);

/// The file of an unpacked toolchain that holds the hash of its archive, written last.
const STAMP: &str = ".sha256";

/// Whether `dir` holds the whole of `archive`, unpacked.
fn complete(dir: &Path, archive: &Archive) -> bool {
    fs::read_to_string(dir.join(STAMP)).is_ok_and(|s| s == archive.sha256)
}

/// The bytes at `url`: an HTTPS URL, or a `file://` one.
///
/// # Errors
///
/// Fails when they can't be read, or when the server answers with anything but 200.
pub fn download(url: &str) -> Result<Vec<u8>, String> {
    if let Some(path) = url.strip_prefix("file://") {
        return fs::read(path).map_err(|e| e.to_string());
    }
    let response = crate::net::get(url)?;
    if response.status == 200 {
        Ok(response.body)
    } else {
        Err(format!("the server answers {}", response.status))
    }
}

#[cfg(test)]
mod tests;
