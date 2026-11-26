//! The clang of a release build (builds.finding-clang and builds.another-compiler), the first of:
//!
//! - the one `STILT_CC` names, which gives up the promise of builds.same-bytes;
//! - the toolchain's own, `clang/bin/clang` in the toolchain beside `stilt`, which `just
//!   toolchain` assembles from the build machine's clang for a build of `stilt` from source;
//! - the archive that this version of `stilt` names for the host, fetched the first time a
//!   release build needs it into the cache, `toolchains/` in the directory that `STILT_HOME`
//!   names, and checked against the SHA-256 below.
//!
//! An archive holds `bin/clang` and what it loads, and nothing else: the C includes no header,
//! and the build links no library of clang's. The manifest of archives, `toolchains.txt`,
//! gains a host's line when its archive is published, which is a step of a release; until then
//! a host without one builds with the toolchain's own clang or `STILT_CC`.

use std::path::{Path, PathBuf};
use std::process::Command;

use stilt_codegen_clif::Target;
use stilt_pkg::toolchain::{Archive, install};

use super::Environment;

/// The release of clang that this version of `stilt` names.
pub(crate) const CLANG: &str = "22.1.8";

/// The archive of the release toolchain of each host that has one, a line of `HOST URL
/// SHA256` each.
const ARCHIVES: &str = include_str!("toolchains.txt");

/// The archive that `manifest` names for `host`.
fn archive(manifest: &str, host: Target) -> Result<Option<Archive>, String> {
    for line in manifest.lines().map(str::trim) {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let fields: Vec<&str> = line.split_whitespace().collect();
        let [name, url, sha256] = fields[..] else {
            return Err(format!(
                "a malformed line of the toolchains' manifest: {line}"
            ));
        };
        if name == host.name() {
            return Ok(Some(Archive {
                name: format!("clang-{CLANG}-{name}"),
                url: url.to_owned(),
                sha256: sha256.to_owned(),
            }));
        }
    }
    Ok(None)
}

/// A clang, and what tells its objects apart from another's in the cache of objects.
#[derive(Debug)]
pub(crate) struct Compiler {
    pub(crate) path: PathBuf,
    pub(crate) identity: String,
}

/// The clang of a release build on `host`, and the line that reports a fetch of it, when
/// this build fetched it.
pub(crate) fn find(
    environment: &Environment,
    toolchain: &Path,
    host: Target,
) -> Result<(Compiler, Option<String>), String> {
    if let Some(cc) = &environment.cc {
        let identity = asked(cc).map_err(|e| {
            format!(
                "STILT_CC names {}, which can't be run as a C compiler: {e}",
                cc.display()
            )
        })?;
        return Ok((
            Compiler {
                path: cc.clone(),
                identity,
            },
            None,
        ));
    }
    let own = toolchain.join("clang/bin/clang");
    if own.exists() {
        let identity =
            identity(&own, "").map_err(|e| format!("cannot read {}: {e}", own.display()))?;
        return Ok((
            Compiler {
                path: own,
                identity,
            },
            None,
        ));
    }
    let Some(archive) = archive(ARCHIVES, host)? else {
        return Err(format!(
            "no release toolchain is published for {} hosts yet: set STILT_CC to a clang",
            host.name()
        ));
    };
    let home = (environment.home.as_deref())
        .ok_or("there is no cache to fetch the release toolchain into: set STILT_HOME or HOME")?;
    let (dir, fetched) = install(&archive, home)?;
    let compiler = Compiler {
        path: dir.join("bin/clang"),
        identity: format!("clang {CLANG}, {}", archive.sha256),
    };
    let report = fetched.then(|| {
        format!(
            "stilt: fetched the release toolchain, clang {CLANG} for {}, into {}\n",
            host.name(),
            dir.display()
        )
    });
    Ok((compiler, report))
}

/// The identity of the clang that `STILT_CC` names, which may be a script that runs another:
/// what it says of its version, as well as its binary's.
fn asked(cc: &Path) -> Result<String, String> {
    let output = Command::new(cc)
        .arg("--version")
        .output()
        .map_err(|e| e.to_string())?;
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).trim().to_owned());
    }
    identity(cc, String::from_utf8_lossy(&output.stdout).trim())
}

/// What tells a clang's objects apart: `version`, the path of its binary, and the binary's size
/// and time of change, so that another clang at the same path keeps none of the objects of the
/// one before it. The toolchain's clang, whose release `just toolchain` checks, is told apart by
/// its binary alone, which a build reads without running clang, a fifth of a small build's
/// time.
fn identity(cc: &Path, version: &str) -> Result<String, String> {
    let real = cc.canonicalize().map_err(|e| e.to_string())?;
    let meta = std::fs::metadata(&real).map_err(|e| e.to_string())?;
    let changed = meta
        .modified()
        .ok()
        .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
        .map_or(0, |d| d.as_nanos());
    Ok(format!(
        "{version}\n{}\n{} {changed}",
        real.display(),
        meta.len()
    ))
}

#[cfg(test)]
mod tests {
    use stilt_codegen_clif::Target;

    use super::{ARCHIVES, archive};

    #[test]
    fn the_manifest_names_each_hosts_archive() {
        let manifest = "# a comment\n\naarch64-macos file:///a.tar.gz 00ff\n";
        let found = archive(manifest, Target::Aarch64Macos).unwrap().unwrap();
        assert_eq!(
            (found.url.as_str(), found.sha256.as_str()),
            ("file:///a.tar.gz", "00ff")
        );
        assert_eq!(found.name, format!("clang-{}-aarch64-macos", super::CLANG));
        assert!(archive(manifest, Target::X86_64Linux).unwrap().is_none());
        assert!(archive("aarch64-macos only-a-url\n", Target::Aarch64Macos).is_err());
        for host in [Target::Aarch64Macos, Target::X86_64Linux] {
            assert!(
                archive(ARCHIVES, host).is_ok(),
                "the built-in manifest reads"
            );
        }
    }
}
