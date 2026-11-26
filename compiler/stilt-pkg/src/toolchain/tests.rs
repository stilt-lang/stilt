//! The fetch of a toolchain from `file://` archives, and archives read back as written.

use std::fs;
use std::path::{Path, PathBuf};

use super::archive::{pack, unpack};
use super::{Archive, install, sha256};

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stilt-toolchain-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

/// A tree like a toolchain's: an executable, a library beside it and a link to the executable.
fn tree(at: &Path) {
    fs::create_dir_all(at.join("bin")).unwrap();
    fs::create_dir_all(at.join("lib")).unwrap();
    fs::write(at.join("bin/clang-22"), b"#!/bin/sh\necho clang\n").unwrap();
    fs::write(at.join("lib/libLLVM.dylib"), vec![7u8; 3000]).unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        fs::set_permissions(at.join("bin/clang-22"), fs::Permissions::from_mode(0o755)).unwrap();
        std::os::unix::fs::symlink("clang-22", at.join("bin/clang")).unwrap();
    }
}

/// An archive of `tree` written to `dir`, and its entry with its true hash.
fn published(dir: &Path) -> (Archive, PathBuf) {
    let source = dir.join("source");
    tree(&source);
    let bytes = pack(&source).unwrap();
    let file = dir.join("clang.tar.gz");
    fs::write(&file, &bytes).unwrap();
    let archive = Archive {
        name: "clang-test".to_owned(),
        url: format!("file://{}", file.display()),
        sha256: sha256(&bytes),
    };
    (archive, file)
}

#[test]
fn an_archive_unpacks_to_the_tree_it_was_packed_from() {
    let dir = scratch("roundtrip");
    let (_, file) = published(&dir);
    let bytes = fs::read(&file).unwrap();
    assert_eq!(
        bytes,
        pack(&dir.join("source")).unwrap(),
        "packing is deterministic"
    );
    unpack(&bytes, &dir.join("out")).unwrap();
    assert_eq!(
        fs::read(dir.join("out/bin/clang-22")).unwrap(),
        b"#!/bin/sh\necho clang\n"
    );
    assert_eq!(
        fs::read(dir.join("out/lib/libLLVM.dylib")).unwrap(),
        vec![7u8; 3000]
    );
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        let mode = fs::metadata(dir.join("out/bin/clang-22"))
            .unwrap()
            .permissions()
            .mode();
        assert_eq!(mode & 0o777, 0o755);
        assert_eq!(
            fs::read_link(dir.join("out/bin/clang")).unwrap(),
            Path::new("clang-22")
        );
    }
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn a_toolchain_is_fetched_once_and_then_found() {
    let dir = scratch("install");
    let (archive, file) = published(&dir);
    let home = dir.join("home");
    let (at, fetched) = install(&archive, &home).unwrap();
    assert!(fetched);
    assert!(at.join("bin/clang-22").is_file());
    fs::remove_file(&file).unwrap();
    let (again, fetched) = install(&archive, &home).unwrap();
    assert_eq!(
        (again, fetched),
        (at, false),
        "the cache answers without the archive"
    );
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn an_archive_whose_hash_differs_is_refused_by_name() {
    let dir = scratch("corrupt");
    let (archive, file) = published(&dir);
    let mut bytes = fs::read(&file).unwrap();
    let last = bytes.len() - 20;
    bytes[last] ^= 0xff;
    fs::write(&file, &bytes).unwrap();
    let home = dir.join("home");
    let error = install(&archive, &home).unwrap_err();
    assert!(error.contains(&archive.sha256), "{error}");
    assert!(error.contains(&sha256(&bytes)), "{error}");
    assert!(
        !home.join("toolchains/clang-test").exists(),
        "nothing is kept"
    );
    let _ = fs::remove_dir_all(&dir);
}

/// A release build fails with status 2 on any error of its toolchain, as the CLI's tests of
/// `STILT_CC` check; the fetch's own error names the URL and keeps nothing
/// (builds.fetching-toolchain).
#[test]
fn a_fetch_from_a_url_that_doesnt_answer_fails_naming_it() {
    let dir = scratch("unanswered");
    // Nothing listens on port 1 of this machine, so the connection is refused at once.
    let archive = Archive {
        name: "clang-test".to_owned(),
        url: "https://127.0.0.1:1/clang.tar.gz".to_owned(),
        sha256: "00".repeat(32),
    };
    let home = dir.join("home");
    let error = install(&archive, &home).unwrap_err();
    assert!(error.contains(&archive.url), "{error}");
    assert!(
        !home.join("toolchains/clang-test").exists(),
        "nothing is kept"
    );
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn a_toolchain_left_incomplete_in_the_cache_is_fetched_again() {
    let dir = scratch("incomplete");
    let (archive, _) = published(&dir);
    let home = dir.join("home");
    let (at, _) = install(&archive, &home).unwrap();
    fs::remove_file(at.join(".sha256")).unwrap();
    fs::write(at.join("bin/clang-22"), b"broken").unwrap();
    let (again, fetched) = install(&archive, &home).unwrap();
    assert!(fetched);
    assert_eq!(
        fs::read(again.join("bin/clang-22")).unwrap(),
        b"#!/bin/sh\necho clang\n"
    );
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn an_entry_that_would_leave_the_toolchain_is_refused() {
    let dir = scratch("escape");
    fs::create_dir_all(dir.join("source")).unwrap();
    fs::write(dir.join("source/a"), b"x").unwrap();
    let mut bytes = pack(&dir.join("source")).unwrap();
    // The same archive, its one entry renamed `../a`, its header's checksum made again.
    let mut tar = miniz_oxide::inflate::decompress_to_vec(&bytes[10..bytes.len() - 8]).unwrap();
    tar[..4].copy_from_slice(b"../a");
    tar[148..156].fill(b' ');
    let sum: usize = tar[..512].iter().map(|&b| usize::from(b)).sum();
    tar[148..155].copy_from_slice(format!("{sum:06o}\0").as_bytes());
    bytes = [
        &bytes[..10],
        &miniz_oxide::deflate::compress_to_vec(&tar, 6),
        &[0; 8],
    ]
    .concat();
    let error = unpack(&bytes, &dir.join("out")).unwrap_err();
    assert!(error.contains("outside"), "{error}");
    let _ = fs::remove_dir_all(&dir);
}
