//! Which entries below a module root are modules (program.module-names), on trees with links,
//! hidden entries and named pipes made as the tests run.

use std::fs;
use std::path::{Path, PathBuf};

use super::module_files;

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stilt-files-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn write(at: &Path, path: &str) {
    let file = at.join(path);
    fs::create_dir_all(file.parent().unwrap()).unwrap();
    fs::write(file, b"pub fn f() -> i64 { 1 }\n").unwrap();
}

#[cfg(unix)]
fn link(target: &str, at: &Path, path: &str) {
    std::os::unix::fs::symlink(target, at.join(path)).unwrap();
}

#[test]
fn hidden_entries_are_skipped() {
    let root = scratch("hidden");
    write(&root, "main.lt");
    write(&root, ".notes.lt");
    write(&root, ".cache/x.lt");
    write(&root, "a/.b.lt");
    write(&root, "a/c.lt");
    fs::write(root.join("readme.md"), b"").unwrap();
    assert_eq!(module_files(&root).unwrap(), ["a/c.lt", "main.lt"]);
    let _ = fs::remove_dir_all(&root);
}

#[cfg(unix)]
#[test]
fn links_are_followed_at_their_paths() {
    let root = scratch("links");
    write(&root, "main.lt");
    write(&root, ".shared/util.lt");
    link(".shared", &root, "lib");
    link(".shared/util.lt", &root, "tool.lt");
    link("missing.lt", &root, "dangling.lt");
    assert_eq!(
        module_files(&root).unwrap(),
        ["lib/util.lt", "main.lt", "tool.lt"]
    );
    let _ = fs::remove_dir_all(&root);
}

#[cfg(unix)]
#[test]
fn links_that_make_cycles_are_skipped() {
    let root = scratch("cycles");
    write(&root, "main.lt");
    write(&root, "a/one.lt");
    write(&root, "b/two.lt");
    link("..", &root, "a/up");
    link("../..", &root, "far");
    link("../b", &root, "a/x");
    link("../a", &root, "b/y");
    link("itself", &root, "itself");
    assert_eq!(
        module_files(&root).unwrap(),
        [
            "a/one.lt",
            "a/x/two.lt",
            "b/two.lt",
            "b/y/one.lt",
            "main.lt"
        ]
    );
    let _ = fs::remove_dir_all(&root);
}

#[cfg(unix)]
#[test]
fn only_regular_files_are_modules() {
    let root = scratch("pipes");
    write(&root, "main.lt");
    let made = std::process::Command::new("mkfifo")
        .arg(root.join("pipe.lt"))
        .status();
    if !made.is_ok_and(|status| status.success()) {
        let _ = fs::remove_dir_all(&root);
        return;
    }
    link("pipe.lt", &root, "piped.lt");
    fs::create_dir(root.join("folder.lt")).unwrap();
    assert_eq!(module_files(&root).unwrap(), ["main.lt"]);
    let _ = fs::remove_dir_all(&root);
}
