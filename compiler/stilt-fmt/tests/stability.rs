//! The formatter's output across releases (versions.formatting-kept): each output of
//! `tests/format/` is what it was at the tag of the last release, unless `VERSION` names the
//! next release, not yet tagged, and it is of January. Between releases `VERSION` holds the
//! last one's, so a change waits for the commit that names a January release. A checkout without
//! the release's tag, as a shallow clone, checks nothing.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Whether a toolchain's version, `YYYY.M.PATCH`, is of a release of January.
fn january(version: &str) -> bool {
    version.trim().split('.').nth(1) == Some("1")
}

/// Whether the formatter's output may change, with `VERSION` holding `version` and the last
/// release tagged `tag`: when `VERSION` names the next release, and it is of January.
fn may_change(version: &str, tag: &str) -> bool {
    version.trim() != tag && january(version)
}

/// What `git` prints in the repository, if it succeeds.
fn git(args: &[&str]) -> Option<String> {
    let out = Command::new("git")
        .args(args)
        .current_dir(root())
        .output()
        .ok()?;
    out.status
        .success()
        .then(|| String::from_utf8_lossy(&out.stdout).into_owned())
}

/// The tag of the last release before this commit, its version, if the checkout has one.
fn last_release() -> Option<String> {
    let tag = git(&[
        "describe",
        "--tags",
        "--abbrev=0",
        "--match",
        "[0-9]*.[0-9]*.[0-9]*",
    ])?;
    Some(tag.trim().to_owned())
}

/// The outputs that differ from their text at `before`, of those that `before` holds.
fn changed(now: &[(String, String)], before: impl Fn(&str) -> Option<String>) -> Vec<String> {
    now.iter()
        .filter(|(name, text)| before(name).is_some_and(|b| b != *text))
        .map(|(name, _)| name.clone())
        .collect()
}

#[test]
fn outputs_are_kept_but_in_a_january_release() {
    let version = fs::read_to_string(root().join("VERSION")).expect("VERSION");
    let Some(tag) = last_release() else {
        return;
    };
    if may_change(&version, &tag) {
        return;
    }
    let mut now: Vec<(String, String)> = fs::read_dir(root().join("tests/format"))
        .expect("tests/format")
        .map(|entry| entry.expect("an entry").path())
        .filter(|path| path.to_string_lossy().ends_with(".out.lt"))
        .map(|path| {
            let name = path
                .file_name()
                .expect("a name")
                .to_string_lossy()
                .into_owned();
            (name, fs::read_to_string(&path).expect("an output"))
        })
        .collect();
    now.sort();
    let differ = changed(&now, |name| {
        git(&["show", &format!("{tag}:tests/format/{name}")])
    });
    assert!(
        differ.is_empty(),
        "`stilt fmt`'s output changes only in a January release (versions.formatting-kept), \
         and VERSION is {}; these differ from {tag}: {}",
        version.trim(),
        differ.join(", ")
    );
}

#[test]
fn only_the_next_release_in_january_may_change_the_format() {
    assert!(january("2027.1.0") && january("2028.1.2\n"));
    assert!(!january("2027.11.0") && !january("2027.3.1") && !january("2027.10.0"));
    assert!(may_change("2028.1.0\n", "2027.11.0"));
    assert!(!may_change("2028.1.0\n", "2028.1.0"));
    assert!(!may_change("2027.3.0", "2027.1.0"));
}

#[test]
fn an_output_changes_where_its_text_at_the_tag_differs() {
    let now = [
        ("a.out.lt".to_owned(), "x\n".to_owned()),
        ("b.out.lt".to_owned(), "y\n".to_owned()),
        ("new.out.lt".to_owned(), "z\n".to_owned()),
    ];
    let before = |name: &str| match name {
        "a.out.lt" => Some("x\n".to_owned()),
        "b.out.lt" => Some("y  \n".to_owned()),
        _ => None,
    };
    assert_eq!(changed(&now, before), ["b.out.lt"]);
}
