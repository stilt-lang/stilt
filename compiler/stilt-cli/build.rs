//! The version that `stilt --version` prints: the release from the repository's VERSION file,
//! and the commit and the day it was built from, when the sources are a git checkout.

use std::process::Command;

fn main() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let file = root.join("VERSION");
    println!("cargo::rerun-if-changed={}", file.display());
    let release = std::fs::read_to_string(&file).expect("the repository's VERSION file");
    let git = |args: &[&str]| {
        Command::new("git")
            .args(args)
            .current_dir(&root)
            .output()
            .ok()
            .filter(|o| o.status.success())
            .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_owned())
    };
    let built = match (
        git(&["rev-parse", "--short=9", "HEAD"]),
        git(&["log", "-1", "--format=%cs"]),
    ) {
        (Some(commit), Some(day)) => {
            // The commit a build comes from changes with each commit, whose ref git rewrites.
            if let Some(head) = git(&["rev-parse", "--git-path", "HEAD"]) {
                println!("cargo::rerun-if-changed={}", root.join(head).display());
            }
            if let Some(refs) = git(&["rev-parse", "--git-path", "refs/heads"]) {
                println!("cargo::rerun-if-changed={}", root.join(refs).display());
            }
            format!(" ({commit} {day})")
        }
        _ => String::new(),
    };
    println!("cargo::rustc-env=STILT_VERSION={}{built}", release.trim());
}
