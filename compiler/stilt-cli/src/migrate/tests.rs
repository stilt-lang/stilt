//! `stilt migrate` over packages of 2027, with the compiler given a second edition, 2028, that
//! renames `List.contains` to `List.includes` (editions.renames and editions.migrate).

use std::path::{Path, PathBuf};

use stilt_pkg::edition::{self, EDITIONS, Edition, Rename};

use super::command;

/// The editions of the toolchain, and 2028.
static WITH_2028: [Edition; 2] = [
    EDITIONS[0],
    Edition {
        name: "2028",
        renames: &[Rename {
            owner: "List",
            from: "contains",
            to: "includes",
        }],
    },
];

/// A package in a directory of its own, named for the test, holding `files`.
fn package(test: &str, files: &[(&str, &str)]) -> PathBuf {
    edition::extend(&WITH_2028);
    let dir = std::env::temp_dir().join(format!("stilt-migrate-{test}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    for (path, text) in files {
        let path = dir.join(path);
        std::fs::create_dir_all(path.parent().expect("a directory")).expect("the directory");
        std::fs::write(path, text).expect("the file");
    }
    dir
}

fn read(dir: &Path, path: &str) -> String {
    std::fs::read_to_string(dir.join(path)).expect("the file")
}

const MAIN: &str = "use sets\n\nfn main() / io {\n  let xs = [1, 2]\n  \
                    print(\"{xs.contains(1)} {sets.has([3], 3)}\")\n}\n";
const SETS: &str = "pub fn has(xs: List<i64>, x: i64) -> bool { xs.contains(x) }\n";

#[test]
fn a_package_of_2027_moves_to_2028() {
    let dir = package(
        "moves",
        &[
            (
                "stilt.toml",
                "[package]\nname = \"app\"\nedition = \"2027\"\n",
            ),
            ("src/main.lt", MAIN),
            ("src/sets.lt", SETS),
        ],
    );
    let report = command(&dir);
    assert_eq!(report.status, 0, "{}", report.stderr);
    let expected = "src/main.lt:5: includes, for contains\n\
                    src/sets.lt:1: includes, for contains\n\
                    app: edition 2027 → 2028, 2 files rewritten\n";
    assert_eq!(report.stdout, expected);
    assert_eq!(
        read(&dir, "src/main.lt"),
        MAIN.replace("contains", "includes")
    );
    assert_eq!(
        read(&dir, "src/sets.lt"),
        SETS.replace("contains", "includes")
    );
    let manifest = "[package]\nname = \"app\"\nedition = \"2028\"\n";
    assert_eq!(read(&dir, "stilt.toml"), manifest);
    let again = command(&dir);
    assert_eq!(again.stdout, "app: edition 2028, the newest\n");
}

#[test]
fn a_manifest_without_an_edition_gains_one() {
    let dir = package(
        "gains",
        &[
            ("stilt.toml", "[package]\nname = \"app\"\n"),
            ("src/main.lt", MAIN),
            ("src/sets.lt", SETS),
        ],
    );
    assert_eq!(command(&dir).status, 0);
    let manifest = "[package]\nname = \"app\"\nedition = \"2028\"\n";
    assert_eq!(read(&dir, "stilt.toml"), manifest);
    let bare = package(
        "bare",
        &[("stilt.toml", ""), ("src/main.lt", "fn main() {}\n")],
    );
    assert_eq!(command(&bare).status, 0);
    assert_eq!(
        read(&bare, "stilt.toml"),
        "[package]\nedition = \"2028\"\n\n"
    );
}

#[test]
fn an_old_name_is_e0314_in_2028_and_the_new_one_checks() {
    let manifest = "[package]\nname = \"app\"\nedition = \"2028\"\n";
    let dir = package(
        "e0314",
        &[
            ("stilt.toml", manifest),
            ("src/main.lt", "fn main() { let _ = [1].contains(1) }\n"),
        ],
    );
    let report =
        crate::report::in_process(&dir, |db, program| crate::report::check(db, program, true));
    assert!(report.stdout.contains("\"E0314\""), "{}", report.stdout);
    assert!(
        report
            .stdout
            .contains("the edition 2028 renames `contains` to `includes`"),
        "{}",
        report.stdout
    );
    std::fs::write(
        dir.join("src/main.lt"),
        "fn main() { let _ = [1].includes(1) }\n",
    )
    .expect("the file");
    let report =
        crate::report::in_process(&dir, |db, program| crate::report::check(db, program, false));
    assert_eq!(report.status, 0, "{}", report.stderr);
}

#[test]
fn a_package_with_an_error_or_no_manifest_is_left_as_it_is() {
    let broken = "fn main() { let x: i64 = \"a\" }\n";
    let dir = package(
        "broken",
        &[
            ("stilt.toml", "[package]\nname = \"app\"\n"),
            ("src/main.lt", broken),
        ],
    );
    let report = command(&dir);
    assert_eq!(report.status, 1);
    assert_eq!(read(&dir, "stilt.toml"), "[package]\nname = \"app\"\n");
    let single = package("single", &[("main.lt", "fn main() {}\n")]);
    assert_eq!(command(&single.join("main.lt")).status, 2);
}
