//! Fixes as edits of parts (edits.json-form and edits.fixes-as-edits): the `edits` of a fix in
//! `check --json`, which `--edit` takes as they are. The fixes of every snapshot are applied by
//! `tests/snapshots.rs`.

mod common;

use std::path::{Path, PathBuf};

use common::{file, stilt};
use serde_json::Value;

fn repository() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

#[test]
fn a_fix_is_a_list_of_edits_that_one_check_applies() {
    // edits.fixes-as-edits: a fix in a body edits the body; one in a signature, the declaration.
    let dir = repository().join("tests/diagnostics");
    let misspelled = dir.join("E0211_misspelled_name.lt");
    let output = stilt(&["check", "--json", misspelled.to_str().unwrap()], None);
    let json: Value = serde_json::from_slice(&output.stdout).unwrap();
    let d = &json["diagnostics"][0];
    let edit = &d["fixes"][0]["edits"][0];
    assert!(
        edit["at"]
            .as_str()
            .unwrap()
            .starts_with("main.average/body#")
    );
    assert_eq!(edit["at"], d["at"]);
    assert_eq!(edit["new"], "{ sum / count }");
    let private = dir.join("E0214_private_item_in_a_public_signature.lt");
    let output = stilt(&["check", "--json", private.to_str().unwrap()], None);
    let json: Value = serde_json::from_slice(&output.stdout).unwrap();
    let edit = &json["diagnostics"][0]["fixes"][0]["edits"][0];
    assert!(edit["at"].as_str().unwrap().starts_with("main.Config#"));
    assert_eq!(edit["new"], "pub type Config = { port: i64 }");
}

#[test]
fn a_fix_outside_every_part_or_in_a_part_with_two_paths_has_no_edits() {
    // edits.fixes-as-edits: a `use` declaration, and a function defined twice.
    let dir = repository().join("tests/diagnostics");
    let twice = file(
        "edit-apply",
        "two-paths",
        "fn f(count: i64) -> i64 { cuont }\n\nfn f() -> i64 { 1 }\n",
    );
    // The program is accepted, or waits in `_pending/` with its changed snapshot.
    let misspelled = ["", "_pending"]
        .map(|place| dir.join(place).join("E0205_misspelled_module.lt"))
        .into_iter()
        .find(|path| path.exists())
        .expect("the program is in tests/diagnostics");
    for path in [misspelled, twice] {
        let output = stilt(&["check", "--json", path.to_str().unwrap()], None);
        let json: Value = serde_json::from_slice(&output.stdout).unwrap();
        let fixes: Vec<&Value> = json["diagnostics"]
            .as_array()
            .unwrap()
            .iter()
            .flat_map(|d| d["fixes"].as_array().unwrap())
            .collect();
        assert!(!fixes.is_empty(), "{} offers a fix", path.display());
        assert!(
            fixes
                .iter()
                .all(|f| f["edits"].as_array().unwrap().is_empty())
        );
        assert!(
            fixes
                .iter()
                .all(|f| !f["title"].as_str().unwrap().is_empty())
        );
    }
}
