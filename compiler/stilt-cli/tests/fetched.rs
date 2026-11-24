//! Fetched packages (packages.fetching, packages.content-hash and packages.fetch-report): filling
//! in an entry's `version` and `hash`, and the report of what was fetched; entries left as they
//! are; packages that can't be built from their content; and content that doesn't match its hash,
//! in the cache or as a repository serves it.

mod repos;

use std::fs;

use repos::{Place, codes, content_hash, message};

const CSV_TOML: &str = "[package]\nname = \"csv\"\n";
const ROWS: &str = "pub fn rows() -> i64 { 3 }\n";
const ROWS_COLS: &str = "pub fn rows() -> i64 { 3 }\n\npub fn cols() -> i64 { 2 }\n";
const APP: &str = "use csv\n\nfn main() / io { print(\"{csv.rows()} rows\") }\n";

/// The files of `csv` 1.0.0, then those of 1.1.0, which adds an item.
fn csv(place: &Place) -> (repos::Repo, [Vec<(&'static str, &'static str)>; 2]) {
    let repo = place.repo("csv");
    let one = vec![
        ("stilt.toml", CSV_TOML),
        ("src/main.lt", ROWS),
        ("README.md", "csv\n"),
    ];
    let two = vec![
        ("stilt.toml", CSV_TOML),
        ("src/main.lt", ROWS_COLS),
        ("README.md", "csv, with columns\n"),
    ];
    repo.tag("1.0.0", &one);
    repo.tag("1.1.0", &two);
    (repo, [one, two])
}

fn manifest(entry: &str) -> String {
    format!("[package]\nname = \"app\"\n\n[dependencies]\n{entry}\n")
}

#[test]
fn an_entry_with_from_alone_is_filled_in_with_the_highest_version() {
    let place = Place::new("from_alone");
    let (repo, [_, two]) = csv(&place);
    let url = repo.url();
    let entry = format!("csv = {{ from = \"{url}\" }}");
    let app = place.program(&[("stilt.toml", &manifest(&entry)), ("src/main.lt", APP)]);
    let checked = place.check("home", &app);
    assert_eq!(codes(&checked), Vec::<String>::new(), "{checked}");
    let hash = content_hash(&two);
    let filled = format!("csv = {{ from = \"{url}\", version = \"1.1.0\", hash = \"{hash}\" }}");
    let written = fs::read_to_string(app.join("stilt.toml")).expect("the manifest");
    assert_eq!(written, manifest(&filled));
    let fetched = checked["fetched"]
        .as_array()
        .expect("a list of what was fetched");
    let selected =
        serde_json::json!({ "name": "csv", "from": url, "version": "1.1.0", "hash": hash });
    assert!(fetched.contains(&selected), "{checked}");
    let again = place.check("home", &app);
    assert_eq!(again.get("fetched"), None, "the cache holds it: {again}");
    assert_eq!(
        fs::read_to_string(app.join("stilt.toml")).expect("the manifest"),
        written
    );
    let ran = place.stilt("home", &["run"], &app);
    assert_eq!(String::from_utf8_lossy(&ran.stdout), "3 rows\n");
}

/// The repository is packed, so that its objects are read from a pack, and the entry is a table
/// of its own, whose hash goes on a line after its last.
#[test]
fn an_entry_with_a_version_is_filled_in_with_its_hash() {
    let place = Place::new("with_version");
    let (repo, [one, _]) = csv(&place);
    repo.pack();
    let url = repo.url();
    let entry = format!("[dependencies.csv]\nfrom = \"{url}\"\nversion = \"1.0.0\"\n");
    let text = format!("[package]\nname = \"app\"\n\n{entry}");
    let app = place.program(&[("stilt.toml", &text), ("src/main.lt", APP)]);
    let output = place.stilt("home", &["check"], &app);
    assert!(output.status.success(), "{output:?}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    let hash = content_hash(&one);
    assert!(
        stderr.contains(&format!("fetched csv 1.0.0 from {url}, {hash}")),
        "{stderr}"
    );
    let filled = format!("{text}hash = \"{hash}\"\n");
    assert_eq!(
        fs::read_to_string(app.join("stilt.toml")).expect("the manifest"),
        filled
    );
}

#[test]
fn a_pinned_entry_and_a_refused_edit_leave_the_manifest_as_it_is() {
    let place = Place::new("unchanged");
    let (repo, [one, _]) = csv(&place);
    let url = repo.url();
    let hash = content_hash(&one);
    let pinned = manifest(&format!(
        "csv = {{ from = \"{url}\", version = \"1.0.0\", hash = \"{hash}\" }}"
    ));
    let app = place.program(&[("stilt.toml", &pinned), ("src/main.lt", APP)]);
    assert_eq!(codes(&place.check("home", &app)), Vec::<String>::new());
    assert_eq!(
        fs::read_to_string(app.join("stilt.toml")).expect("the manifest"),
        pinned
    );
    let open = manifest(&format!("csv = {{ from = \"{url}\" }}"));
    fs::write(app.join("stilt.toml"), &open).expect("the manifest can be written");
    let refused = place.stilt(
        "home",
        &["check", "--edit", "main.nowhere#0000", "fn f() {}"],
        &app,
    );
    assert_eq!(refused.status.code(), Some(2), "{refused:?}");
    assert_eq!(
        fs::read_to_string(app.join("stilt.toml")).expect("the manifest"),
        open
    );
}

#[test]
fn a_package_that_cant_be_built_from_its_content_is_e0601() {
    let place = Place::new("unbuildable");
    let (csv, _) = csv(&place);
    let manifests = [
        "[package]\nname = \"http\"\n\n[dependencies]\ncsv = { path = \"../csv\" }\n".to_owned(),
        format!(
            "[package]\nname = \"http\"\n\n[dependencies]\ncsv = {{ from = \"{}\", version = \"1.0.0\" }}\n",
            csv.url()
        ),
    ];
    for (i, toml) in manifests.iter().enumerate() {
        let http = place.repo(&format!("http{i}"));
        let files = [
            ("stilt.toml", toml.as_str()),
            ("src/main.lt", "pub fn get() -> i64 { 1 }\n"),
        ];
        http.tag("1.0.0", &files);
        let entry = format!(
            "http = {{ from = \"{}\", version = \"1.0.0\", hash = \"{}\" }}",
            http.url(),
            content_hash(&files)
        );
        let app = place.program(&[
            ("stilt.toml", &manifest(&entry)),
            ("src/main.lt", "fn main() {}\n"),
        ]);
        assert_eq!(codes(&place.check("home", &app)), ["E0601"], "{toml}");
    }
    let bare = place.repo("bare");
    bare.tag("1.0.0", &[("src/main.lt", "pub fn get() -> i64 { 1 }\n")]);
    let entry = format!("bare = {{ from = \"{}\" }}", bare.url());
    let app = place.program(&[
        ("stilt.toml", &manifest(&entry)),
        ("src/main.lt", "fn main() {}\n"),
    ]);
    assert_eq!(codes(&place.check("home", &app)), ["E0601"]);
}

#[test]
fn content_that_doesnt_match_its_hash_is_e0602() {
    let place = Place::new("mismatch");
    let (repo, [one, _]) = csv(&place);
    let url = repo.url();
    let hash = content_hash(&one);
    let pinned = manifest(&format!(
        "csv = {{ from = \"{url}\", version = \"1.0.0\", hash = \"{hash}\" }}"
    ));
    let app = place.program(&[("stilt.toml", &pinned), ("src/main.lt", APP)]);
    assert_eq!(codes(&place.check("home", &app)), Vec::<String>::new());
    let held = place
        .dir
        .join("home/packages")
        .join(hash.trim_start_matches("b3:"));
    fs::write(held.join("src/main.lt"), "pub fn rows() -> i64 { 4 }\n").expect("the cache");
    let changed = place.check("home", &app);
    assert_eq!(
        codes(&changed),
        ["E0602"],
        "a cache entry changed on disk: {changed}"
    );
    repo.tag(
        "1.0.0",
        &[
            ("stilt.toml", CSV_TOML),
            ("src/main.lt", "pub fn rows() -> i64 { 5 }\n"),
        ],
    );
    let retagged = place.check("other", &app);
    assert_eq!(
        codes(&retagged),
        ["E0602"],
        "a retagged version: {retagged}"
    );
    let served = content_hash(&[
        ("stilt.toml", CSV_TOML),
        ("src/main.lt", "pub fn rows() -> i64 { 5 }\n"),
    ]);
    let expected =
        format!("`csv` 1.0.0, as {url} serves it, has the hash {served}, not the one pinned here");
    assert_eq!(message(&retagged, "E0602"), expected);
    assert_eq!(
        fs::read_to_string(app.join("stilt.toml")).expect("the manifest"),
        pinned
    );
}
