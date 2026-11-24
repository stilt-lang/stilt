//! Versions of fetched packages (versions.checked-versions, versions.selection and
//! packages.running-with-ungranted-effect): a version checked against the change in its API before
//! it is written, an API that holds each limitable fact, as it is when verification proves nothing,
//! and no other inferred fact (versions.limitable-facts; versions.facts-in-api;
//! versions.facts-without-proofs); minimal version selection over a graph, its majors and its
//! compatible selections; a cycle through an earlier version; fetched dependencies with errors; and
//! an effect that a fetched manifest doesn't grant. A version that starts to hold an `unsafe` block
//! needs a new major version (c.unsafe-in-api).

mod repos;

use repos::{Place, Repo, codes, content_hash, message};

const JSON_TOML: &str = "[package]\nname = \"json\"\n";
const V1_0: &str = "pub fn parse(s: str) -> i64 { 1 }\n\npub fn version() -> str { \"1.0.0\" }\n";
const V1_1: &str = "pub fn parse(s: str) -> i64 { 1 }\n\npub fn more() -> i64 { 2 }\n\n\
                    pub fn version() -> str { \"1.1.0\" }\n";
const V1_2: &str = "pub fn more() -> i64 { 2 }\n\npub fn version() -> str { \"1.2.0\" }\n";

/// `json` 1.0.0; 1.1.0, which adds `json.more`; and 1.2.0, which removes `json.parse`.
fn json(place: &Place) -> Repo {
    let repo = place.repo("json");
    for (version, main) in [("1.0.0", V1_0), ("1.1.0", V1_1), ("1.2.0", V1_2)] {
        repo.tag(version, &[("stilt.toml", JSON_TOML), ("src/main.lt", main)]);
    }
    repo
}

/// The entry that pins `name`, from `repo`, at `version`, whose files are `files`.
fn pinned(name: &str, repo: &Repo, version: &str, files: &[(&str, &str)]) -> String {
    let hash = content_hash(files);
    format!(
        "{name} = {{ from = \"{}\", version = \"{version}\", hash = \"{hash}\" }}",
        repo.url()
    )
}

fn json_entry(repo: &Repo, version: &str, main: &str) -> String {
    pinned(
        "json",
        repo,
        version,
        &[("stilt.toml", JSON_TOML), ("src/main.lt", main)],
    )
}

/// A package `name` at `version` in a repository of its own, whose dependencies are `entries`
/// and whose module `main` is `main`, and the entry that pins it.
fn package(place: &Place, name: &str, entries: &[String], main: &str) -> String {
    let toml = format!(
        "[package]\nname = \"{name}\"\n\n[dependencies]\n{}\n",
        entries.join("\n")
    );
    let files = [("stilt.toml", toml.as_str()), ("src/main.lt", main)];
    let repo = place.repo(name);
    repo.tag("0.9.0", &files);
    pinned(name, &repo, "0.9.0", &files)
}

fn app(place: &Place, entries: &[String], main: &str) -> std::path::PathBuf {
    let toml = format!(
        "[package]\nname = \"app\"\n\n[dependencies]\n{}\n",
        entries.join("\n")
    );
    place.program(&[("stilt.toml", &toml), ("src/main.lt", main)])
}

#[test]
fn a_version_that_understates_its_change_is_e0604_and_isnt_written() {
    let place = Place::new("understated");
    let repo = json(&place);
    let entry = format!("json = {{ from = \"{}\" }}", repo.url());
    let app = app(&place, &[entry], "fn main() {}\n");
    let before = std::fs::read_to_string(app.join("stilt.toml")).expect("the manifest");
    let checked = place.check("home", &app);
    assert_eq!(codes(&checked), ["E0604"], "{checked}");
    let expected = "the highest version of `json`, 1.2.0, removes `json.parse`, which 1.1.0 has, \
                    so it needs a new major version, 2.0.0; 1.1.0 is the highest version that checks";
    assert_eq!(message(&checked, "E0604"), expected);
    let after = std::fs::read_to_string(app.join("stilt.toml")).expect("the manifest");
    assert_eq!(after, before);
}

#[test]
fn a_change_in_which_parameters_a_function_consumes_needs_no_new_version() {
    let place = Place::new("consumed");
    let repo = place.repo("pick");
    let toml = "[package]\nname = \"pick\"\n";
    let first = "pub fn pick(a: List<i64>, b: List<i64>) -> List<i64> { a }\n";
    let second = "pub fn pick(a: List<i64>, b: List<i64>) -> List<i64> { b }\n";
    repo.tag("1.0.0", &[("stilt.toml", toml), ("src/main.lt", first)]);
    repo.tag("1.0.1", &[("stilt.toml", toml), ("src/main.lt", second)]);
    let entry = format!("pick = {{ from = \"{}\" }}", repo.url());
    let app = app(&place, &[entry], "fn main() {}\n");
    let checked = place.check("home", &app);
    assert_eq!(codes(&checked), Vec::<String>::new(), "{checked}");
    let written = std::fs::read_to_string(app.join("stilt.toml")).expect("the manifest");
    assert!(written.contains("version = \"1.0.1\""), "{written}");
}

/// Version 1.0.0 of `facts`, whose functions version 1.0.1 gives `div` by a `while` loop that
/// verification proves to end, the capability `clock` and `copy`, and nothing else that
/// versions.limitable-facts counts.
const FACTS_1_0_0: &str = "use std.clock\n\npub fn count(n: i64) -> i64 { n + 1 }\n\n\
                           pub fn stamp() -> i64 / io {\n  print(\"stamp\")\n  0\n}\n\n\
                           pub fn both() -> i64 {\n  var xs = [1]\n  let ys = [0]\n  \
                           xs.push(2)\n  xs.len() + ys.len()\n}\n";
const FACTS_1_0_1: &str = "use std.clock\n\npub fn count(n: i64) -> i64 {\n  var i = 0\n  \
                           while i < n { i += 1 }\n  i + 1\n}\n\n\
                           pub fn stamp() -> i64 / io {\n  print(\"stamp\")\n  \
                           clock.unix_ms()\n}\n\n\
                           pub fn both() -> i64 {\n  var xs = [1]\n  let ys = xs\n  \
                           xs.push(2)\n  xs.len() + ys.len()\n}\n";

/// The manifest of a package `name`.
fn named(name: &str) -> String {
    format!("[package]\nname = \"{name}\"\n")
}

/// A repository of `name` whose versions 1.0.0 and 1.0.1 hold `first` and `second`.
fn twice_tagged(place: &Place, name: &str, first: &str, second: &str) -> Repo {
    let repo = place.repo(name);
    for (version, main) in [("1.0.0", first), ("1.0.1", second)] {
        repo.tag(
            version,
            &[("stilt.toml", &named(name)), ("src/main.lt", main)],
        );
    }
    repo
}

/// Checks a program that asks for the newest version of such a repository, granted `io`, and
/// gives the manifest it leaves.
fn newest(place: &Place, name: &str, first: &str, second: &str) -> (serde_json::Value, String) {
    let repo = twice_tagged(place, name, first, second);
    let entry = format!("{name} = {{ from = \"{}\", may = [\"io\"] }}", repo.url());
    let app = app(place, &[entry], "fn main() {}\n");
    let checked = place.check("home", &app);
    let written = std::fs::read_to_string(app.join("stilt.toml")).expect("the manifest");
    (checked, written)
}

/// Pairs of versions of one function, the second of which gains one limitable fact, as
/// `FACTS_1_0_1` gives them all: the fact, the function, and the two versions.
const GAINS: [(&str, &str, &str, &str); 3] = [
    (
        "div",
        "count",
        "pub fn count(n: i64) -> i64 { n + 1 }\n",
        "pub fn count(n: i64) -> i64 {\n  var i = 0\n  while i < n { i += 1 }\n  i + 1\n}\n",
    ),
    (
        "clock",
        "stamp",
        "use std.clock\n\npub fn stamp() -> i64 / io {\n  print(\"stamp\")\n  0\n}\n",
        "use std.clock\n\npub fn stamp() -> i64 / io {\n  print(\"stamp\")\n  clock.unix_ms()\n}\n",
    ),
    (
        "copy",
        "both",
        "pub fn both() -> i64 {\n  var xs = [1]\n  let ys = [0]\n  xs.push(2)\n  xs.len()\n}\n",
        "pub fn both() -> i64 {\n  var xs = [1]\n  let ys = xs\n  xs.push(2)\n  ys.len()\n}\n",
    ),
];

/// A function that gains a fact that a `without` can name, `div`, a capability or `copy`,
/// needs a new major version, even when verification proves the loop that gives it `div` to end,
/// and one that loses it a new minor version (versions.limitable-facts and versions.change-needed;
/// versions.facts-in-api; versions.lost-proofs).
#[test]
fn a_function_that_gains_a_limitable_fact_needs_a_new_major_version() {
    let place = Place::new("facts");
    for (fact, function, before, after) in GAINS {
        let name = format!("gains_{fact}");
        let (checked, written) = newest(&place, &name, before, after);
        assert_eq!(codes(&checked), ["E0604"], "{checked}");
        let expected = format!(
            "the highest version of `{name}`, 1.0.1, gains `{fact}` in `{name}.{function}`, \
             which 1.0.0 has, so it needs a new major version, 2.0.0; 1.0.0 is the highest \
             version that checks"
        );
        assert_eq!(message(&checked, "E0604"), expected);
        assert!(!written.contains("version = \"1.0.1\""), "{written}");
        let name = format!("loses_{fact}");
        let (checked, _) = newest(&place, &name, after, before);
        let needs = message(&checked, "E0604");
        assert!(needs.contains("new minor version, 1.1.0"), "{needs}");
    }
    let pure = "pub fn stamp() -> i64 / io { 0 }\n";
    let timed = "use std.clock\n\npub fn stamp() -> i64 / io { clock.unix_ms() }\n";
    let (checked, _) = newest(&place, "timed", pure, timed);
    assert_eq!(
        codes(&checked),
        ["E0604"],
        "starts performing `io`: {checked}"
    );
}

/// A version whose own code starts to hold an `unsafe` block needs a new major version, and one
/// whose code stops a new minor version (c.unsafe-in-api).
#[test]
fn a_version_that_starts_holding_unsafe_needs_a_new_major_version() {
    let place = Place::new("unsafe_code");
    let plain = "pub fn n() -> i32 { 1 }\n";
    let wrapped = "extern fn abs(n: i32) -> i32\n\npub fn n() -> i32 {\n  \
                   unsafe because \"abs takes any i32 but the least\" { abs(-1) }\n}\n";
    let (checked, _) = newest(&place, "wraps", plain, wrapped);
    assert_eq!(
        message(&checked, "E0604"),
        "the highest version of `wraps`, 1.0.1, makes the package's own code hold an `unsafe` \
         block, which 1.0.0 has, so it needs a new major version, 2.0.0; 1.0.0 is the highest \
         version that checks"
    );
    let (checked, _) = newest(&place, "unwraps", wrapped, plain);
    let needs = message(&checked, "E0604");
    assert!(needs.contains("new minor version, 1.1.0"), "{needs}");
}

/// A selection of 1.0.1 where 1.0.0 is asked for, whose functions gain limitable facts, is
/// E0605 (versions.facts-in-api; versions.compatible-selections).
#[test]
fn a_selection_across_a_gained_fact_is_e0605() {
    let place = Place::new("facts_selected");
    let repo = twice_tagged(&place, "facts", FACTS_1_0_0, FACTS_1_0_1);
    let granted = |version: &str, main: &str| {
        let files = [
            ("stilt.toml", named("facts")),
            ("src/main.lt", main.to_owned()),
        ];
        let files = files.each_ref().map(|(n, t)| (*n, t.as_str()));
        pinned("facts", &repo, version, &files).replace(" }", ", may = [\"io\"] }")
    };
    let user = package(
        &place,
        "user",
        &[granted("1.0.1", FACTS_1_0_1)],
        "use facts\n\npub fn get() -> i64 { facts.count(1) }\n",
    );
    let app = app(
        &place,
        &[granted("1.0.0", FACTS_1_0_0), user],
        "fn main() {}\n",
    );
    let checked = place.check("home", &app);
    assert_eq!(codes(&checked), ["E0605"], "{checked}");
}

/// Version 1.0.0 of `first`, whose index verification proves in range, and 1.0.1, which does
/// the same with its test moved into a function, so that the index isn't proved.
const FIRST_1_0_0: &str = "pub fn first(xs: List<i64>) -> i64 {\n  \
                           if xs.len() > 0 { xs[0] } else { 0 }\n}\n";
const FIRST_1_0_1: &str = "pub fn first(xs: List<i64>) -> i64 {\n  \
                           if filled(xs) { xs[0] } else { 0 }\n}\n\n\
                           fn filled(xs: List<i64>) -> bool {\n  xs.len() > 0\n}\n";

/// A package's API reads `panic` as it is when no check is proved, so a version whose function
/// loses a proof needs no new version, and is selected where the one before it is asked for; a
/// function that gains a check, proved or not, gains `panic`, as under 0.2 (versions.lost-proofs).
#[test]
fn a_version_s_number_follows_no_proof_of_verification() {
    let place = Place::new("proofs");
    let (checked, written) = newest(&place, "first", FIRST_1_0_0, FIRST_1_0_1);
    assert_eq!(codes(&checked), Vec::<String>::new(), "{checked}");
    assert!(written.contains("version = \"1.0.1\""), "{written}");
    let repo = twice_tagged(&place, "picked", FIRST_1_0_0, FIRST_1_0_1);
    let at = |version: &str, main: &str| {
        let files = [
            ("stilt.toml", named("picked")),
            ("src/main.lt", main.to_owned()),
        ];
        let files = files.each_ref().map(|(n, t)| (*n, t.as_str()));
        pinned("picked", &repo, version, &files)
    };
    let user = package(
        &place,
        "user",
        &[at("1.0.1", FIRST_1_0_1)],
        "use picked\n\npub fn get() -> i64 { picked.first([1]) }\n",
    );
    let app = app(&place, &[at("1.0.0", FIRST_1_0_0), user], "fn main() {}\n");
    let checked = place.check("home", &app);
    assert_eq!(codes(&checked), Vec::<String>::new(), "{checked}");
    let none = "pub fn first(xs: List<i64>) -> i64 {\n  0\n}\n";
    let (checked, _) = newest(&place, "gained", none, FIRST_1_0_0);
    assert_eq!(codes(&checked), ["E0604"], "a proved check: {checked}");
}

/// Exporting a function to C changes nothing in its package's API (versions.facts-in-api;
/// c.exported-fact).
#[test]
fn a_function_exported_to_c_needs_no_new_version() {
    let place = Place::new("exported");
    let plain = "pub fn total(n: i64) -> i64 {\n  n + 1\n}\n";
    let exported = "pub extern fn total(n: i64) -> i64 {\n  n + 1\n}\n";
    let (checked, written) = newest(&place, "total", plain, exported);
    assert_eq!(codes(&checked), Vec::<String>::new(), "{checked}");
    assert!(written.contains("version = \"1.0.1\""), "{written}");
}

/// A version that moves to another edition, its API unchanged, needs no new version, since
/// the edition is no part of the API (versions.edition).
#[test]
fn a_version_that_names_its_edition_needs_no_new_version() {
    let place = Place::new("edition");
    let repo = place.repo("dated");
    let main = "pub fn total(n: i64) -> i64 {\n  n + 1\n}\n";
    let first = "[package]\nname = \"dated\"\n";
    let second = "[package]\nname = \"dated\"\nedition = \"2027\"\n";
    repo.tag("1.0.0", &[("stilt.toml", first), ("src/main.lt", main)]);
    repo.tag("1.0.1", &[("stilt.toml", second), ("src/main.lt", main)]);
    let entry = format!("dated = {{ from = \"{}\" }}", repo.url());
    let app = app(&place, &[entry], "fn main() {}\n");
    let checked = place.check("home", &app);
    assert_eq!(codes(&checked), Vec::<String>::new(), "{checked}");
    let written = std::fs::read_to_string(app.join("stilt.toml")).expect("the manifest");
    assert!(written.contains("version = \"1.0.1\""), "{written}");
}

#[test]
fn the_highest_version_asked_for_is_selected_the_same_on_two_machines() {
    let place = Place::new("selection");
    let repo = json(&place);
    let http = package(
        &place,
        "http",
        &[json_entry(&repo, "1.1.0", V1_1)],
        "use json\n\npub fn get() -> i64 { json.more() }\n",
    );
    let main = "use json\n\nfn main() / io { print(json.version()) }\n";
    let app = app(&place, &[json_entry(&repo, "1.0.0", V1_0), http], main);
    assert_eq!(codes(&place.check("one", &app)), Vec::<String>::new());
    for home in ["one", "two"] {
        let ran = place.stilt(home, &["run"], &app);
        assert_eq!(String::from_utf8_lossy(&ran.stdout), "1.1.0\n", "{ran:?}");
    }
}

#[test]
fn versions_that_dont_agree_are_e0605() {
    let place = Place::new("disagree");
    let repo = json(&place);
    repo.tag("2.0.0", &[("stilt.toml", JSON_TOML), ("src/main.lt", V1_2)]);
    let two = package(
        &place,
        "http",
        &[json_entry(&repo, "2.0.0", V1_2)],
        "pub fn get() -> i64 { 1 }\n",
    );
    let app_two = app(
        &place,
        &[json_entry(&repo, "1.0.0", V1_0), two],
        "fn main() {}\n",
    );
    let checked = place.check("home", &app_two);
    assert_eq!(codes(&checked), ["E0605"], "two majors: {checked}");
    let removes = package(
        &place,
        "rpc",
        &[json_entry(&repo, "1.2.0", V1_2)],
        "pub fn get() -> i64 { 1 }\n",
    );
    let app_removes = app(
        &place,
        &[json_entry(&repo, "1.1.0", V1_1), removes],
        "fn main() {}\n",
    );
    let checked = place.check("home", &app_removes);
    assert_eq!(
        codes(&checked),
        ["E0605"],
        "a selection that removes: {checked}"
    );
    let expected = "`rpc` 0.9.0 asks for `json` 1.2.0, which removes `json.parse`, which the 1.1.0 \
                    asked for here has";
    assert_eq!(message(&checked, "E0605"), expected);
}

#[test]
fn a_version_that_depends_on_an_earlier_one_of_its_repository_is_e0609() {
    let place = Place::new("earlier");
    let repo = place.repo("knot");
    let first = [
        ("stilt.toml", "[package]\nname = \"knot\"\n"),
        ("src/main.lt", "pub fn a() -> i64 { 1 }\n"),
    ];
    repo.tag("1.0.0", &first);
    let toml = format!(
        "[package]\nname = \"knot\"\n\n[dependencies]\n{}\n",
        pinned("knot", &repo, "1.0.0", &first)
    );
    let second = [
        ("stilt.toml", toml.as_str()),
        ("src/main.lt", "pub fn a() -> i64 { 1 }\n"),
    ];
    repo.tag("1.1.0", &second);
    let app = app(
        &place,
        &[pinned("knot", &repo, "1.1.0", &second)],
        "fn main() {}\n",
    );
    assert_eq!(codes(&place.check("home", &app)), ["E0609"]);
}

#[test]
fn a_fetched_dependency_with_an_error_gives_one_e0607() {
    let place = Place::new("errors");
    let bad = package(&place, "bad", &[], "pub fn rows() -> i64 { \"three\" }\n");
    let http = package(
        &place,
        "http",
        &[bad],
        "use bad\n\npub fn get() -> i64 { bad.rows() }\n",
    );
    let app = app(
        &place,
        &[http],
        "use http\n\nfn main() / io { print(\"{http.get()}\") }\n",
    );
    let checked = place.check("home", &app);
    assert_eq!(codes(&checked), ["E0607"], "{checked}");
    let found = message(&checked, "E0607");
    assert!(
        found.starts_with("`bad` 0.9.0 has errors, the first an E"),
        "{found}"
    );
    assert!(found.contains(" at bad/src/main.lt:1:"), "{found}");
}

#[test]
fn a_fetched_manifest_that_doesnt_grant_io_gives_e0607_and_a_check_error_panic() {
    let place = Place::new("ungranted");
    let log = package(&place, "log", &[], "pub fn say(s: str) / io { print(s) }\n");
    let worker = package(
        &place,
        "worker",
        &[log],
        "use log\n\npub fn go() / io { log.say(\"hello\") }\n",
    );
    let granted = worker.replace(" }", ", may = [\"io\"] }");
    let main = "use worker\n\nfn main() / io {\n  print(\"start\")\n  worker.go()\n  print(\"never\")\n}\n";
    let app = app(&place, &[granted], main);
    let checked = place.check("home", &app);
    assert_eq!(codes(&checked), ["E0607"], "{checked}");
    let found = message(&checked, "E0607");
    assert_eq!(
        found,
        "`worker` 0.9.0 has errors, the first an E0608 at worker/stilt.toml:5:1"
    );
    let ran = place.stilt("home", &["run"], &app);
    assert_eq!(String::from_utf8_lossy(&ran.stdout), "start\n", "{ran:?}");
    assert!(
        String::from_utf8_lossy(&ran.stderr).contains("panic: check-error"),
        "{ran:?}"
    );
}

/// `json` 1.1.0 adds an inherent member, a minor change, which clashes with the method of a
/// trait that `http` implements for the type (traits.name-clashes).
#[test]
fn a_dependency_that_a_selected_version_breaks_gives_e0607() {
    let place = Place::new("broken_by_addition");
    let repo = place.repo("json");
    let one = "pub type Value = { n: i64 }\n";
    let two =
        "pub type Value = { n: i64 }\n\nimpl Value {\n  pub fn pretty(self) -> str { \"v\" }\n}\n";
    repo.tag("1.0.0", &[("stilt.toml", JSON_TOML), ("src/main.lt", one)]);
    repo.tag("1.1.0", &[("stilt.toml", JSON_TOML), ("src/main.lt", two)]);
    let main = "use json\n\npub trait Pretty {\n  fn pretty(self) -> str\n}\n\n\
                impl Pretty for json.Value {\n  fn pretty(self) -> str { \"p\" }\n}\n";
    let http = package(&place, "http", &[json_entry(&repo, "1.0.0", one)], main);
    let alone = app(&place, std::slice::from_ref(&http), "fn main() {}\n");
    assert_eq!(codes(&place.check("home", &alone)), Vec::<String>::new());
    let app = app(
        &place,
        &[json_entry(&repo, "1.1.0", two), http],
        "fn main() {}\n",
    );
    let checked = place.check("home", &app);
    assert_eq!(codes(&checked), ["E0607"], "{checked}");
    let found = message(&checked, "E0607");
    assert!(
        found.starts_with("`http` 0.9.0 has errors, the first an E0308 at http/src/main.lt:"),
        "{found}"
    );
}
