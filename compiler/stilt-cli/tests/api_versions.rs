//! What of an effect and of a procedural macro is part of a package's API (versions.api): a `pub`
//! effect's operations, each of which a handler implements, and a `pub` procedural macro's
//! signature, while what the macro expands to is its body.

mod repos;

use repos::{Place, codes, message};

/// Checks a program that asks for the newest of versions 1.0.0 and 1.0.1 of `name`, which hold
/// `first` and `second`, and gives the check and the manifest it leaves.
fn newest(place: &Place, name: &str, first: &str, second: &str) -> (serde_json::Value, String) {
    let repo = place.repo(name);
    let toml = format!("[package]\nname = \"{name}\"\n");
    for (version, main) in [("1.0.0", first), ("1.0.1", second)] {
        repo.tag(version, &[("stilt.toml", &toml), ("src/main.lt", main)]);
    }
    let entry = format!("{name} = {{ from = \"{}\" }}", repo.url());
    let app_toml = format!("[package]\nname = \"app\"\n\n[dependencies]\n{entry}\n");
    let app = place.program(&[("stilt.toml", &app_toml), ("src/main.lt", "fn main() {}\n")]);
    let checked = place.check("home", &app);
    let written = std::fs::read_to_string(app.join("stilt.toml")).expect("the manifest");
    (checked, written)
}

/// Asserts that 1.0.1 needs a new major version, and isn't written.
fn needs_major(checked: &serde_json::Value, written: &str) {
    assert_eq!(codes(checked), ["E0604"], "{checked}");
    let needs = message(checked, "E0604");
    assert!(needs.contains("new major version, 2.0.0"), "{needs}");
    assert!(!written.contains("version = \"1.0.1\""), "{written}");
}

const LOG: &str = "pub effect Log {\n  fn log(line: str)\n}\n";
const LOG_FLUSHED: &str = "pub effect Log {\n  fn log(line: str)\n  fn flush()\n}\n";
const LOG_COUNTED: &str = "pub effect Log {\n  fn log(line: str) -> i64\n}\n";

/// An operation added to a `pub` effect breaks the handlers that other packages write, which
/// implement every operation, and one changed breaks their performances: each needs a new
/// major version (handlers.declaring-effect and handlers.handler-types).
#[test]
fn an_operation_added_to_an_effect_or_changed_needs_a_new_major_version() {
    let place = Place::new("effects");
    let (checked, written) = newest(&place, "flushed", LOG, LOG_FLUSHED);
    needs_major(&checked, &written);
    let (checked, written) = newest(&place, "counted", LOG, LOG_COUNTED);
    needs_major(&checked, &written);
}

const TWICE: &str = "use std.meta\n\npub macro twice(e: meta.Expr) -> meta.Expr {\n  \
                     quote { $e + $e }\n}\n";
const TWICE_TIMES: &str = "use std.meta\n\npub macro twice(e: meta.Expr) -> meta.Expr {\n  \
                           quote { $e * 2 }\n}\n";
const TWICE_TWO: &str = "use std.meta\n\npub macro twice(e: meta.Expr, f: meta.Expr) -> \
                         meta.Expr {\n  quote { $e + $f }\n}\n";

/// What a `pub` procedural macro expands to is its body, which a version may change freely,
/// while its signature decides which uses check, and a change to it needs a new major version
/// (macros.procedural-declarations).
#[test]
fn a_procedural_macro_s_signature_is_api_and_its_expansion_isnt() {
    let place = Place::new("macros");
    let (checked, written) = newest(&place, "expands", TWICE, TWICE_TIMES);
    assert_eq!(codes(&checked), Vec::<String>::new(), "{checked}");
    assert!(written.contains("version = \"1.0.1\""), "{written}");
    let (checked, written) = newest(&place, "signed", TWICE, TWICE_TWO);
    needs_major(&checked, &written);
}
