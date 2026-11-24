//! The verdicts of properties in `stilt test --json` (tests.property-verdict), whose fields the
//! conformance runner ignores (conformance.test-objects and conformance.extra-fields): each
//! property's seed and number of cases, and for a failing one its case, counterexample, failure and
//! number of shrinks. The expected values are worked out from tests.property-cases, tests.shrinking
//! and tests.shrink-candidates, and the reference interpreter's `interpreter/test/test_props.ml`
//! expects the same ones.

mod common;

use std::path::Path;
use std::process::Command;

use serde_json::{Value, json};

/// The `property` objects of a program's verdict, without the `detail` of a panic other than
/// `explicit`, whose wording is the implementation's.
fn properties(name: &str, source: &str) -> Vec<Value> {
    let path = common::file("properties", name, source);
    let dir = path.parent().expect("a file is in a directory");
    let output = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .current_dir(dir)
        .args(["test", "--json", "main.lt"])
        .output()
        .expect("stilt runs");
    common::stop_engine(dir, Path::new("main.lt"));
    let verdict: Value = serde_json::from_slice(&output.stdout).unwrap_or(Value::Null);
    verdict["tests"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|t| {
            let mut p = t.get("property")?.clone();
            if p["failure"]
                .as_str()
                .is_some_and(|f| f.starts_with("panic: "))
            {
                p.as_object_mut()?.remove("detail");
            }
            Some(p)
        })
        .collect()
}

#[test]
fn counterexamples_are_shrunk_by_rules_11_and_12() {
    let found = properties(
        "shrunk",
        "/// prop: |xs: List<i64>| xs.len() > 0\n\
         /// prop: |x: i64| x + 1 > x\n\
         /// prop: |x: i64, y: i64| x + y == y + x || x > 1000000\n\
         /// prop: |xs: List<i64>| reverse(reverse(xs)) == xs\n\
         fn reverse(xs: List<i64>) -> List<i64> { xs.fold([], |acc, x| [x].concat(acc)) }\n",
    );
    let expected = [
        json!({"seed": "281aaabf0d00138c", "cases": 1, "case": 0, "counterexample": ["[]"],
               "failure": "false", "shrinks": 0}),
        json!({"seed": "29b4b0c2b0880fe4", "cases": 36, "case": 35,
               "counterexample": ["9223372036854775807"], "failure": "panic: overflow",
               "shrinks": 0}),
        json!({"seed": "b14633fb1d644fa9", "cases": 9, "case": 8,
               "counterexample": ["1", "9223372036854775807"], "failure": "panic: overflow",
               "shrinks": 62}),
        json!({"seed": "e13282d7381055c5", "cases": 100}),
    ];
    assert_eq!(found, expected);
}

#[test]
fn a_counterexample_is_shown_by_its_structure_not_its_show() {
    let found = properties(
        "structure",
        "type Wrap = | Wrap(i64)\n\
         impl Show for Wrap { fn show(self) -> str { assert false\n\"\" } }\n\
         /// prop: |w: Wrap| match w { Wrap(n) => n < 5 }\n\
         fn wrap(n: i64) -> Wrap { Wrap(n) }\n",
    );
    let expected = json!({"seed": "41996ed4b41a2b47", "cases": 2, "case": 1,
                          "counterexample": ["Wrap(5)"], "failure": "false", "shrinks": 62});
    assert_eq!(found, [expected]);
}

#[test]
fn shrinking_stops_after_1000_runs() {
    let found = properties("limit", "/// prop: |x: i64| x < 100000\nfn f() {}\n");
    let expected = json!({"seed": "8c843fe3ef7143dd", "cases": 3, "case": 2,
                          "counterexample": ["169039"], "failure": "false", "shrinks": 348});
    assert_eq!(found, [expected]);
}

#[test]
fn a_raise_reports_what_its_show_shows_and_maps_keep_one_entry_per_key() {
    let found = properties(
        "raise",
        "type Key = { k: str }\n\
         impl Eq for Key { fn eq(self, other: Key) -> bool { self.k.len() == other.k.len() } }\n\
         impl Hash for Key { fn hash(self) -> u64 { self.k.len().wrap_to_u64() } }\n\
         /// prop: |x: i64| { try check(x); true }\n\
         /// prop: |m: Map<Key, u8>| m.len() < 2\n\
         fn check(x: i64) / raise<str> { if x > 10 { raise \"big\" } }\n",
    );
    let expected = [
        json!({"seed": "20c35859f209254b", "cases": 2, "case": 1, "counterexample": ["11"],
               "failure": "raise", "detail": "big", "shrinks": 63}),
        json!({"seed": "1f817f10a197012d", "cases": 4, "case": 3,
               "counterexample": ["{Key { k: \"\u{63812}\" }: 0, Key { k: \"g\" }: 0}"],
               "failure": "false", "shrinks": 1}),
    ];
    assert_eq!(found, expected);
}

#[test]
fn every_run_gives_the_same_verdicts() {
    let source = "/// prop: |s: str, n: u8| s.len() < n.to_i64()\nfn f() {}\n";
    assert_eq!(properties("first", source), properties("second", source));
}
