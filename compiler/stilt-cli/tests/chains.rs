//! The chain of a type mismatch in `check --json` (goal one-form-per-reader): each step a span and
//! what it gave, in the order of the program, the last at the mismatch itself.

mod common;

use common::{file, finish, stilt};
use serde_json::Value;

/// The steps of the chain of the program's one diagnostic, as `LINE:COL TEXT`.
fn chain(name: &str, source: &str) -> Vec<String> {
    let path = file("chains", name, source);
    let out = stilt(
        &["check", "--json", path.to_str().expect("a UTF-8 path")],
        None,
    );
    finish(&path);
    let json: Value = serde_json::from_slice(&out.stdout).expect("`check --json` prints JSON");
    let [d] = json["diagnostics"]
        .as_array()
        .map(Vec::as_slice)
        .unwrap_or_default()
    else {
        panic!("one diagnostic: {json}");
    };
    (d["chain"].as_array().into_iter().flatten())
        .map(|s| {
            let at = &s["range"][0];
            format!(
                "{}:{} {}",
                at[0],
                at[1],
                s["text"].as_str().unwrap_or_default()
            )
        })
        .collect()
}

#[test]
fn a_local_s_mismatch_names_where_it_was_bound() {
    let source = "fn total(xs: List<i64>) -> i64 {\n  xs.len()\n}\n\nfn main() / io {\n  \
                  let n = total([1, 2])\n  let m: str = n\n  print(m)\n}\n";
    assert_eq!(
        chain("bound", source),
        [
            "6:7 `n` is bound here, with the type `i64`",
            "7:16 here `i64` is found where `str` is expected",
        ]
    );
}

#[test]
fn an_element_s_mismatch_names_what_gave_the_list_its_type() {
    let source = "fn main() / io {\n  var xs = List.new()\n  xs.push(1)\n  xs.push(\"two\")\n  \
                  print(\"{xs}\")\n}\n";
    assert_eq!(
        chain("element", source),
        [
            "3:11 this gives the expected type `{integer}`",
            "4:3 this gives the expected type `{integer}`",
            "4:11 here `str` is found where `{integer}` is expected",
        ]
    );
}
