//! Loops and large bodies (facts.loop-heads and facts.large-bodies).

use std::fmt::Write as _;

use super::{checks, has, unproved};
use crate::verify::Check;

/// A program of one function `f`, limited by `without panic, div`.
fn total(signature: &str, body: &str) -> String {
    format!("module main\nwithout panic, div\n\nfn f{signature} {{\n{body}\n}}\n")
}

#[test]
fn the_first_iteration_doesnt_reach_the_second() {
    // `i = 0` holds where the loop starts, not on the way back, so `xs[i]` isn't proved.
    let body =
        "  let xs = [7]\n  var s = 0\n  var i = 0\n  while i < n { s += xs[i]\n    i += 1 }\n  s";
    let found = checks(&total("(n: i64) -> i64", body), "f");
    has(&found, "8:22 no bounds");
}

#[test]
fn a_binary_search_is_total() {
    let body = "  var lo = 0\n  var hi = xs.len()\n  while lo < hi {\n    let mid = lo + (hi - lo) / 2\n    \
                if xs[mid] < x { lo = mid + 1 } else { hi = mid }\n  }\n  lo";
    let text = total("(xs: List<i64>, x: i64) -> i64", body);
    let found = checks(&text, "f");
    has(&found, "9:8 bounds");
    assert_eq!(unproved(&text), Vec::<String>::new());
    // The middle of `(lo + hi) / 2`, with `lo` at least 0.
    let body = body.replace("lo + (hi - lo) / 2", "(lo + hi) / 2");
    assert_eq!(
        unproved(&total("(xs: List<i64>, x: i64) -> i64", &body)),
        Vec::<String>::new()
    );
}

#[test]
fn the_head_after_an_inclusive_range_keeps_no_type_bound() {
    // The counter passes 255, so the code after the loop is reached with it at 256.
    let body =
        "  let xs = [1, 2]\n  if hi == 255 {\n    for _ in 0..=hi {}\n    xs[5]\n  } else { 0 }";
    let text = format!("module main\nwithout panic\n\nfn f(hi: u8) -> i64 {{\n{body}\n}}\n");
    let found = checks(&text, "f");
    has(&found, "8:5 no bounds");
}

#[test]
fn a_large_body_keeps_only_bounds() {
    // facts.large-bodies: with the list, `i` and zero, the 61 bindings make 64 and keep `i <
    // xs.len()`; one more makes 65, and the index loses its relation to the length.
    let lets = |n: usize| {
        (0..n).fold(String::new(), |mut text, k| {
            let _ = writeln!(text, "  let a{k} = {k}");
            text
        })
    };
    let body = |n: usize| {
        format!(
            "{}  if i >= 0 && i < xs.len() {{ xs[i] }} else {{ 0 }}",
            lets(n)
        )
    };
    let small = format!(
        "module main\nwithout panic\n\nfn f(xs: List<i64>, i: i64) -> i64 {{\n{}\n}}\n",
        body(61)
    );
    assert_eq!(unproved(&small), Vec::<String>::new());
    let large = format!(
        "module main\nwithout panic\n\nfn f(xs: List<i64>, i: i64) -> i64 {{\n{}\n}}\n",
        body(62)
    );
    let found = unproved(&large);
    assert_eq!(found.len(), 1);
    assert!(found[0].ends_with("no bounds"), "{found:?}");
}

#[test]
fn a_release_build_drops_what_a_rule_proves_beyond_the_analysis() {
    // facts.large-bodies loses `i < xs.len()` in the analysis of a large body, while the guard
    // around the access proves it by a rule of acceptance (facts.rules-of-acceptance), so the
    // release build drops the check all the same.
    let lets = (0..62).fold(String::new(), |mut text, k| {
        let _ = writeln!(text, "  let a{k} = {k}");
        text
    });
    let text = format!(
        "module main\nwithout panic\n\nfn f(xs: List<i64>, i: i64) -> i64 {{\n{lets}  \
         if i >= 0 && i < xs.len() {{ xs[i] }} else {{ 0 }}\n}}\n"
    );
    let db = super::Database::default();
    let (program, file) = super::program(&db, &text);
    let index = super::body_of(&db, program, file, "f");
    let analysed = crate::verify::verified(&db, program, file, index);
    let [(at, Check::Bounds)] = analysed.unproved.as_slice() else {
        panic!("{:?}", analysed.unproved);
    };
    assert!(!analysed.proves(*at, Check::Bounds));
    let released = crate::verify::released(&db, program, file, index);
    assert!(released.proves(*at, Check::Bounds));
    assert_eq!(released.unproved, []);
    // Each proof once: what both prove isn't listed again.
    for p in &released.proved {
        let same = |q: &&crate::verify::Proof| q.at == p.at && q.check == p.check;
        assert_eq!(released.proved.iter().filter(same).count(), 1, "{p:?}");
    }
    for p in &analysed.proved {
        assert!(released.proves(p.at, p.check), "{p:?}");
    }
}

#[test]
fn a_check_met_twice_is_proved_only_when_both_times_are() {
    // A guard of an or-pattern is analysed once for each way (patterns.guards).
    use crate::verify::{Proof, Proofs};
    let at = stilt_syntax::TextRange::new(4.into(), 9.into());
    let other = stilt_syntax::TextRange::new(10.into(), 12.into());
    let proof = |at, check| Proof { at, check };
    let both = Proofs {
        proved: vec![proof(at, Check::Bounds)],
        unproved: vec![(at, Check::Bounds)],
    };
    assert!(!both.proves(at, Check::Bounds));
    let once = Proofs {
        proved: vec![proof(at, Check::Bounds), proof(other, Check::Overflow)],
        unproved: vec![(other, Check::Bounds)],
    };
    assert!(once.proves(at, Check::Bounds));
    assert!(once.proves(other, Check::Overflow));
    assert!(
        !once.proves(at, Check::Overflow),
        "another check at the same place"
    );
    assert!(!once.proves(other, Check::Bounds));
}

#[test]
fn a_check_both_prove_is_listed_once() {
    // The analysis proves `xs[i]` in a range loop over the list's length, and so does the rule
    // of range loops (facts.range-loops): a release build lists the proof once.
    let text = "module main\nwithout panic\n\nfn f(xs: List<i64>) -> i64 {\n  var s = 0\n  \
                for i in 0..xs.len() { s += xs[i] }\n  s\n}\n";
    let db = super::Database::default();
    let (program, file) = super::program(&db, text);
    let index = super::body_of(&db, program, file, "f");
    let analysed = crate::verify::verified(&db, program, file, index);
    let bounds: Vec<_> = analysed
        .proved
        .iter()
        .filter(|p| p.check == Check::Bounds)
        .collect();
    assert_eq!(bounds.len(), 1, "{:?}", analysed.proved);
    let accepted = crate::accept::accepted(&db, program, file, index);
    assert!(
        accepted.checks.iter().any(|(at, c, v)| *at == bounds[0].at
            && *c == Check::Bounds
            && matches!(v, crate::accept::Verdict::Proved(_))),
        "{:?}",
        accepted.checks
    );
    let released = crate::verify::released(&db, program, file, index);
    let listed = released
        .proved
        .iter()
        .filter(|p| p.at == bounds[0].at && p.check == Check::Bounds)
        .count();
    assert_eq!(listed, 1, "{:?}", released.proved);
}
