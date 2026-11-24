use std::time::Duration;

use stilt_meter::Counts;

use super::sample::{Runs, Sample, parse};
use super::toolchains::Language;
use super::{geometric_mean, json};

#[test]
fn the_helpers_line_reads_back() {
    let sample = parse("134 2000000 1500000 9000 7000 8000 6000 4096").expect("a line");
    assert_eq!(sample.status, 134);
    assert_eq!(sample.wall, Duration::from_millis(2));
    assert_eq!(sample.counts.instructions, Some(9000));
    assert_eq!(sample.counts.performance.map(|p| p.cycles), Some(6000));
    assert_eq!(sample.peak, 4096);
    let uncounted = parse("0 10 10 - - - - 1").expect("a line without counts");
    assert_eq!(uncounted.counts.instructions, None);
    assert!(uncounted.counts.performance.is_none());
    assert!(parse("0 10 10").is_none());
}

fn run(nanos: u64) -> Sample {
    Sample {
        counts: Counts {
            instructions: Some(nanos),
            cycles: None,
            performance: None,
            cpu: Duration::from_nanos(nanos),
        },
        wall: Duration::from_secs(1),
        peak: nanos,
        status: 0,
    }
}

#[test]
fn runs_give_their_mean_spread_and_least_peak() {
    let runs = Runs {
        samples: vec![run(900), run(1100)],
    };
    assert_eq!(runs.time(), Duration::from_nanos(1000));
    assert!((runs.spread() - 0.141_421).abs() < 1e-5);
    assert_eq!(runs.instructions(), Some(1000));
    assert_eq!(runs.peak(), 900);
}

#[test]
fn a_geometric_mean_of_ratios() {
    assert_eq!(geometric_mean(&[]), None);
    let mean = geometric_mean(&[2.0, 8.0]).expect("a mean");
    assert!((mean - 4.0).abs() < 1e-12);
}

#[test]
fn languages_are_named_in_any_case() {
    assert_eq!(Language::named("ocaml"), Some(Language::OCaml));
    assert_eq!(Language::named("Go"), Some(Language::Go));
    assert_eq!(Language::named("zig"), None);
}

#[test]
fn json_text_is_escaped() {
    let mut out = String::new();
    json::quote("a \"b\"\\\n\u{1}", &mut out);
    assert_eq!(out, "\"a \\\"b\\\"\\\\\\n\\u0001\"");
}
