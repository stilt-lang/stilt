//! The form of a profile's lines (builds.profile-form): what parses, what is E0610 and why, and
//! how merging adds counts and rounds them down.

use super::lines::{Kind, Line, merge, parse, render, round_down};

fn line(kind: Kind, place: (u32, u32), callee: Option<&str>, count: u64) -> Line {
    Line {
        address: "main.totals/body".to_owned(),
        hash: "3f2a".to_owned(),
        kind,
        place,
        callee: callee.map(str::to_owned),
        count,
    }
}

#[test]
fn a_profile_reads_back_as_it_was_written() {
    let lines = vec![
        line(Kind::Loop, (3, 5), None, 64),
        line(Kind::Entry, (1, 1), None, 2),
        line(Kind::Call, (4, 9), Some("main.key"), 8),
    ];
    let text = render(&lines);
    assert_eq!(
        text,
        "main.totals/body 3f2a entry 1:1 2\n\
         main.totals/body 3f2a loop 3:5 64\n\
         main.totals/body 3f2a call 4:9 main.key 8\n"
    );
    let mut sorted = lines;
    sorted.sort_by_key(|l| l.place);
    assert_eq!(parse(&text), Ok(sorted));
}

#[test]
fn counts_round_down_to_a_power_of_two() {
    assert_eq!(
        [0, 1, 2, 3, 5, 1000, u64::MAX].map(round_down),
        [0, 1, 2, 2, 4, 512, 1 << 63]
    );
}

#[test]
fn merging_adds_the_counts_and_rounds_the_sum_down() {
    let old = vec![
        line(Kind::Arm, (2, 3), None, 4),
        line(Kind::Entry, (1, 1), None, 1),
    ];
    let new = vec![
        line(Kind::Arm, (2, 3), None, 3),
        line(Kind::Arm, (6, 3), None, 1),
        line(Kind::Entry, (1, 1), None, 1),
    ];
    let merged = merge(old, new);
    let counts: Vec<(u32, u64)> = merged.iter().map(|l| (l.place.0, l.count)).collect();
    assert_eq!(counts, [(1, 2), (2, 4), (6, 1)]);
}

#[test]
fn a_line_not_of_the_form_is_named_with_its_reason() {
    let good = "main.f/body 00ff entry 1:1 1\n";
    let cases = [
        ("main.f/body 00ff entry 1:1\n", "fewer than five words"),
        ("main.f 00ff entry 1:1 1\n", "isn't the address of a body"),
        ("main.f/body 00FF entry 1:1 1\n", "isn't a hash"),
        (
            "main.f/body 00ff branch 1:1 1\n",
            "isn't `entry`, `arm`, `loop` or `call`",
        ),
        ("main.f/body 00ff arm 0:1 1\n", "isn't a place"),
        (
            "main.f/body 00ff arm 1:1 3\n",
            "isn't a count, a power of two",
        ),
        (
            "main.f/body 00ff arm 1:1 0\n",
            "isn't a count, a power of two",
        ),
        (
            "main.f/body 00ff arm 1:1 main.g 2\n",
            "only a `call` names a callee",
        ),
        ("main.f/body 00ff call 1:1 2\n", "names its callee"),
        (
            "main.f/body 00ff call 1:1 main.g/body 2\n",
            "isn't the address of a function",
        ),
        ("\n", "fewer than five words"),
    ];
    for (bad, reason) in cases {
        let text = format!("{good}{bad}{good}");
        let m = parse(&text).expect_err(bad);
        assert_eq!(m.number, 2, "{bad}");
        assert_eq!(&text[m.range.clone()], bad.trim_end_matches('\n'), "{bad}");
        assert!(m.reason.contains(reason), "{bad}: {}", m.reason);
    }
}
