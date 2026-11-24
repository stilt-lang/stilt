//! The tables of `std/text.lt` (std.text), from the Unicode data of Rust's `char`, each run of
//! scalar values one number, so that the tables are short to read, as every program reads them:
//! a property's runs as `first << 22 | (last - first) << 1 | step - 1`, its step 1 or 2; a case
//! mapping's as `first << 42 | (last - first) << 22 | (step - 1) << 21 | add + 2^20`, with what
//! the run's scalar values add to become their mapping; and the scalar values that a mapping
//! makes several, in order, with the three each becomes, `a << 42 | b << 21 | c`, 0 for none,
//! in a table beside them. Each table of runs is in order of first scalar value. The test fails when the file's tables aren't these, as
//! after a toolchain whose Unicode is newer, and
//! `cargo test -p stilt-db --test unicode_tables -- --ignored write` writes them, after which
//! `stilt fmt std/text.lt` lays them out.

use std::fmt::Write as _;
use std::path::PathBuf;

/// The line after which the file holds only its tables.
const MARK: &str = "// The tables, which `compiler/stilt-db/tests/unicode_tables.rs` writes";

fn file() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../std/text.lt")
}

fn scalars() -> impl Iterator<Item = char> {
    (0..=0x10_FFFF_u32).filter_map(char::from_u32)
}

/// Runs of `(first, last, step)` that hold exactly the scalar values that `p` holds of.
fn runs(p: impl Fn(char) -> bool) -> Vec<i64> {
    let mut found: Vec<[i64; 3]> = Vec::new();
    let mut open: Option<[i64; 3]> = None;
    for x in scalars().filter(|&c| p(c)).map(|c| i64::from(u32::from(c))) {
        open = Some(match open {
            Some([first, last, 0]) if x - last <= 2 => [first, x, x - last],
            Some([first, last, step]) if step != 0 && x - last == step => [first, x, step],
            Some(run) => {
                found.push(run);
                [x, x, 0]
            }
            None => [x, x, 0],
        });
    }
    found.extend(open);
    (found.into_iter())
        .map(|[first, last, step]| first << 22 | (last - first) << 1 | (step.max(1) - 1))
        .collect()
}

/// The runs of the scalar values that `map` maps to one other, the scalar values that it maps to
/// several, and the three each of those becomes.
fn case(map: impl Fn(char) -> Vec<char>) -> (Vec<i64>, Vec<i64>, Vec<i64>) {
    let mut found: Vec<[i64; 4]> = Vec::new();
    let mut more = Vec::new();
    let mut becomes = Vec::new();
    for c in scalars() {
        let x = i64::from(u32::from(c));
        let to = map(c);
        match to.as_slice() {
            [one] if *one == c => {}
            [one] => {
                let add = i64::from(u32::from(*one)) - x;
                match found.last_mut() {
                    Some(run @ [_, _, 0, _]) if run[3] == add && x - run[1] <= 2 => {
                        run[2] = x - run[1];
                        run[1] = x;
                    }
                    Some(run) if run[3] == add && run[2] != 0 && x - run[1] == run[2] => {
                        run[1] = x;
                    }
                    _ => found.push([x, x, 0, add]),
                }
            }
            several => {
                assert!(several.len() <= 3, "{c:?} maps to more than three");
                let to = |k: usize| several.get(k).map_or(0, |&s| i64::from(u32::from(s)));
                more.push(x);
                becomes.push(to(0) << 42 | to(1) << 21 | to(2));
            }
        }
    }
    let runs = (found.into_iter())
        .map(|[first, last, step, add]| {
            assert!(
                add.abs() < 1 << 20 && last - first < 1 << 20,
                "a run that doesn't fit"
            );
            first << 42 | (last - first) << 22 | (step.max(1) - 1) << 21 | (add + (1 << 20))
        })
        .collect();
    (runs, more, becomes)
}

/// Each table by its name, in the order the file holds them.
fn tables() -> Vec<(&'static str, Vec<i64>)> {
    let (upper, upper_more, upper_to) = case(|c| c.to_uppercase().collect());
    let (lower, lower_more, lower_to) = case(|c| c.to_lowercase().collect());
    vec![
        ("ALPHABETIC", runs(char::is_alphabetic)),
        ("UPPERCASE", runs(char::is_uppercase)),
        ("LOWERCASE", runs(char::is_lowercase)),
        ("NUMERIC", runs(char::is_numeric)),
        ("WHITESPACE", runs(char::is_whitespace)),
        ("UPPER", upper),
        ("UPPER_MORE", upper_more),
        ("UPPER_TO", upper_to),
        ("LOWER", lower),
        ("LOWER_MORE", lower_more),
        ("LOWER_TO", lower_to),
    ]
}

fn version() -> String {
    let (a, b, c) = char::UNICODE_VERSION;
    format!("{a}.{b}.{c}")
}

/// The tables as the file writes them, each number on a line of its own, which `stilt fmt`
/// then fills.
fn written() -> String {
    let mut out = format!(
        "{MARK} from Unicode {}.\n// Each run is one number, as that file writes them.\n",
        version()
    );
    for (name, numbers) in tables() {
        let _ = writeln!(out, "\nconst {name}: List<i64> = [");
        for n in numbers {
            let _ = writeln!(out, "  {n},");
        }
        out.push_str("]\n");
    }
    out
}

/// The tables the file holds, by their names, read off its text.
fn held(text: &str) -> Vec<(String, Vec<i64>)> {
    let tail = text.split_once(MARK).map_or("", |(_, tail)| tail);
    let mut found = Vec::new();
    for part in tail.split("const ").skip(1) {
        let (name, rest) = part.split_once(':').unwrap_or_default();
        let body = rest.split_once('[').map_or("", |(_, b)| b);
        let body = body.split_once(']').map_or("", |(b, _)| b);
        let numbers = body
            .split(',')
            .map(str::trim)
            .filter(|n| !n.is_empty())
            .map(|n| {
                n.parse()
                    .unwrap_or_else(|_| panic!("{name}: {n} is no number"))
            })
            .collect();
        found.push((name.to_owned(), numbers));
    }
    found
}

#[test]
fn the_file_holds_the_tables_of_this_unicode() {
    let text = std::fs::read_to_string(file()).expect("std/text.lt");
    let want: Vec<(String, Vec<i64>)> = tables()
        .into_iter()
        .map(|(n, t)| (n.to_owned(), t))
        .collect();
    assert!(
        held(&text) == want,
        "std/text.lt's tables aren't those of Unicode {}: run `cargo test -p stilt-db --test unicode_tables -- --ignored write`, then `stilt fmt std/text.lt`",
        version()
    );
    let named = format!("pub fn unicode_version() -> str {{ \"{}\" }}", version());
    assert!(
        text.contains(&named),
        "unicode_version() isn't {}",
        version()
    );
}

#[test]
fn runs_hold_exactly_their_scalar_values() {
    let table = runs(|c| matches!(c, 'a' | 'c' | 'e' | 'f' | 'g' | 'z'));
    let run = |first: i64, last: i64, step: i64| first << 22 | (last - first) << 1 | (step - 1);
    assert_eq!(
        table,
        [run(0x61, 0x65, 2), run(0x66, 0x67, 1), run(0x7a, 0x7a, 1)]
    );
}

#[test]
#[ignore = "writes std/text.lt's tables"]
fn write() {
    let path = file();
    let text = std::fs::read_to_string(&path).expect("std/text.lt");
    let head = text
        .split_once(MARK)
        .map_or(text.as_str(), |(head, _)| head);
    let named = format!("pub fn unicode_version() -> str {{ \"{}\" }}", version());
    let head: Vec<String> = (head.trim_end().lines())
        .map(|l| {
            if l.starts_with("pub fn unicode_version()") {
                named.clone()
            } else {
                l.to_owned()
            }
        })
        .collect();
    let text = format!("{}\n\n{}", head.join("\n"), written());
    std::fs::write(&path, text).expect("std/text.lt written");
}
