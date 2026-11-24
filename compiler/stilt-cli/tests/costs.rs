//! The costs suite (builds.performance-report; goal no-hidden-costs). Each program under
//! `tests/costs/` marks what a release build compiles for each function, each call left on a
//! dictionary and each check proved or kept, as the Reference gives them ([its
//! README](../../../tests/costs/README.md)), and `stilt show --release --json` must report exactly
//! those, and drop exactly the lines of the program's profile whose bodies changed. The reference
//! counts it reports are the compiler's own, pinned by reviewed snapshots.

mod common;

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use common::suite;
use serde_json::Value;

/// An entry at a line of a program: `FOR` and its lists of arguments, `ONCE`, `UNREACHED`,
/// `DICTIONARIES` and its lists, `DICTIONARY` and a reason, or `PROVED` or `KEPT` and a kind.
type Entry = (u32, String);

/// The entries that a program's annotations expect.
fn expected(path: &Path) -> Result<BTreeSet<Entry>, String> {
    let text = fs::read_to_string(path).map_err(|e| e.to_string())?;
    let mut out = BTreeSet::new();
    for (n, line) in (1..).zip(text.lines()) {
        let Some((_, annotation)) = line.split_once("//~") else {
            continue;
        };
        let words: Vec<&str> = annotation.split_whitespace().collect();
        let mut i = 0;
        while i < words.len() {
            let entry = match words[i] {
                "ONCE" | "UNREACHED" => words[i].to_owned(),
                "FOR" | "DICTIONARIES" => {
                    let entry = words[i..].join(" ");
                    i = words.len();
                    entry
                }
                word @ ("DICTIONARY" | "PROVED" | "KEPT") => {
                    i += 1;
                    format!("{word} {}", words.get(i).copied().unwrap_or_default())
                }
                other => {
                    return Err(format!(
                        "{}:{n}: an unknown entry `{other}`",
                        path.display()
                    ));
                }
            };
            out.insert((n, entry));
            i += 1;
        }
    }
    Ok(out)
}

/// The records of `show --release --json` on the program's module `main`.
fn records(program: &Path) -> Result<Vec<Value>, String> {
    let dir = program.parent().expect("a program has a directory");
    let output = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(["show", "--release", "--json", "main"])
        .arg(program.file_name().expect("a program has a name"))
        .current_dir(dir)
        .output()
        .expect("stilt runs");
    let stderr = String::from_utf8_lossy(&output.stderr);
    if !output.status.success() || !stderr.is_empty() {
        return Err(format!("`show --release --json main` failed: {stderr}"));
    }
    let lines = String::from_utf8_lossy(&output.stdout).into_owned();
    lines
        .lines()
        .map(|l| serde_json::from_str(l).map_err(|e| e.to_string()))
        .collect()
}

/// A list of arguments as an annotation writes it, as in `A = i64, B = str`.
fn arguments(list: &Value) -> String {
    let pairs = list.as_array().into_iter().flatten().map(|p| {
        let (n, t) = (p["parameter"].as_str(), p["argument"].as_str());
        format!("{} = {}", n.unwrap_or_default(), t.unwrap_or_default())
    });
    pairs.collect::<Vec<_>>().join(", ")
}

/// The entries that the records report.
fn shown(records: &[Value]) -> BTreeSet<Entry> {
    let mut out = BTreeSet::new();
    let line = |v: &Value| u32::try_from(v["line"].as_u64().unwrap_or(0)).unwrap_or(0);
    for r in records {
        let lists: Vec<String> = r["instantiations"]
            .as_array()
            .into_iter()
            .flatten()
            .map(arguments)
            .collect();
        let with = |word: &str| match lists.as_slice() {
            [] => word.to_owned(),
            _ => format!("{word} {}", lists.join(" | ")),
        };
        let compiled = match (r["reached"].as_bool(), r["dictionaries"].as_bool()) {
            (Some(false), _) => "UNREACHED".to_owned(),
            (_, Some(true)) => with("DICTIONARIES"),
            _ if lists.is_empty() => "ONCE".to_owned(),
            _ => with("FOR"),
        };
        out.insert((line(r), compiled));
        for c in r["calls"].as_array().into_iter().flatten() {
            let reason = c["reason"].as_str().unwrap_or_default();
            out.insert((
                line(c),
                format!("DICTIONARY {}", reason.trim_start_matches("polymorphic ")),
            ));
        }
        for (key, word) in [("proved", "PROVED"), ("kept", "KEPT")] {
            for c in r["checks"][key].as_array().into_iter().flatten() {
                out.insert((
                    line(c),
                    format!("{word} {}", c["kind"].as_str().unwrap_or_default()),
                ));
            }
        }
    }
    out
}

/// What is wrong with the lines of the program's profile that the records report dropped:
/// every line whose hash isn't its body's must be dropped at its function.
fn dropped(program: &Path, records: &[Value]) -> Vec<String> {
    let profile = fs::read_to_string(program.with_extension("profile")).unwrap_or_default();
    let mut problems = Vec::new();
    for r in records {
        let body = r["body"].as_str().unwrap_or_default();
        let (address, hash) = body.split_once('#').unwrap_or((body, ""));
        let stale: Vec<&str> = (profile.lines())
            .filter(|l| l.starts_with(&format!("{address} ")) && l.split(' ').nth(1) != Some(hash))
            .collect();
        let listed: Vec<&str> = r["dropped"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .collect();
        if stale != listed {
            problems.push(format!("{address}: drops {listed:?} rather than {stale:?}"));
        }
    }
    problems
}

/// The reference counts of the records, as the snapshot holds them: for each function, its
/// address, then for each line, its operations and its copies.
fn references(records: &[Value]) -> String {
    let mut out = String::new();
    for r in records {
        let at = r["at"].as_str().unwrap_or_default();
        let counts: Vec<String> = (r["references"].as_array().into_iter().flatten())
            .map(|c| {
                let (n, m) = (c["operations"].as_u64(), c["copies"].as_u64());
                let (n, m) = (n.unwrap_or_default(), m.unwrap_or_default());
                let operations = if n == 1 { "operation" } else { "operations" };
                let copies = if m == 1 { "copy" } else { "copies" };
                format!("line {}: {n} {operations}, {m} {copies}", c["line"])
            })
            .collect();
        let address = at.split_once('#').map_or(at, |(a, _)| a);
        let counted = if counts.is_empty() {
            "none".to_owned()
        } else {
            counts.join("; ")
        };
        let _ = writeln!(out, "{address}: {counted}");
    }
    out
}

/// The approved snapshot of a program's reference counts, and its draft.
fn snapshots(program: &Path) -> (PathBuf, PathBuf) {
    let name = program.with_extension("references");
    let file = name.file_name().expect("a snapshot has a name").to_owned();
    (name, suite::root("costs").join("_pending").join(file))
}

fn problems(program: &Path) -> Vec<String> {
    let mut found = Vec::new();
    let records = match records(program) {
        Ok(records) => records,
        Err(e) => return vec![e],
    };
    match expected(program) {
        Ok(expected) => {
            let shown = shown(&records);
            found.extend(
                expected
                    .difference(&shown)
                    .map(|(n, e)| format!("line {n}: no `{e}`")),
            );
            found.extend(
                shown
                    .difference(&expected)
                    .map(|(n, e)| format!("line {n}: `{e}` too")),
            );
        }
        Err(e) => found.push(e),
    }
    found.extend(dropped(program, &records));
    let counts = references(&records);
    let (approved, draft) = snapshots(program);
    let current = match fs::read_to_string(&approved) {
        Ok(snapshot) => snapshot == counts,
        Err(_) => fs::read_to_string(&draft).is_ok_and(|d| d == counts),
    };
    if !current {
        found.push("its reference counts differ from their snapshot, or it has none".to_owned());
    }
    found
}

#[test]
fn the_costs_corpus_reports_what_the_records_give() {
    let failures: Vec<String> = suite::programs(&suite::root("costs"))
        .iter()
        .flat_map(|p| {
            let name = p
                .file_name()
                .unwrap_or_default()
                .to_string_lossy()
                .into_owned();
            problems(p).into_iter().map(move |e| format!("{name}: {e}"))
        })
        .collect();
    assert!(
        failures.is_empty(),
        "\n{}\n\nChanged reference counts need a review: draft them with `cargo test \
         -p stilt-cli --test costs -- --ignored draft`.\n",
        failures.join("\n")
    );
}

/// Drafts into `_pending/` the snapshot of each program whose reference counts have no approved
/// snapshot or differ from it. A draft is reviewed before it is moved up.
#[test]
#[ignore = "it writes the drafts: cargo test -p stilt-cli --test costs -- --ignored --exact draft"]
fn draft() {
    for program in suite::programs(&suite::root("costs")) {
        let counts = references(&records(&program).expect("the program reports"));
        let (approved, draft) = snapshots(&program);
        if fs::read_to_string(&approved).ok().as_deref() != Some(counts.as_str()) {
            let pending = draft.parent().expect("a draft is in `_pending`");
            fs::create_dir_all(pending).expect("`_pending` can be made");
            fs::write(&draft, counts).expect("the draft can be written");
        }
    }
}

#[test]
fn the_report_for_people_gives_each_cost_by_kind_and_line() {
    let dir = suite::root("costs");
    let report = |address: &str, program: &str| {
        let output = Command::new(env!("CARGO_BIN_EXE_stilt"))
            .args(["show", "--release", address, program])
            .current_dir(&dir)
            .output()
            .expect("stilt runs");
        let text = String::from_utf8_lossy(&output.stdout).into_owned();
        // Where references are counted is the compiler's own, which the snapshots pin.
        (text.lines())
            .filter(|l| !l.starts_with("  references:"))
            .collect::<Vec<_>>()
            .join("\n")
    };
    assert_eq!(
        report("main.depth", "instantiations.lt"),
        "fn depth<T>(n: Nested<T>) -> i64\n  compiled once with dictionaries, called at: T = i64\n  \
         dictionaries: line 34, polymorphic recursion\n  checks: 1 kept (overflow, line 34)"
    );
    assert_eq!(
        report("main.largest", "instantiations.lt"),
        "fn largest<T: Ord>(xs: List<T>) -> T\n  compiled for: T = i64, T = str\n  \
         checks: 1 kept (bounds, line 11)"
    );
    assert_eq!(
        report("main.unused", "instantiations.lt"),
        "fn unused<T: Show>(x: T) -> str\n  no instantiation: no root reaches it\n  checks: none"
    );
    assert_eq!(
        report("main.ratio", "checks.lt"),
        "fn ratio(a: i64, b: i64) -> i64\n  compiled once\n  \
         checks: 1 proved and dropped (divide-by-zero, line 13), 1 kept (overflow, line 13)"
    );
    // `n % 2` can't divide by zero, nor overflow, its divisor leaving out -1
    // (facts.proved-overflow).
    assert_eq!(
        report("main.parity", "profiled.lt"),
        "fn parity(n: i64) -> str\n  compiled once\n  \
         checks: 2 proved and dropped (divide-by-zero, line 5; overflow, line 5)\n  \
         profile: 2 lines dropped, as the body changed since\n    \
         main.parity/body 0000 entry 1:26 4\n    main.parity/body 0000 arm 2:6 2"
    );
}
