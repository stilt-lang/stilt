//! Cycles through `Shared<T>` (cycles.through-shared-values): a program
//! that makes cycles and lets them go runs out of memory only when what it still reaches doesn't
//! fit in the heap (cycles.freeing), under `stilt run` and as an executable that `stilt build`
//! writes, and `stilt show` writes which types can form one (cycles.can-form-cycle). The
//! conformance suite's tests of `cycles/` cover the rest, under both implementations; the loop here
//! makes too many cycles for the reference interpreter to run in a test's time, and the facts
//! suite checks the fact on each kind of type (`CYCLE`).

use std::path::Path;
use std::process::{Command, Output};

use serde_json::Value;

mod common;

/// The heap the loop runs in, which `STILT_HEAP` sets (program.exit-statuses).
const HEAP: &str = "512M";

/// Each cycle holds a list of 100,000 integers, 800 KB, so that the 2,000 it makes would need
/// 1.6 GB, more than a heap of [`HEAP`], if none was freed before the end.
const CYCLES: &str = "use std.sync

type Node = { items: List<i64>, next: Option<sync.Shared<Node>> }

fn main() / io {
  var total = 0
  for i in 0..2000 {
    let a = sync.Shared.new(Node { items: List.repeat(i, 100000), next: None })
    let b = sync.Shared.new(Node { items: [], next: Some(a) })
    when a { a.next = Some(b) }
    total += when a { a.items.len() }
  }
  print(\"{total}\")
}
";

fn stilt(args: &[&str], path: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(args)
        .arg(path)
        .env("STILT_HEAP", HEAP)
        .output()
        .expect("stilt runs")
}

/// Checks that a run printed the total of the lists' lengths and ended with every count at zero.
fn total(output: &Output, what: &str) {
    assert_eq!(
        (output.status.code(), common::stdout(output).as_str()),
        (Some(0), "200000000\n"),
        "{what}: {}",
        common::stderr(output)
    );
}

#[test]
fn a_loop_that_lets_go_of_cycles_runs_within_the_heap() {
    let path = common::file("cycles", "heap", CYCLES);
    total(&stilt(&["run"], &path), "stilt run");
    let exe = path.with_file_name("program");
    let built = stilt(&["build", "-o", &exe.to_string_lossy()], &path);
    assert!(built.status.success(), "{built:?}");
    let ran = Command::new(&exe)
        .env("STILT_HEAP", HEAP)
        .output()
        .expect("the program runs");
    total(&ran, "the executable");
}

/// The same loop, keeping every cycle it makes, outgrows the heap and ends the program with 134
/// (program.exit-statuses), so a heap of [`HEAP`] is what the loop above runs within.
#[test]
fn the_loop_that_keeps_its_cycles_outgrows_the_heap() {
    let kept = CYCLES
        .replace("var total = 0", "var total = 0\n  var all = []")
        .replace(
            "when a { a.next = Some(b) }",
            "when a { a.next = Some(b) }\n    all.push(a)",
        );
    let path = common::file("cycles", "outgrown", &kept);
    let ran = stilt(&["run"], &path);
    assert_eq!(ran.status.code(), Some(134), "{}", common::stderr(&ran));
    assert!(
        common::stderr(&ran).starts_with("fatal: out of memory"),
        "{}",
        common::stderr(&ran)
    );
}

const TYPES: &str = "use std.sync

type Node = { name: str, next: Option<sync.Shared<Node>>, prev: Option<sync.Shared<Node>> }

type Account = { balance: i64 }

fn main() {}
";

#[test]
fn show_writes_which_types_can_form_a_cycle() {
    let path = common::file("cycles", "show", TYPES);
    let dir = path.parent().expect("a directory");
    let output = stilt(&["show", "main.Node"], &path);
    let text = common::stdout(&output);
    let line = text.lines().find(|l| l.starts_with("type Node"));
    assert_eq!(
        line,
        Some(
            "type Node = { name: str, next: Option<sync.Shared<Node>>, prev: Option<sync.Shared<Node>> }  // can form a cycle, through `next` and `prev`"
        ),
        "{text}"
    );
    let output = stilt(&["show", "--json", "main.Node"], &path);
    let record: Value = serde_json::from_slice(&output.stdout).expect("one JSON record");
    assert_eq!(record["cycle"], serde_json::json!(["next", "prev"]));
    let output = stilt(&["show", "--json", "main.Account"], &path);
    let record: Value = serde_json::from_slice(&output.stdout).expect("one JSON record");
    assert!(record.get("cycle").is_none(), "{record}");
    common::stop_engine(dir, &path);
}
