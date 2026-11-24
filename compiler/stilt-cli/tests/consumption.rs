//! The parameters each function consumes, which the compiler infers (values.consumed-parameters): a
//! function owns a parameter that its body returns, stores, rebinds with `var` or passes to a
//! consumed parameter, its direct callers give it their argument, and calls through function values
//! and dictionaries borrow, through adapters that give the function what it consumes. Each program
//! prints what value semantics says, and ends with every count at zero (goal no-leaks), both
//! under `stilt run` and as an executable.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

/// Runs `source` under `stilt run` with its MIR written out, then as a built executable, checks
/// that both print `expected` and succeed, and returns the MIR.
fn runs_as(name: &str, source: &str, expected: &str) -> String {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("consumption")
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("the directory can be made");
    let file = dir.join("main.lt");
    fs::write(&file, source).expect("the program can be written");
    let stilt = env!("CARGO_BIN_EXE_stilt");
    let run = Command::new(stilt)
        .arg("run")
        .arg(&file)
        .env("STILT_DUMP_MIR", "1")
        .output()
        .expect("stilt runs");
    let mir = String::from_utf8_lossy(&run.stderr).into_owned();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected, "{mir}");
    assert!(run.status.success(), "stilt run: {mir}");
    let exe = dir.join("program");
    let built = Command::new(stilt)
        .args(["build", "-o"])
        .arg(&exe)
        .arg(&file)
        .output()
        .expect("stilt runs");
    assert!(built.status.success(), "{built:?}");
    let ran = Command::new(&exe).output().expect("the program runs");
    assert_eq!(String::from_utf8_lossy(&ran.stdout), expected);
    assert!(ran.status.success(), "the executable: {ran:?}");
    mir
}

/// The line of the MIR that starts the function `name`, with its parameters.
fn header<'m>(mir: &'m str, name: &str) -> &'m str {
    let start = format!("fn {name}(");
    mir.lines()
        .find(|l| l.starts_with(&start))
        .unwrap_or_else(|| panic!("no function {name} in\n{mir}"))
}

/// The lines of the MIR of the function `name`.
fn body<'m>(mir: &'m str, name: &str) -> Vec<&'m str> {
    let start = header(mir, name);
    mir.lines()
        .skip_while(|l| *l != start)
        .take_while(|l| *l != "}")
        .collect()
}

const GROWN: &str = "fn grown(xs: List<i64>) -> List<i64> {\n  var ys = xs\n  ys.push(9)\n  ys\n}\n\nfn size(xs: List<i64>) -> i64 {\n  var n = 0\n  for x in xs { n += 1 }\n  n\n}\n\n";

#[test]
fn a_consumed_parameter_is_given_and_a_read_one_is_lent() {
    let main = "fn main() / io {\n  var a = [1, 2]\n  a = grown(a)\n  let b = grown(a)\n  print(\"{a} {b} {size(a)}\")\n}\n";
    let mir = runs_as(
        "given",
        &format!("{GROWN}{main}"),
        "[1, 2, 9] [1, 2, 9, 9] 3\n",
    );
    assert!(
        header(&mir, "main.grown").contains("_1: Owned Heap"),
        "{mir}"
    );
    assert!(
        header(&mir, "main.size").contains("_1: Borrowed Heap"),
        "{mir}"
    );
    let calls = body(&mir, "main.main");
    assert_eq!(
        calls
            .iter()
            .filter(|l| l.contains("call main.grown(") && l.contains(", own _"))
            .count(),
        2,
        "{mir}"
    );
}

#[test]
fn consumption_flows_through_recursion_and_calls() {
    let source = "fn even(xs: List<i64>, n: i64) -> List<i64> {\n  if n == 0 { xs } else { odd(xs, n - 1) }\n}\n\nfn odd(xs: List<i64>, n: i64) -> List<i64> {\n  if n == 0 { [] } else { even(xs, n - 1) }\n}\n\nfn relay(xs: List<i64>) -> List<i64> { even(xs, 2) }\n\nfn main() / io {\n  let xs = [4]\n  print(\"{relay(xs)} {odd(xs, 2)} {xs}\")\n}\n";
    let mir = runs_as("recursion", source, "[4] [] [4]\n");
    for name in ["main.even", "main.odd", "main.relay"] {
        assert!(
            header(&mir, name).contains("_1: Owned Heap"),
            "{name}\n{mir}"
        );
    }
}

#[test]
fn calls_through_values_borrow_and_adapters_give() {
    let source = format!(
        "{GROWN}trait Grow {{\n  fn grow(self) -> Self\n}}\n\ntype Bag = {{ items: List<i64> }}\n\nimpl Grow for Bag {{\n  fn grow(self) -> Bag {{\n    var b = self\n    b.items.push(0)\n    b\n  }}\n}}\n\nfn twice<T: Grow>(x: T) -> T {{ x.grow().grow() }}\n\nfn main() / io {{\n  let f = grown\n  let a = [1]\n  let b = Bag {{ items: [2] }}\n  print(\"{{f(a)}} {{a}} {{twice(b)}} {{b}} {{[a, a].map(grown)}}\")\n}}\n"
    );
    let mir = runs_as(
        "values",
        &source,
        "[1, 9] [1] Bag { items: [2, 0, 0] } Bag { items: [2] } [[1, 9], [1, 9]]\n",
    );
    // The code of `grown` as a value borrows, and gives `grown` its argument.
    assert!(
        header(&mir, "main.grown#value").contains("_2: Borrowed Heap"),
        "{mir}"
    );
    let value = body(&mir, "main.grown#value");
    assert!(
        value
            .iter()
            .any(|l| l.contains("call main.grown(") && l.contains("own _")),
        "{mir}"
    );
    // So does the entry of `grow` in `Bag`'s dictionary, which `twice` calls through.
    let entry = header(&mir, "<main.Bag as main.Grow>#entry0");
    assert!(!entry.contains("Owned"), "{mir}");
    assert!(
        header(&mir, "<main.Bag as main.Grow>.grow").contains("Owned Heap"),
        "{mir}"
    );
}

/// `start` consumes its table. `handed` assigns `table` after its last use, so the call takes
/// the table's reference and the write changes it in place; `kept` gives `table` back to its
/// caller as it was, and `risky` raises before it assigns it, so both copy it, and the caller's
/// table is the one they were given (values.consumed-parameters and values.inout-arguments).
const TABLES: &str = "type Table = { slots: List<i64> }\n\ntype State = { table: Table, n: i64 }\n\nfn start(table: Table) -> State { State { table, n: 0 } }\n\nfn handed(inout table: Table) {\n  var s = start(table)\n  s.table.slots[0] += 1\n  table = s.table\n}\n\nfn kept(inout table: Table) -> i64 {\n  var s = start(table)\n  s.table.slots[0] += 10\n  s.table.slots[0]\n}\n\nfn risky(inout table: Table, n: i64) / raise<str> {\n  var s = start(table)\n  s.table.slots[0] += 100\n  if n < 0 { raise \"no\" }\n  table = s.table\n}\n\n";

#[test]
fn an_inout_parameter_assigned_after_its_last_use_hands_its_value_over() {
    let main = "fn main() / io {\n  var table = Table { slots: [1, 0] }\n  handed(inout table)\n  let k = kept(inout table)\n  try risky(inout table, -1) catch _ because \"the table shows it\" => ()\n  print(\"{table.slots} {k}\")\n  try risky(inout table, 1) catch _ because \"it doesn't raise\" => ()\n  print(\"{table.slots}\")\n}\n";
    let mir = runs_as("inout", &format!("{TABLES}{main}"), "[2, 0] 12\n[102, 0]\n");
    let dups = |name: &str| {
        body(&mir, name)
            .iter()
            .filter(|l| l.contains("dup "))
            .count()
    };
    assert_eq!(dups("main.handed"), 0, "{mir}");
    assert_eq!(dups("main.kept"), 1, "{mir}");
    assert_eq!(dups("main.risky"), 1, "{mir}");
}

/// facts.in-place-promise: a call that passes an argument to an in-place parameter makes its
/// storage unique there, in the caller, so the callee's writes copy nothing. `main` keeps `a` after
/// passing it to `bump_all`, and `c` shares `a`'s storage when `zero_first` gets it, so both calls
/// copy their argument at the call, and value semantics still hold. A callee that isn't limited by
/// `without alloc` has no in-place parameter, and its caller makes nothing unique.
#[test]
fn an_in_place_parameter_gets_storage_made_unique_at_the_call() {
    let source = "fn bump_all(xs: List<i64>) -> List<i64> without alloc {\n  var ys = xs\n  for i in 0..ys.len() { ys[i] += 1 }\n  ys\n}\n\nfn zero_first(inout xs: List<i64>) without alloc { xs[0] = 0 }\n\nfn zero_last(inout xs: List<i64>) { xs[xs.len() - 1] = 0 }\n\nfn main() / io {\n  let a = [1, 2]\n  let b = bump_all(a)\n  var c = a\n  zero_first(inout c)\n  zero_last(inout c)\n  print(\"{a} {b} {c}\")\n}\n";
    let mir = runs_as("in_place", source, "[1, 2] [2, 3] [0, 0]\n");
    let main = body(&mir, "main.main");
    // Whether the block makes a list unique between its start and the call of `callee`.
    let made_unique_before = |callee: &str| {
        let call = format!("call {callee}(");
        main.iter().enumerate().any(|(j, line)| {
            line.contains(&call)
                && main[..j]
                    .iter()
                    .rev()
                    .take_while(|l| !l.contains("call ") && !l.trim_start().starts_with("bb"))
                    .any(|l| l.contains("stilt_rt_unique("))
        })
    };
    assert!(made_unique_before("main.bump_all"), "{mir}");
    assert!(made_unique_before("main.zero_first"), "{mir}");
    assert!(!made_unique_before("main.zero_last"), "{mir}");
}

/// facts.writes-in-place: under `without alloc`, a write through the fields of an element whose
/// type isn't copy-on-write is in place. `step` calls nothing and writes each element where it is,
/// once its list is unique; `main` shares the list with `keep`, so it makes the list unique at the
/// call, and `keep` keeps its value.
#[test]
fn an_element_that_holds_nothing_on_the_heap_is_written_in_place() {
    let source = "type Particle = { x: f64, v: f64 }\n\nfn step(inout ps: List<Particle>, dt: f64) without alloc {\n  for i in 0..ps.len() { ps[i].x += ps[i].v * dt }\n}\n\nfn main() / io {\n  var ps = [Particle { x: 0.0, v: 1.0 }, Particle { x: 1.0, v: 2.0 }]\n  let keep = ps\n  step(inout ps, 0.5)\n  print(\"{keep[0].x} {ps[0].x} {ps[1].x}\")\n}\n";
    let mir = runs_as("elements", source, "0.0 0.5 2.0\n");
    let step = body(&mir, "main.step");
    let calls: Vec<&&str> = step
        .iter()
        .filter(|l| l.contains(" = call ") && !l.contains("List.len("))
        .collect();
    assert!(calls.is_empty(), "{mir}");
    assert!(step.iter().any(|l| l.contains("list_element_at(")), "{mir}");
    let main = body(&mir, "main.main");
    let call = main
        .iter()
        .position(|l| l.contains("call main.step("))
        .unwrap_or_else(|| panic!("no call of step in\n{mir}"));
    assert!(
        main[..call]
            .iter()
            .rev()
            .take(2)
            .any(|l| l.contains("stilt_rt_unique(")),
        "{mir}"
    );
}
