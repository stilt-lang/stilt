//! `stilt show` (Inferred facts, "Seven commands"; goals shown-facts, short-messages and
//! hole-context): a code's explanation, a module's skeleton as the design shows it, a function with
//! its facts written in, the calls that lose reuse among them, and its variables' inferred types,
//! and the context of each hole. The facts themselves are checked against the records by the facts
//! suite (`tests/facts.rs`), and the holes' contexts by the holes suite (`tests/holes.rs`).

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

mod common;

use serde_json::Value;
use stilt_diag::codes;

fn repository() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Runs `stilt show` with `args` in `dir`.
fn show(dir: &Path, args: &[&str]) -> Output {
    let output = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .arg("show")
        .args(args)
        .current_dir(dir)
        .output()
        .expect("stilt runs");
    common::stop_engine(dir, Path::new("."));
    output
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

/// A directory holding a program whose `main.lt` is `source`.
fn program(name: &str, source: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("show")
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("the directory can be made");
    fs::write(dir.join("main.lt"), source).expect("the program can be written");
    dir
}

#[test]
fn a_code_shows_its_entry_in_the_registry() {
    let output = show(&repository(), &["E0404"]);
    assert!(output.status.success());
    assert_eq!(stdout(&output), codes::E0404.explanation());
    let output = show(&repository(), &["--json", "E0404"]);
    let record: Value = serde_json::from_slice(&output.stdout).expect("one JSON record");
    assert_eq!(record["code"], "E0404");
    assert_eq!(record["reference"], "modes.change-while-iterating");
    let output = show(&repository(), &["E9999"]);
    assert_eq!(
        output.status.code(),
        Some(2),
        "a code that isn't registered"
    );
}

#[test]
fn a_module_shows_as_the_skeleton_the_design_measures() {
    let dir = repository().join("tools/measurements/token-cost/programs");
    let output = show(&dir, &["main", "orders.lt"]);
    assert!(output.status.success());
    let skeleton = fs::read_to_string(dir.join("orders.skeleton.txt")).expect("it is readable");
    assert_eq!(stdout(&output), skeleton);
}

/// A program whose functions have facts of each kind.
const SOURCE: &str = "type Stack = { items: List<i64> }\n\nimpl Stack {\n  /// The stack with `x` on top.\n  fn pushed(self, x: i64) -> Stack {\n    var s = self\n    s.items.push(x)\n    s\n  }\n}\n\nfn top(s: Stack) -> i64 {\n  s.items[s.items.len() - 1]\n}\n\nfn main() / io {\n  let s = Stack { items: [] }.pushed(4)\n  print(\"{top(s)}\")\n}\n";

#[test]
fn a_function_shows_with_its_facts_written_in() {
    let dir = program("facts", SOURCE);
    let output = show(&dir, &["main.Stack.pushed"]);
    assert!(output.status.success());
    // modes.escaping and modes.show: `s` escapes where it is returned.
    assert_eq!(
        stdout(&output),
        "module main [core]\nimpl Stack {\n  /// The stack with `x` on top.\n  fn pushed(self, x: i64) -> Stack [consumes self, alloc] {\n    var s: Stack = self // consumes `self`\n    s.items.push(x) // `List.push` allocates\n    s // `s` escapes, returned\n  }\n}\n"
    );
    let output = show(&dir, &["main.main"]);
    assert_eq!(
        stdout(&output),
        "module main [core]\nfn main() / io [panic, overflow, alloc, io: console] {\n  let s: Stack = Stack { items: [] }.pushed(4) // `Stack.pushed` allocates, through `List.push`; a list allocates\n  print(\"{top(s)}\") // `top` can panic, through an index; `top` can overflow, through a `-`; `print` allocates; an interpolated string allocates; the built-in `show` allocates; `print` uses `console`\n}\n"
    );
}

#[test]
fn a_function_shows_as_a_json_record() {
    let dir = program("json", SOURCE);
    let output = show(&dir, &["--json", "main.top"]);
    let record: Value = serde_json::from_slice(&output.stdout).expect("one JSON record");
    // edits.showing-parts: the address with its hash, the canonical text, and the body's address;
    // modes.show: the modes, of which `top`'s bindings have none but their defaults;
    // views.show and projections.show: the sources of its views, read or written, of which
    // it has none; facts.visibility: its in-place parameters, `div` and `copy`, of which it has
    // none; facts.visibility: its capabilities, of which it has none; shared.locks: `locks`,
    // which it doesn't have; par.atomic-sites: the lines that may make counts atomic, of which it
    // has none; meta.reflects: the type parameters it reflects on, of which it has none;
    // facts.shown-proofs: the checks that verification proves, of which it has none, since its
    // index is no name or literal (facts.guards). c.exported-fact: whether it is exported.
    // c.unsafe-and-foreign: its `unsafe` blocks and the foreign functions it names, of which it has
    // none.
    let text = "fn top(s: Stack) -> i64 { s.items[s.items.len() - 1] }";
    let body = "{ s.items[s.items.len() - 1] }";
    let expected: Value = serde_json::from_str(&format!(
        r#"{{"function": "main.top", "file": "main.lt", "line": 12, "tier": "core",
            "exported": false, "consumes": [], "lost_reuse": [], "alloc": [], "locals": [],
            "escapes": [], "shared": [], "once": [], "views": [], "writes": [],
            "in_place": [], "div": [], "copy": [], "locks": [], "atomic": [], "proved": [],
            "reflects": [], "unsafe": [], "foreign": [],
            "capabilities": {{"fs": [], "net": [], "clock": [], "env": [], "console": [],
                              "rand": [], "spawn": [], "exec": []}},
            "panic": [{{"line": 13, "cause": "an index can panic"}}],
            "overflow": [{{"line": 13, "cause": "a `-` can overflow"}}],
            "at": "main.top#{}", "text": "{text}", "body": "main.top/body#{}"}}"#,
        common::hash(text),
        common::hash(body)
    ))
    .expect("valid JSON");
    assert_eq!(record, expected);
    let output = show(&dir, &["--json", "main"]);
    let record: Value = serde_json::from_slice(&output.stdout).expect("one JSON record");
    let names: Vec<&str> = record["functions"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|f| f["function"].as_str())
        .collect();
    assert_eq!(names, ["main.Stack.pushed", "main.top", "main.main"]);
    assert_eq!(record["tier"], "core");
}

/// A program whose `main` keeps using a list it passes to a parameter that `grown` consumes
/// (values.consumed-parameters).
const REUSE: &str = "fn grown(xs: List<i64>) -> List<i64> {\n  var out = xs\n  out.push(1)\n  out\n}\n\nfn main() / io {\n  let xs = [1, 2]\n  let ys = grown(xs)\n  print(\"{xs.len()} {ys.len()}\")\n}\n";

#[test]
fn a_call_that_loses_reuse_shows_where() {
    let dir = program("reuse", REUSE);
    let output = show(&dir, &["main.main"]);
    assert!(output.status.success());
    // modes.escaping and modes.show: `xs` escapes where it is passed to a consumed parameter.
    assert_eq!(
        stdout(&output),
        "module main [core]\nfn main() / io [alloc, io: console] {\n  let xs: List<i64> = [1, 2] // a list allocates\n  let ys: List<i64> = grown(xs) // `xs` is used after this call, so `grown` can't reuse it; `xs` escapes, consumed by `grown`; `grown` allocates, through `List.push`\n  print(\"{xs.len()} {ys.len()}\") // `print` allocates; an interpolated string allocates; the built-in `show` allocates; `print` uses `console`\n}\n"
    );
    let output = show(&dir, &["--json", "main.main"]);
    let record: Value = serde_json::from_slice(&output.stdout).expect("one JSON record");
    let expected: Value = serde_json::from_str(
        r#"[{"place": "xs", "line": 9,
             "cause": "`xs` is used after this call, so `grown` can't reuse it"}]"#,
    )
    .expect("valid JSON");
    assert_eq!(record["lost_reuse"], expected);
}

/// A program whose `inout` parameter goes back to the caller as it was after a call that consumes
/// it: where `kept` returns, and where `risky` raises (values.consumed-parameters and
/// values.inout-arguments).
const BACK: &str = "type Table = { slots: List<i64> }\n\ntype State = { table: Table, n: i64 }\n\nfn start(table: Table) -> State { State { table, n: 0 } }\n\nfn kept(inout table: Table) -> i64 {\n  var s = start(table)\n  s.n\n}\n\nfn risky(inout table: Table, n: i64) / raise<i64> {\n  var s = start(table)\n  if n < 0 { raise n }\n  table = s.table\n}\n\nfn main() {}\n";

#[test]
fn an_inout_parameter_that_goes_back_to_the_caller_shows_where_it_loses_reuse() {
    let dir = program("back", BACK);
    let output = show(&dir, &["main.kept"]);
    assert!(output.status.success());
    assert_eq!(
        stdout(&output),
        "module main [core]\nfn kept(inout table: Table) -> i64 {\n  var s: State = start(table) // `table` goes back to the caller when the function returns, so `start` can't reuse it\n  s.n\n}\n"
    );
    let output = show(&dir, &["main.risky"]);
    // modes.escaping and modes.show: a part of `s` escapes where it is assigned to `table`.
    assert_eq!(
        stdout(&output),
        "module main [core]\nfn risky(inout table: Table, n: i64) / raise<i64> {\n  var s: State = start(table) // `table` goes back to the caller when the function raises, so `start` can't reuse it\n  if n < 0 { raise n }\n  table = s.table // `s` escapes, assigned to `table`\n}\n"
    );
}

#[test]
fn a_variable_shows_its_inferred_type_where_the_source_writes_none() {
    let dir = program(
        "locals",
        "fn total() -> i64 {\n  let xs: List<i64> = [1, 2]\n  var n = 0\n  let (a, b) = (xs[0], || n)\n  a + b()\n}\n",
    );
    let output = show(&dir, &["main.total"]);
    // facts.div: a call through a function value that a local holds may not end; facts.guards: no
    // test guards the index into the list of two, so it can panic.
    assert_eq!(
        stdout(&output),
        "module main [core]\nfn total() -> i64 [panic, overflow, alloc, div] {\n  let xs: List<i64> = [1, 2] // a list allocates\n  var n: i64 = 0\n  let (a, b): (i64, fn() -> i64) = (xs[0], || n) // an index can panic; a closure allocates\n  a + b() // a `+` can overflow; a call through the local `b` may not end\n}\n"
    );
    let output = show(&dir, &["--json", "main.total"]);
    let record: Value = serde_json::from_slice(&output.stdout).expect("one JSON record");
    let expected: Value = serde_json::from_str(
        r#"[{"pattern": "n", "line": 3, "type": "i64"},
            {"pattern": "(a, b)", "line": 4, "type": "(i64, fn() -> i64)"}]"#,
    )
    .expect("valid JSON");
    assert_eq!(record["locals"], expected);
}

/// A program whose bindings have modes other than their defaults (modes.bindings-and-axes): a
/// parameter called once, a closure passed to it, a `var` written while a copy of it lasts, and a
/// local that escapes.
const MODES: &str = "fn run(f: fn() -> i64) -> i64 {\n  f()\n}\n\nfn main() -> List<i64> {\n  var xs = [1]\n  let ys = xs\n  xs.push(run(|| ys.len()))\n  xs\n}\n";

#[test]
fn a_function_shows_the_modes_of_its_bindings() {
    let dir = program("modes", MODES);
    // modes.once-parameters and modes.show: a `once` parameter is in the bracket, and at its one
    // use.
    let output = show(&dir, &["main.run"]);
    assert_eq!(
        stdout(&output),
        "module main [core]\nfn run(f: fn() -> i64) -> i64 [once f] {\n  f() // `f` runs once\n}\n"
    );
    // modes.escaping, modes.shared-writes, modes.once-closures and modes.show: `xs` is written
    // while `ys` holds a copy, the closure passed to a `once` parameter runs once, and `xs` escapes
    // where it is returned. facts.copy: the shared write copies shared data.
    let output = show(&dir, &["main.main"]);
    assert_eq!(
        stdout(&output),
        "module main [core]\nfn main() -> List<i64> [alloc, copy] {\n  var xs: List<i64> = [1] // a list allocates\n  let ys: List<i64> = xs\n  xs.push(run(|| ys.len())) // `xs` is shared with `ys`, so this write may copy it; this closure runs once; `List.push` allocates; a closure allocates; a write to `xs` while `ys` shares it copies a shared value\n  xs // `xs` escapes, returned\n}\n"
    );
    let output = show(&dir, &["--json", "main.main"]);
    let record: Value = serde_json::from_slice(&output.stdout).expect("one JSON record");
    let expected: Value = serde_json::from_str(
        r#"{"escapes": [{"line": 9, "name": "xs", "cause": "`xs` escapes, returned"}],
            "shared": [{"line": 8, "name": "xs",
                        "cause": "`xs` is shared with `ys`, so this write may copy it"}],
            "once": [{"line": 8, "cause": "this closure runs once"}]}"#,
    )
    .expect("valid JSON");
    for key in ["escapes", "shared", "once"] {
        assert_eq!(record[key], expected[key], "{key}");
    }
}

/// A program with views (views.what-view-is and views.across-calls): a function whose result views
/// its parameter, and a binding that views a local through the call.
const VIEWS: &str = "use std.view\n\nfn first(line: str) -> view.View<str> {\n  view.View.of(line, 0, 2)\n}\n\nfn main() / io {\n  let text = \"to be\"\n  let w = first(text)\n  print(\"{w.len()}\")\n}\n";

#[test]
fn a_function_shows_the_sources_of_its_views() {
    let dir = program("views", VIEWS);
    // views.std-view and views.show: a module that names a view type is in the advanced tier, and a
    // result that views a parameter is in the bracket, and at the line of the expression
    // returned; `View.of` can panic (views.functions-of-views).
    let output = show(&dir, &["main.first"]);
    assert_eq!(
        stdout(&output),
        "module main [advanced]\nfn first(line: str) -> view.View<str> [views line, panic] {\n  view.View.of(line, 0, 2) // the result views `line`; `View.of` can panic\n}\n"
    );
    // views.across-calls and views.show: the result of `first` views its argument `text`, so `w`
    // does, which stands for `fixed`.
    let output = show(&dir, &["main.main"]);
    assert_eq!(
        stdout(&output),
        "module main [advanced]\nfn main() / io [panic, alloc, io: console] {\n  let text: str = \"to be\"\n  let w: View<str> = first(text) // `w` views `text`; `first` can panic, through `View.of`\n  print(\"{w.len()}\") // `print` allocates; an interpolated string allocates; the built-in `show` allocates; `print` uses `console`\n}\n"
    );
    let output = show(&dir, &["--json", "main"]);
    let record: Value = serde_json::from_slice(&output.stdout).expect("one JSON record");
    assert_eq!(record["tier"], "advanced");
    let views: Vec<&Value> = record["functions"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|f| &f["views"])
        .collect();
    let expected: Value = serde_json::from_str(
        r#"[[{"line": 4, "name": "line", "cause": "the result views `line`"}],
            [{"line": 9, "name": "text", "cause": "`w` views `text`"}]]"#,
    )
    .expect("valid JSON");
    assert_eq!(serde_json::json!(views), expected);
}

/// A program with a projection and writable views (projections.writable-views): a function whose
/// result writes its `inout` parameter, a projection, and a writable binding.
const PROJECTIONS: &str = "use std.view\n\nfn left(inout xs: List<i64>) -> view.View<List<i64>> {\n  view.into(inout xs, 0, 1)\n}\n\nfn at(inout xs: List<i64>, i: i64) -> inout i64 {\n  yield xs[i]\n}\n\nfn main() / io {\n  var xs = [1, 2]\n  {\n    var tail = view.into(inout xs, 1, 2)\n    tail[0] = 9\n  }\n  at(inout xs, 0) = 5\n  print(\"{xs}\")\n}\n";

#[test]
fn a_function_shows_what_its_views_write() {
    let dir = program("projections", PROJECTIONS);
    // projections.declaring-projection and projections.show: a module that declares a projection is
    // in the advanced tier; a result that writes an `inout` parameter is in the bracket, and at the
    // line of the expression returned; `view.into` can panic and allocates
    // (projections.writable-views).
    let output = show(&dir, &["main.left"]);
    assert_eq!(
        stdout(&output),
        "module main [advanced]\nfn left(inout xs: List<i64>) -> view.View<List<i64>> [writes xs, panic, alloc] {\n  view.into(inout xs, 0, 1) // the result writes `xs`; `view.into` can panic; `view.into` allocates\n}\n"
    );
    // projections.show: a projection's signature prints `-> inout T` as written, and nothing else
    // is printed for it; a `yield` through an index allocates (projections.yield).
    let output = show(&dir, &["main.at"]);
    assert_eq!(
        stdout(&output),
        "module main [advanced]\nfn at(inout xs: List<i64>, i: i64) -> inout i64 [panic, alloc] {\n  yield xs[i] // an index can panic; a `yield` through an index allocates\n}\n"
    );
    // projections.writable-modes and projections.show: `writes` at the line of a writable binding,
    // which stands for `fixed`, and a write through it doesn't allocate
    // (projections.places-through-views).
    let output = show(&dir, &["main.main"]);
    assert_eq!(
        stdout(&output),
        "module main [advanced]\nfn main() / io [panic, alloc, io: console] {\n  var xs: List<i64> = [1, 2] // a list allocates\n  {\n    var tail: View<List<i64>> = view.into(inout xs, 1, 2) // `tail` writes `xs`; `view.into` can panic; `view.into` allocates\n    tail[0] = 9 // an index can panic\n  }\n  at(inout xs, 0) = 5 // `at` can panic, through an index; `at` allocates, through a `yield` through an index\n  print(\"{xs}\") // `print` allocates; an interpolated string allocates; the built-in `show` allocates; `print` uses `console`\n}\n"
    );
    let output = show(&dir, &["--json", "main"]);
    let record: Value = serde_json::from_slice(&output.stdout).expect("one JSON record");
    assert_eq!(record["tier"], "advanced");
    let writes: Vec<&Value> = record["functions"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|f| &f["writes"])
        .collect();
    let expected: Value = serde_json::from_str(
        r#"[[{"line": 4, "name": "xs", "cause": "the result writes `xs`"}], [],
            [{"line": 14, "name": "xs", "cause": "`tail` writes `xs`"}]]"#,
    )
    .expect("valid JSON");
    assert_eq!(serde_json::json!(writes), expected);
}

#[test]
fn a_parameter_rebound_with_var_is_consumed_where_it_is_rebound() {
    // values.consumed-parameters: rebinding a parameter with `var` consumes it, even when the `var`
    // is never changed.
    let dir = program(
        "rebound",
        "fn kept(xs: List<i64>) -> i64 {\n  var ys = xs\n  ys.len()\n}\n",
    );
    let output = show(&dir, &["main.kept"]);
    assert_eq!(
        stdout(&output),
        "module main [core]\nfn kept(xs: List<i64>) -> i64 [consumes xs] {\n  var ys: List<i64> = xs // consumes `xs`\n  ys.len()\n}\n"
    );
}

#[test]
fn an_address_that_names_nothing_is_refused() {
    let dir = program("nothing", SOURCE);
    let output = show(&dir, &["main.missing"]);
    assert_eq!(output.status.code(), Some(2));
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "stilt: the program has no module or part `main.missing`\n"
    );
}

#[test]
fn a_function_with_an_error_has_no_facts() {
    let dir = program(
        "broken",
        "fn first(xs: List<i64>) -> i64 {\n  xs[missing]\n}\n",
    );
    let output = show(&dir, &["main.first"]);
    assert!(output.status.success());
    assert_eq!(
        stdout(&output),
        "module main [core]\nfn first(xs: List<i64>) -> i64 {\n  xs[missing]\n}\n"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("`main.first` has an error"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// A program whose hole fits one function alone: no function of the standard library makes a
/// `Point`.
const MOVED: &str = "type Point = { x: i64, y: i64 }\n\nfn origin() -> Point { Point { x: 0, y: 0 } }\n\nfn moved(p: Point, by: i64) -> Point / io = ?\n";

#[test]
fn a_hole_shows_its_context_after_its_part() {
    let dir = program("hole", MOVED);
    let output = show(&dir, &["main.moved/body"]);
    assert!(output.status.success());
    assert_eq!(
        stdout(&output),
        "= ?\n\nhole at main.lt:5:45\n  expects: Point\n  effects: io\n  types:\n    type Point = { x: i64, y: i64 }\n  in scope:\n    p: Point\n    by: i64\n  fits:\n    origin() -> Point\n"
    );
}

#[test]
fn a_module_record_holds_the_holes_of_its_functions() {
    let dir = program("hole-module", MOVED);
    let output = show(&dir, &["--json", "main"]);
    let record: Value = serde_json::from_slice(&output.stdout).expect("a JSON record");
    let moved = record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|f| f["function"] == "main.moved")
        .expect("`moved` is shown");
    let hole = &moved["holes"][0];
    assert_eq!(hole["line"], 5);
    assert_eq!(hole["expects"], "Point");
    assert_eq!(hole["headers"], serde_json::json!(["origin() -> Point"]));
    assert_eq!(hole["types"][0]["path"], "main.Point");
}

#[test]
fn a_hole_under_without_panic_fits_no_function_that_can_panic() {
    // effects.without-panic: a hole can panic, so the function has an error, but its body still
    // checks, and its hole has a context.
    let dir = program(
        "hole-limits",
        "fn first(xs: List<i64>) -> i64 { xs[0] }\n\nfn safe(xs: List<i64>) -> i64 without panic { ? }\n",
    );
    let output = show(&dir, &["--json", "main.safe/body"]);
    let record: Value = serde_json::from_slice(&output.stdout).expect("a JSON record");
    let hole = &record["holes"][0];
    assert_eq!(hole["without"], serde_json::json!(["panic"]));
    let headers: Vec<&str> = hole["headers"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(Value::as_str)
        .collect();
    assert!(headers.contains(&"List.len(self) -> i64"), "{headers:?}");
    assert!(
        !headers.contains(&"first(xs: List<i64>) -> i64"),
        "{headers:?}"
    );
}

#[test]
fn a_hole_in_a_body_with_a_type_error_has_no_context() {
    // facts.bodies-with-errors: what the hole expects isn't known.
    let dir = program(
        "hole-broken",
        "fn f(x: i64) -> i64 {\n  let y: str = x\n  ?\n}\n",
    );
    let output = show(&dir, &["--json", "main.f/body"]);
    let record: Value = serde_json::from_slice(&output.stdout).expect("a JSON record");
    assert!(record.get("holes").is_none(), "{record}");
}

#[test]
fn a_function_whose_patterns_name_another_module_s_variants_bare_shows_its_facts() {
    // patterns.variants-by-type: `Circle` and `Square` name the variants of `shapes.Shape`, so the
    // body has no error, and its facts are written in.
    let dir = program(
        "bare",
        "use shapes\n\nfn size(s: shapes.Shape) -> i64 {\n  match s {\n    Circle(r) => r\n    Square(xs) => xs[0]\n  }\n}\n",
    );
    let shapes = "pub type Shape = | Circle(i64) | Square(List<i64>)\n";
    fs::write(dir.join("shapes.lt"), shapes).expect("the module can be written");
    let output = show(&dir, &["main.size"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        stdout(&output),
        "module main [core]\nfn size(s: shapes.Shape) -> i64 [panic] {\n  match s {\n    Circle(r) => r\n    Square(xs) => xs[0] // an index can panic\n  }\n}\n"
    );
}

#[test]
fn a_function_shows_its_capabilities_after_its_implicit_effects() {
    // facts.visibility: `io: fs, clock`, in the order of facts.capabilities, each at the line that
    // causes it, and a module's capability limits in its header (facts.without).
    let dir = program(
        "capabilities",
        "module main\nwithout net\n\nuse std.clock\nuse std.fs\n\nfn stamp() -> i64 / io {\n  if fs.exists(\"log\") { clock.unix_ms() } else { 0 }\n}\n\nfn main() / io { exit(0) }\n",
    );
    let output = show(&dir, &["main.stamp"]);
    assert_eq!(
        stdout(&output),
        "module main without net [core]\nfn stamp() -> i64 / io [alloc, io: fs, clock] {\n  if fs.exists(\"log\") { clock.unix_ms() } else { 0 } // `fs.exists` allocates; `fs.exists` uses `fs`; `clock.unix_ms` uses `clock`\n}\n"
    );
    // facts.io-and-capabilities: `exit` performs `io` with no capability, so `main` shows none.
    let output = show(&dir, &["main.main"]);
    assert_eq!(
        stdout(&output),
        "module main without net [core]\nfn main() / io { exit(0) }\n"
    );
}
