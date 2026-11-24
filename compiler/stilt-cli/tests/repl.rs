//! `stilt repl`: the REPL (repl.sessions). Each test drives a session through its
//! standard input, a line at a time, waiting for each answer before the next input, and edits
//! the program's files between inputs where the record's rules need it.

mod common;

use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::time::{Duration, Instant};

/// How long a test waits for the session to show what it expects.
const PATIENCE: Duration = Duration::from_secs(30);

/// The program of the record's example: orders and their total.
const ORDERS: &str = "type Order = { name: str, qty: i64 }\n\nfn total(orders: List<Order>) -> i64 {\n  orders.fold(0, |acc, o| acc + o.qty)\n}\n\nfn first(orders: List<Order>) -> Order {\n  orders[0]\n}\n\nfn main() / io {\n  print(\"{total([])}\")\n}\n";

/// A session, killed when it is dropped.
struct Session {
    child: Child,
    stdin: Option<ChildStdin>,
    dir: PathBuf,
}

impl Session {
    /// A session in a directory of the test's own, which holds `files`.
    fn start(name: &str, files: &[(&str, &str)]) -> Self {
        Self::open(common::project("repl", name, files))
    }

    /// A session in `dir`.
    fn open(dir: PathBuf) -> Self {
        let out = fs::File::create(dir.join("out.txt")).expect("stdout can be written");
        let err = fs::File::create(dir.join("err.txt")).expect("stderr can be written");
        let mut child = Command::new(env!("CARGO_BIN_EXE_stilt"))
            .arg("repl")
            .current_dir(&dir)
            .stdin(Stdio::piped())
            .stdout(out)
            .stderr(err)
            .spawn()
            .expect("stilt runs");
        let stdin = child.stdin.take();
        Self { child, stdin, dir }
    }

    /// Gives the session a line of input.
    fn input(&mut self, line: &str) {
        let stdin = self.stdin.as_mut().expect("stdin is open");
        writeln!(stdin, "{line}").expect("the session reads stdin");
        stdin.flush().expect("the session reads stdin");
    }

    /// Gives the session a line, and waits until its stdout ends with `answer`, a line.
    fn answers(&mut self, line: &str, answer: &str) {
        self.input(line);
        let want = format!("{answer}\n");
        self.wait(&format!("{answer:?} after {line:?}"), |out, _| {
            out.ends_with(&want)
        });
    }

    /// Gives the session a line, and waits until its stderr holds `report` once more.
    fn reports(&mut self, line: &str, report: &str) {
        let before = self.stderr().matches(report).count();
        self.input(line);
        self.wait(&format!("{report:?} after {line:?}"), |_, err| {
            err.matches(report).count() > before
        });
    }

    fn edit(&self, from: &str, to: &str) {
        let path = self.dir.join("main.lt");
        let text = fs::read_to_string(&path).expect("the program can be read");
        assert!(text.contains(from), "the program holds {from:?}");
        fs::write(&path, text.replace(from, to)).expect("the program can be written");
    }

    fn stdout(&self) -> String {
        fs::read_to_string(self.dir.join("out.txt")).unwrap_or_default()
    }

    fn stderr(&self) -> String {
        fs::read_to_string(self.dir.join("err.txt")).unwrap_or_default()
    }

    /// Waits until `seen` holds of what the session wrote, and fails the test if it never does.
    fn wait(&self, what: &str, seen: impl Fn(&str, &str) -> bool) {
        let start = Instant::now();
        while start.elapsed() < PATIENCE {
            if seen(&self.stdout(), &self.stderr()) {
                return;
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        panic!(
            "never saw {what}\n--- stdout\n{}\n--- stderr\n{}",
            self.stdout(),
            self.stderr()
        );
    }

    /// Ends standard input, and gives the session's exit status.
    fn end(&mut self) -> i32 {
        self.stdin = None;
        self.status()
    }

    fn status(&mut self) -> i32 {
        let start = Instant::now();
        while start.elapsed() < PATIENCE {
            if let Some(status) = self
                .child
                .try_wait()
                .expect("the session can be waited for")
            {
                return status.code().unwrap_or(-1);
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        panic!("the session never ended\n--- stderr\n{}", self.stderr());
    }
}

impl Drop for Session {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
        common::stop_engine(&self.dir, Path::new("."));
    }
}

/// The record's example: a `let`, an expression, an edit of `main.lt` that the next input sees
/// with the binding kept, and a panic that ends only its input (repl.scope, repl.inputs,
/// repl.input-checking, repl.answers, repl.running-inputs, repl.program-edits and
/// repl.bindings-across-edits).
#[test]
fn the_records_example() {
    let mut s = Session::start("example", &[("main.lt", ORDERS)]);
    s.answers(
        r#"let orders = [Order { name: "a", qty: 2 }, Order { name: "b", qty: 5 }]"#,
        "orders: List<Order>",
    );
    s.answers("total(orders)", "7: i64");
    s.edit("acc + o.qty)", "acc + o.qty * 2)");
    s.answers("total(orders)", "14: i64");
    s.reports(
        "orders[9]",
        "panic: bounds: index 9 is out of bounds for a list of length 2\n",
    );
    s.answers("orders.len()", "2: i64");
    assert_eq!(s.end(), 0);
    assert!(
        !s.stderr().contains("  at "),
        "a panic in the input has no place:\n{}",
        s.stderr()
    );
}

/// repl.scope: inputs see the module's items and imports, and `:module NAME` moves the session to
/// another module, whose scope the next inputs see, the bindings among it.
#[test]
fn the_scope_is_a_modules() {
    let helpers = "pub fn twice(n: i64) -> i64 { n * 2 }\n\nfn secret() -> i64 { 42 }\n";
    let main = "use helpers\n\nfn main() {}\n";
    let mut s = Session::start("scope", &[("main.lt", main), ("helpers.lt", helpers)]);
    s.answers("helpers.twice(2)", "4: i64");
    s.answers("let k = 3", "k: i64");
    s.reports("secret()", "Unknown name `secret`");
    s.input(":module helpers");
    s.answers("secret() + twice(k)", "48: i64");
    s.reports(":module nope", "stilt: the program has no module `nope`\n");
    s.answers("secret()", "42: i64");
    assert_eq!(s.end(), 0);
}

/// repl.sessions: a program with errors is reported first, and its code with an error panics where
/// an input reaches it, while the rest runs.
#[test]
fn a_program_with_errors() {
    let main = ORDERS.replace("orders[0]", "orders[0].nmae");
    let mut s = Session::start("errors", &[("main.lt", &main)]);
    s.answers("total([])", "0: i64");
    s.reports("first([])", "panic: check-error:");
    let err = s.stderr();
    let reported = err
        .find("[E0313]")
        .expect("the program's error is reported");
    assert!(reported < err.find("panic:").unwrap_or(0), "{err}");
    assert_eq!(s.end(), 0);
}

/// repl.sessions: with no program in the working directory, inputs see the prelude alone.
#[test]
fn without_a_program_the_prelude_alone() {
    let mut s = Session::start("prelude", &[]);
    s.answers("[1, 2, 3].map(|x| x * 2)", "[2, 4, 6]: List<i64>");
    s.reports("total([])", "Unknown name `total`");
    assert_eq!(s.end(), 0);
}

/// repl.answers: each answer gives the value, as `show_nested` shows it, and its type; a type
/// without `Show`, its type alone; a `let`, each name it binds with its type, a name bound
/// again replacing the binding. What the input prints comes before its answer.
#[test]
fn answers() {
    let mut s = Session::start("answers", &[("main.lt", ORDERS)]);
    s.answers(r#""ana""#, r#""ana": str"#);
    s.answers("|x: i64| x + 1", "fn(i64) -> i64");
    s.answers(r#"let (n, word) = (2, "two")"#, "word: str");
    assert!(
        s.stdout().ends_with("n: i64\nword: str\n"),
        "{}",
        s.stdout()
    );
    s.answers("let n = n * 10", "n: i64");
    s.answers("(n, word)", r#"(20, "two"): (i64, str)"#);
    s.answers(r#"print("hello")"#, "(): ()");
    assert!(s.stdout().ends_with("hello\n(): ()\n"), "{}", s.stdout());
    s.input(r#"let _ = print("quiet")"#);
    s.answers("word", r#""two": str"#);
    assert!(
        s.stdout().ends_with("quiet\n\"two\": str\n"),
        "{}",
        s.stdout()
    );
    assert_eq!(s.end(), 0);
}

/// repl.inputs and repl.input-checking: an input is an expression or a `let`, checked as a test's
/// body of its module, whose diagnostics are placed at `input N`; one with an error, or that the
/// REPL doesn't take, runs nothing and binds nothing.
#[test]
fn inputs_it_refuses() {
    let mut s = Session::start("refused", &[("main.lt", ORDERS)]);
    s.answers("let n = 1", "n: i64");
    let declaration = "stilt: input 2 is a declaration, which the program's files hold";
    s.reports("fn f() -> i64 { 1 }", declaration);
    s.reports("var v = 1", "stilt: input 3 is a `var`");
    s.reports("n = 2", "stilt: input 4 is an assignment");
    s.reports("assert n == 1", "stilt: input 5 is an `assert`");
    s.reports(":quit", "stilt: input 6 is no command");
    s.reports("1 +", "input 7:1:4  [E0100]");
    s.reports(r#"let n = n + "a""#, "input 8:1:");
    s.reports("let m = []", "[E0312]");
    s.reports("m", "Unknown name `m`");
    s.answers("n", "1: i64");
    assert_eq!(s.end(), 0);
}

/// repl.running-inputs: a raise or a panic ends only its input, which binds nothing; a panic in the
/// program's code keeps its place; `exit` ends the session with its status.
#[test]
fn raises_and_panics_end_only_their_input() {
    let main = "fn check(n: i64) -> i64 / raise<str> {\n  if n < 0 { raise \"negative\" }\n  n\n}\n\nfn main() {}\n";
    let mut s = Session::start("ended", &[("main.lt", main), ("orders.lt", ORDERS)]);
    s.reports("try check(-1)", "error: negative\n");
    s.answers("try check(4)", "4: i64");
    s.reports("let xs: List<i64> = [][0]", "panic: bounds:");
    s.reports("xs", "Unknown name `xs`");
    s.answers("let n = 5", "n: i64");
    s.reports("let n = try check(-2)", "error: negative\n");
    s.reports("let n: i64 = [][0]", "panic: bounds:");
    s.answers("n + 1", "6: i64");
    s.input(":module orders");
    s.reports("first([])", "  at orders.lt:8:3\n");
    s.input("exit(3)");
    assert_eq!(s.status(), 3);
}

/// repl.program-edits and repl.bindings-across-edits: bindings keep their values across edits,
/// which are patched as `run` patches them; an edit that changes a binding's type drops it, with a
/// note, and one that changes any declaration drops a binding that holds a function; an edit with
/// errors is reported, and its code with an error panics where it is reached.
#[test]
fn bindings_across_edits() {
    let mut s = Session::start("edits", &[("main.lt", ORDERS)]);
    s.answers(
        r#"let orders = [Order { name: "a", qty: 2 }]"#,
        "orders: List<Order>",
    );
    s.answers("let k = 7", "k: i64");
    s.answers("let add = |x: i64| x + k", "add: fn(i64) -> i64");
    s.edit("qty: i64 }", "qty: i64, price: f64 }");
    s.reports(
        "k",
        "note: `orders` is dropped, since the edit changed its type, `List<Order>`\n",
    );
    // The answer goes to stdout and the notes to stderr, so either may be seen first.
    s.wait("\"7: i64\" after \"k\"", |out, _| out.ends_with("7: i64\n"));
    s.wait("the note that drops `add`", |_, err| {
        err.contains("note: `add` is dropped")
    });
    s.reports("orders", "Unknown name `orders`");
    s.edit("acc + o.qty)", "acc + o.qtyy)");
    s.reports("k + 1", "[E0313]");
    s.reports("total([])", "panic: check-error:");
    s.edit("acc + o.qtyy)", "acc + o.qty)");
    s.answers("total([])", "0: i64");
    assert_eq!(s.stderr().matches("[E0313]").count(), 1, "{}", s.stderr());
    assert_eq!(s.end(), 0);
}

/// repl.prompt-and-end: a session keeps its program's engine from stopping, however long it waits.
#[test]
fn a_session_keeps_its_engine() {
    let dir = common::project("repl", "engine", &[("main.lt", ORDERS)]);
    let mut engine = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(["engine", "--idle", "1", "."])
        .current_dir(&dir)
        .spawn()
        .expect("the engine starts");
    std::thread::sleep(Duration::from_millis(500));
    let mut s = Session::open(dir);
    s.answers("total([])", "0: i64");
    std::thread::sleep(Duration::from_millis(2500));
    s.answers("let n = 1", "n: i64");
    let alive = engine
        .try_wait()
        .expect("the engine can be waited for")
        .is_none();
    assert!(alive, "the engine idled while the session was open");
    assert_eq!(s.end(), 0);
    let _ = engine.kill();
    let _ = engine.wait();
}

/// repl.no-one-shot-evaluation: `repl` takes no expression on its command line.
#[test]
fn no_one_shot_evaluation() {
    let output = common::stilt(&["repl", "--eval", "1 + 2"], None);
    assert_eq!(output.status.code(), Some(2), "{}", common::stderr(&output));
    assert_eq!(common::stdout(&output), "");
}
