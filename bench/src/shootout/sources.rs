//! Each language's text of the shootout's project ([`super::project`]): its files around the
//! modules, and each module, as the language's programmers write them. Every version computes
//! the same numbers: a 64-bit integer's arithmetic stays far below its bounds.

use std::fmt::Write as _;
use std::path::PathBuf;

use super::Language;
use super::project::{Function, Shape};

impl Language {
    /// The path of module `i`, in the project's directory.
    pub(crate) fn module_path(self, i: usize) -> PathBuf {
        PathBuf::from(match self {
            Language::Stilt => format!("m{i}.lt"),
            Language::Rust => format!("src/m{i}.rs"),
            Language::Go => format!("m{i}/m{i}.go"),
            Language::OCaml => format!("m{i}.ml"),
            Language::Swift => format!("Sources/shoot/m{i}.swift"),
        })
    }

    /// The files around the modules: `main`, which with `watch` prints what the last module's
    /// first function gives every 20 ms, and otherwise the sum of what its functions give, and
    /// the build's own files.
    pub(crate) fn scaffold(self, shape: Shape) -> Vec<(PathBuf, String)> {
        let last = shape.modules - 1;
        let sum = |line: &dyn Fn(usize) -> String| -> String {
            (0..shape.functions).map(|j| line(j) + "\n").collect()
        };
        let files: Vec<(&str, String)> = match self {
            Language::Stilt => vec![("main.lt", stilt_main(last, &sum))],
            Language::Rust => vec![
                (
                    "Cargo.toml",
                    "[package]\nname = \"shoot\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\n[workspace]\n".to_owned(),
                ),
                ("src/main.rs", rust_main(shape, &sum)),
            ],
            Language::Go => vec![
                ("go.mod", "module shoot\n\ngo 1.22\n".to_owned()),
                ("main.go", go_main(last, &sum)),
            ],
            Language::OCaml => vec![
                ("dune-project", "(lang dune 3.0)\n".to_owned()),
                ("dune", "(executable\n (name main)\n (libraries unix))\n".to_owned()),
                ("main.ml", ocaml_main(last, &sum)),
            ],
            Language::Swift => vec![
                (
                    "Package.swift",
                    "// swift-tools-version:5.9\nimport PackageDescription\n\nlet package = Package(\n    name: \"shoot\",\n    targets: [.executableTarget(name: \"shoot\", path: \"Sources/shoot\")]\n)\n".to_owned(),
                ),
                ("Sources/shoot/main.swift", swift_main(last, &sum)),
            ],
        };
        files
            .into_iter()
            .map(|(p, t)| (PathBuf::from(p), t))
            .collect()
    }

    /// The text of module `i`, whose functions are `functions`.
    pub(crate) fn module(self, i: usize, functions: &[Function]) -> String {
        let mut text = match (self, i) {
            (Language::Stilt, 0) => "// A module of the shootout's project.\n\npub type R = { a: i64, b: i64 }\n".to_owned(),
            (Language::Stilt, _) => format!("// A module of the shootout's project.\n\nuse m{}\n\npub type R = {{ a: i64, b: i64 }}\n", i - 1),
            (Language::Rust, 0) => "//! A module of the shootout's project.\n\npub struct R {\n    pub a: i64,\n    pub b: i64,\n}\n".to_owned(),
            (Language::Rust, _) => format!("//! A module of the shootout's project.\n\nuse crate::m{};\n\npub struct R {{\n    pub a: i64,\n    pub b: i64,\n}}\n", i - 1),
            (Language::Go, 0) => "// Package m0 is a module of the shootout's project.\npackage m0\n\n// R is the module's record.\ntype R struct{ A, B int64 }\n".to_owned(),
            (Language::Go, _) => format!("// Package m{i} is a module of the shootout's project.\npackage m{i}\n\nimport \"shoot/m{}\"\n\n// R is the module's record.\ntype R struct{{ A, B int64 }}\n", i - 1),
            (Language::OCaml, _) => "(* A module of the shootout's project. *)\n\ntype r = { a : int; b : int }\n".to_owned(),
            (Language::Swift, _) => format!("// A module of the shootout's project.\n\nenum M{i} {{\n    struct R {{\n        let a: Int\n        let b: Int\n    }}\n"),
        };
        for f in functions {
            text.push('\n');
            text.push_str(&self.function(f));
        }
        if self == Language::Swift {
            text.push_str("}\n");
        }
        text
    }

    fn function(self, f: &Function) -> String {
        let first = |modulo: &str| {
            if f.broken {
                format!("x {modulo} \"a\"")
            } else {
                format!("x {modulo} 1000")
            }
        };
        // The call of the function of the same name in the module before, if there is one.
        let before = |call: &dyn Fn(usize) -> String, field: &str| {
            if f.i == 0 {
                format!("r.{field}")
            } else {
                call(f.i - 1)
            }
        };
        let (j, c) = (f.j, f.constant);
        match self {
            Language::Stilt => {
                let call = before(&|m| format!("m{m}.f{j}(r.a)"), "a");
                format!(
                    "pub fn f{j}(x: i64) -> i64 {{\n  var acc = {}\n  for k in 0..4 {{\n    acc = (acc * 31 + k + {c}) % 1000003\n  }}\n  let r = R {{ a: acc, b: x % 7 }}\n  {call} + r.b\n}}\n",
                    first("%")
                )
            }
            Language::Rust => {
                let call = before(&|m| format!("m{m}::f{j}(r.a)"), "a");
                format!(
                    "pub fn f{j}(x: i64) -> i64 {{\n    let mut acc = {};\n    for k in 0..4 {{\n        acc = (acc * 31 + k + {c}) % 1000003;\n    }}\n    let r = R {{ a: acc, b: x % 7 }};\n    {call} + r.b\n}}\n",
                    first("%")
                )
            }
            Language::Go => {
                let call = before(&|m| format!("m{m}.F{j}(r.A)"), "A");
                format!(
                    "// F{j} is one of the module's functions.\nfunc F{j}(x int64) int64 {{\n\tacc := {}\n\tfor k := int64(0); k < 4; k++ {{\n\t\tacc = (acc*31 + k + {c}) % 1000003\n\t}}\n\tr := R{{A: acc, B: x % 7}}\n\treturn {call} + r.B\n}}\n",
                    first("%")
                )
            }
            Language::OCaml => {
                let call = before(&|m| format!("M{m}.f{j} r.a"), "a");
                format!(
                    "let f{j} x =\n  let acc = ref ({}) in\n  for k = 0 to 3 do\n    acc := ((!acc * 31) + k + {c}) mod 1000003\n  done;\n  let r = {{ a = !acc; b = x mod 7 }} in\n  {call} + r.b\n",
                    first("mod")
                )
            }
            Language::Swift => {
                let call = before(&|m| format!("M{m}.f{j}(r.a)"), "a");
                format!(
                    "    static func f{j}(_ x: Int) -> Int {{\n        var acc = {}\n        for k in 0..<4 {{\n            acc = (acc * 31 + k + {c}) % 1000003\n        }}\n        let r = R(a: acc, b: x % 7)\n        return {call} + r.b\n    }}\n",
                    first("%")
                )
            }
        }
    }
}

/// The lines that add each function of the last module to the total, one for each index.
type Sum<'a> = &'a dyn Fn(&dyn Fn(usize) -> String) -> String;

fn stilt_main(last: usize, sum: Sum<'_>) -> String {
    format!(
        "use std.cli\nuse std.clock\nuse m{last}\n\nfn total() -> i64 {{\n  var t = 0\n{}  t\n}}\n\nfn main() / io {{\n  if (cli.arg(0) else \"\") == \"watch\" {{\n    loop {{\n      print(\"{{m{last}.f0(1)}}\")\n      clock.sleep_ms(20)\n    }}\n  }}\n  print(\"{{total()}}\")\n}}\n",
        sum(&|j| format!("  t = (t + m{last}.f{j}({j})) % 1000003"))
    )
}

fn rust_main(shape: Shape, sum: Sum<'_>) -> String {
    let last = shape.modules - 1;
    format!(
        "{}\nfn total() -> i64 {{\n    let mut t = 0;\n{}    t\n}}\n\nfn main() {{\n    if std::env::args().nth(1).as_deref() == Some(\"watch\") {{\n        loop {{\n            println!(\"{{}}\", m{last}::f0(1));\n            std::thread::sleep(std::time::Duration::from_millis(20));\n        }}\n    }}\n    println!(\"{{}}\", total());\n}}\n",
        (0..shape.modules).fold(String::new(), |mut mods, i| {
            let _ = writeln!(mods, "mod m{i};");
            mods
        }),
        sum(&|j| format!("    t = (t + m{last}::f{j}({j})) % 1000003;"))
    )
}

fn go_main(last: usize, sum: Sum<'_>) -> String {
    format!(
        "package main\n\nimport (\n\t\"fmt\"\n\t\"os\"\n\t\"time\"\n\n\t\"shoot/m{last}\"\n)\n\nfunc total() int64 {{\n\tt := int64(0)\n{}\treturn t\n}}\n\nfunc main() {{\n\tif len(os.Args) > 1 && os.Args[1] == \"watch\" {{\n\t\tfor {{\n\t\t\tfmt.Println(m{last}.F0(1))\n\t\t\ttime.Sleep(20 * time.Millisecond)\n\t\t}}\n\t}}\n\tfmt.Println(total())\n}}\n",
        sum(&|j| format!("\tt = (t + m{last}.F{j}({j})) % 1000003"))
    )
}

fn ocaml_main(last: usize, sum: Sum<'_>) -> String {
    format!(
        "let total () =\n  let t = ref 0 in\n{}  !t\n\nlet () =\n  if Array.length Sys.argv > 1 && Sys.argv.(1) = \"watch\" then\n    while true do\n      print_endline (string_of_int (M{last}.f0 1));\n      Unix.sleepf 0.02\n    done\n  else print_endline (string_of_int (total ()))\n",
        sum(&|j| format!("  t := (!t + M{last}.f{j} {j}) mod 1000003;"))
    )
}

fn swift_main(last: usize, sum: Sum<'_>) -> String {
    format!(
        "import Foundation\n\nfunc total() -> Int {{\n    var t = 0\n{}    return t\n}}\n\nif CommandLine.arguments.count > 1 && CommandLine.arguments[1] == \"watch\" {{\n    while true {{\n        print(M{last}.f0(1))\n        fflush(stdout)\n        usleep(20000)\n    }}\n}}\nprint(total())\n",
        sum(&|j| format!("    t = (t + M{last}.f{j}({j})) % 1000003"))
    )
}
