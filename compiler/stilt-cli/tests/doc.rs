//! `stilt doc` (docs.stilt-doc, docs.module-pages, docs.markdown and docs.std): a package's
//! pages, written or printed as JSON, what they hold and leave out, its Markdown, the programs it
//! refuses, and the standard library's pages.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use serde_json::Value;

/// An empty directory of its own for the test `name`.
fn place(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stilt-doc-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("the directory");
    dir
}

fn stilt(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(args)
        .current_dir(dir)
        .output()
        .expect("stilt runs")
}

fn text(out: &[u8]) -> String {
    String::from_utf8_lossy(out).into_owned()
}

const SHAPES: &str = r#"// shapes: points, and a trait for things with an area.
//
// Each figure is a record.

/// A point of the plane.
pub type Point = { x: f64, y: f64 }

impl Point {
  /// How far the point is from `other`, as a **straight** line.
  /// ex: Point { x: 0.0, y: 0.0 }.distance(Point { x: 3.0, y: 4.0 }) == 5.0
  pub fn distance(self, other: Point) -> f64 {
    let (dx, dy) = (self.x - other.x, self.y - other.y)
    (dx * dx + dy * dy).sqrt()
  }

  fn secret(self) -> f64 { self.x }
}

impl Show for Point {
  fn show(self) -> str { "({self.x}, {self.y})" }
}

/// Something with an area.
pub trait Area {
  fn area(self) -> f64

  /// Whether the area is at least `limit`.
  fn at_least(self, limit: f64) -> bool { self.area() >= limit }
}

/// The most elements `first` reads.
pub const LIMIT: i64 = 10

/// The first element of `xs`, which `<b>` doesn't need, or 0.
/// - It reads one element.
pub fn first(xs: List<i64>) -> i64 { xs.get(0) else 0 }

/// The sum of `a` and `b`.
pub fn add(a: i64, b: i64) -> i64 { a + b }

fn hidden() -> i64 { 1 }

test "first" { assert first([4]) == 4 }
"#;

/// The package `shapes`, with its manifest.
fn shapes(name: &str) -> PathBuf {
    let dir = place(name);
    std::fs::create_dir_all(dir.join("src")).expect("src");
    let manifest = "[package]\nname = \"shapes\"\nedition = \"2027\"\n";
    std::fs::write(dir.join("stilt.toml"), manifest).expect("the manifest");
    std::fs::write(dir.join("src/main.lt"), SHAPES).expect("the module");
    std::fs::write(
        dir.join("src/extra.lt"),
        "// More.\n\npub fn one() -> i64 { 1 }\n",
    )
    .expect("a second module");
    dir
}

#[test]
fn a_package_s_pages_are_written_into_doc_or_where_o_says() {
    let dir = shapes("written");
    let out = stilt(&dir, &["doc"]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    assert!(
        text(&out.stdout).trim_end().ends_with("index.html"),
        "{}",
        text(&out.stdout)
    );
    for page in [
        "index.html",
        "shapes.html",
        "shapes.extra.html",
        "style.css",
    ] {
        assert!(dir.join("doc").join(page).is_file(), "{page}");
    }
    let index = std::fs::read_to_string(dir.join("doc/index.html")).expect("the index");
    assert!(index.contains("href=\"shapes.extra.html\""), "{index}");
    assert!(
        index.contains("points, and a trait for things with an area."),
        "{index}"
    );
    let out = stilt(&dir, &["doc", "-o", "pages", "."]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    assert!(dir.join("pages/shapes.html").is_file());
}

#[test]
fn the_json_holds_the_pub_declarations_with_their_facts_docs_and_members() {
    let dir = shapes("json");
    let out = stilt(&dir, &["doc", "--json"]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    let pages: Value = serde_json::from_slice(&out.stdout).expect("JSON");
    assert_eq!(pages["package"], "shapes");
    let main = &pages["modules"][0];
    assert_eq!(main["address"], "shapes");
    assert_eq!(main["tier"], "core");
    assert_eq!(
        main["description"],
        "shapes: points, and a trait for things with an area.\n\nEach figure is a record."
    );
    let names: Vec<&str> = (main["items"].as_array().expect("items").iter())
        .map(|i| i["name"].as_str().expect("a name"))
        .collect();
    assert_eq!(names, ["Point", "Area", "LIMIT", "first", "add"]);
    let point = &main["items"][0];
    assert_eq!(point["signature"], "pub type Point = { x: f64, y: f64 }");
    assert_eq!(point["facts"], Value::Null);
    let members: Vec<(&str, &str)> = (point["members"].as_array().expect("members").iter())
        .map(|m| {
            (
                m["kind"].as_str().unwrap_or(""),
                m["signature"].as_str().unwrap_or(""),
            )
        })
        .collect();
    assert_eq!(
        members,
        [
            ("fn", "pub fn distance(self, other: Point) -> f64"),
            ("impl", "impl Show for Point")
        ]
    );
    let distance = &point["members"][0];
    assert_eq!(distance["facts"], serde_json::json!([]));
    assert_eq!(
        distance["examples"],
        serde_json::json!(["Point { x: 0.0, y: 0.0 }.distance(Point { x: 3.0, y: 4.0 }) == 5.0"])
    );
    let area = &main["items"][1];
    assert_eq!(area["members"][0]["facts"], Value::Null, "no default body");
    assert_eq!(area["members"][1]["facts"], serde_json::json!([]));
    assert_eq!(main["items"][2]["signature"], "pub const LIMIT: i64");
    assert_eq!(main["items"][4]["facts"], serde_json::json!(["overflow"]));
    assert_eq!(pages["modules"][1]["address"], "shapes.extra");
}

#[test]
fn docs_are_rendered_as_markdown_and_escaped() {
    let dir = shapes("markdown");
    assert!(stilt(&dir, &["doc"]).status.success());
    let page = std::fs::read_to_string(dir.join("doc/shapes.html")).expect("the page");
    assert!(
        page.contains("as a <strong>straight</strong> line."),
        "{page}"
    );
    assert!(
        page.contains("which <code>&lt;b&gt;</code> doesn"),
        "{page}"
    );
    assert!(page.contains("<li>It reads one element.</li>"), "{page}");
    assert!(
        page.contains("<span class=\"fact\">overflow</span>"),
        "{page}"
    );
    assert!(
        !page.contains("hidden") && !page.contains("secret"),
        "{page}"
    );
}

#[test]
fn a_program_with_an_error_is_refused_and_nothing_is_written() {
    let dir = place("refused");
    std::fs::write(
        dir.join("main.lt"),
        "pub fn f() -> i64 { missing }\n\nfn main() {}\n",
    )
    .expect("the program");
    let out = stilt(&dir, &["doc"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(
        text(&out.stderr).contains("E0211 at main.lt:1:21"),
        "{}",
        text(&out.stderr)
    );
    assert!(!dir.join("doc").exists());
}

#[test]
fn a_program_without_a_manifest_is_named_by_its_directory() {
    let dir = place("unnamed").join("tally");
    std::fs::create_dir_all(&dir).expect("the program's directory");
    std::fs::write(
        dir.join("main.lt"),
        "/// One.\npub fn one() -> i64 { 1 }\n\nfn main() {}\n",
    )
    .expect("the program");
    let out = stilt(&dir, &["doc", "--json"]);
    let pages: Value = serde_json::from_slice(&out.stdout).expect("JSON");
    assert_eq!(pages["package"], "tally");
    assert_eq!(pages["modules"][0]["address"], "tally");
}

/// The item named `name` of a module's or an item's JSON.
fn named<'a>(items: &'a Value, name: &str) -> &'a Value {
    (items.as_array().expect("items").iter())
        .find(|i| i["name"] == name)
        .unwrap_or_else(|| panic!("no item `{name}`"))
}

#[test]
fn the_standard_library_is_documented_with_its_examples_and_its_natives_facts() {
    let dir = place("std");
    let out = stilt(&dir, &["doc", "--std", "--json"]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    let pages: Value = serde_json::from_slice(&out.stdout).expect("JSON");
    assert_eq!(pages["package"], "std");
    let module = |address: &str| {
        (pages["modules"].as_array().expect("modules").iter())
            .find(|m| m["address"] == address)
            .unwrap_or_else(|| panic!("no module `{address}`"))
    };
    let fs = &module("std.fs")["items"];
    // facts.native-allocation and facts.capability-natives: a native of `std.fs` whose result
    // names `str` allocates and reaches files.
    assert_eq!(
        named(fs, "read")["facts"],
        serde_json::json!(["alloc", "fs"])
    );
    // std.examples: the library's examples are on its pages.
    let join = named(fs, "join");
    assert_eq!(join["facts"], serde_json::json!(["alloc"]));
    assert_ne!(join["examples"], serde_json::json!([]));
    // facts.native-allocation: `print` isn't among the natives that allocate nothing.
    let prelude = &module("std.prelude")["items"];
    assert_eq!(
        named(prelude, "print")["facts"],
        serde_json::json!(["alloc", "console"])
    );
    // docs.std: the built-in types follow the declarations, in the order of their first impl.
    let names: Vec<&str> = (prelude.as_array().expect("items").iter())
        .map(|i| i["name"].as_str().expect("a name"))
        .collect();
    let built_in = [
        "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "f32", "f64", "str", "List", "Map",
    ];
    assert!(names.ends_with(&built_in), "{names:?}");
    let list = named(prelude, "List");
    assert_eq!(list["kind"], "type");
    assert_eq!(list["signature"], "List<T>");
    assert_eq!(list["doc"], "");
    let push = named(&list["members"], "push");
    assert_eq!(push["signature"], "pub fn push(inout self, x: T)");
    assert_eq!(push["facts"], serde_json::json!(["alloc"]));
    let out = stilt(&dir, &["doc", "--std", "-o", "pages"]);
    assert!(out.status.success(), "{}", text(&out.stderr));
    for page in ["index.html", "std.prelude.html", "std.fs.html", "style.css"] {
        assert!(dir.join("pages").join(page).is_file(), "{page}");
    }
    let page = std::fs::read_to_string(dir.join("pages/std.prelude.html")).expect("the page");
    assert!(page.contains("id=\"List.push\""), "{page}");
}
