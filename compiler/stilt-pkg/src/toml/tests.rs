use super::{Defined, ValueKind, parse};

/// Where `text` stops being TOML, as `line:col`, or `ok`.
fn verdict(text: &str) -> String {
    match parse(text.as_bytes()) {
        Ok(_) => "ok".to_owned(),
        Err(e) => {
            let before = &text[..e.at];
            let line = before.matches('\n').count() + 1;
            let col = before.rsplit('\n').next().unwrap_or("").chars().count() + 1;
            format!("{line}:{col}")
        }
    }
}

#[test]
fn reads_the_forms_of_toml() {
    let text = r#"
# a comment
title = "TOML" # after a value
"quoted key" = 'literal'
dotted.key = 1_000
hex = 0xDEAD_beef
float = -1.5e+3
special = [inf, -nan, +inf]
date = 1979-05-27T07:32:00.999-07:00
local = 1979-05-27 07:32:00
day = 1979-05-27
time = 07:32:00
multi = """
one \
  two"""
lit = '''it's'''
quotes = """a""""
array = [
  1, # one
  "two",
]
inline = { a = 1, b.c = true }

[table.sub]
x = false

[[fruits]]
name = "apple"

[[fruits]]
name = "pear"

[table]
y = 2
"#;
    let root = parse(text.as_bytes()).expect("valid TOML");
    let multi = root.get("multi").unwrap();
    assert_eq!(multi.kind, ValueKind::String("one two".to_owned()));
    assert_eq!(
        root.get("quotes").unwrap().kind,
        ValueKind::String("a\"".to_owned())
    );
    let Some(ValueKind::Tables(fruits)) = root.get("fruits").map(|v| &v.kind) else {
        panic!("fruits is an array of tables");
    };
    assert_eq!(fruits.len(), 2);
    let Some(ValueKind::Table(table)) = root.get("table").map(|v| &v.kind) else {
        panic!("table is a table");
    };
    assert_eq!(table.defined, Defined::Header);
    assert!(table.get("sub").is_some() && table.get("y").is_some());
}

#[test]
fn places_syntax_errors_where_no_document_can_continue() {
    for (text, at) in [
        ("this is [not toml", "1:6"),
        (
            "[dependencies]\njson = { path = \"deps/json\" # no\n",
            "2:29",
        ),
        ("a = \"open\n", "1:10"),
        ("a = \"\\q\"", "1:7"),
        ("a = 01", "1:6"),
        ("a = 1__2", "1:7"),
        ("a = 1.", "1:7"),
        ("a = { b = 1, }", "1:14"),
        ("a = { b = 1,\n c = 2 }", "1:13"),
        ("a = tru", "1:8"),
        ("a = yes", "1:5"),
        ("[a", "1:3"),
        ("a = 1979-13-01", "1:10"),
        ("a = \"\"\"x\"\"\"\"\"\"", "1:14"),
        ("a = 1\r", "1:6"),
        ("a = 1 2", "1:7"),
    ] {
        assert_eq!(verdict(text), at, "{text:?}");
    }
}

#[test]
fn places_redefinitions_at_their_keys() {
    for (text, at) in [
        ("a = 1\na = 2", "2:1"),
        ("[a]\n[a]", "2:2"),
        ("[a]\nb.c = 1\n[a.b]", "3:2"),
        ("[a.b]\nc = 1\n[a]\nb.d = 2", "4:1"),
        ("a = { b = 1 }\n[a]", "2:2"),
        ("a = [1]\n[[a]]", "2:3"),
        ("a = { b = 1, b = 2 }", "1:14"),
    ] {
        assert_eq!(verdict(text), at, "{text:?}");
    }
    assert_eq!(verdict("[a.b.c]\n[a]\nb.d = 1"), "ok");
    assert_eq!(verdict("a.b = 1\n[a.c]"), "ok");
}

#[test]
fn keeps_where_values_end() {
    let text = "[dependencies]\njson = { from = \"x\" }\n";
    let root = parse(text.as_bytes()).unwrap();
    let Some(ValueKind::Table(deps)) = root.get("dependencies").map(|v| &v.kind) else {
        panic!("a table");
    };
    let json = deps.get("json").unwrap();
    assert_eq!(&text[json.at..json.end], "{ from = \"x\" }");
    let ValueKind::Table(entry) = &json.kind else {
        panic!("an inline table");
    };
    assert_eq!(&text[..entry.end], "[dependencies]\njson = { from = \"x\"");
}
