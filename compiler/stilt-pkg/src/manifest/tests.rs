use stilt_syntax::capability::Capability;

use super::{Fill, Source, read, with_edition};

/// Each E0600 of a manifest, as the text it is at.
fn problems(text: &str) -> Vec<String> {
    read(text.as_bytes())
        .problems
        .iter()
        .map(|d| {
            let r = d.range;
            let at = &text[usize::from(r.start())..usize::from(r.end())];
            format!("{}:{at}", d.code)
        })
        .collect()
}

#[test]
fn reads_a_name_and_entries() {
    let text = "[package]\nname = \"app\"\n\n[dependencies]\ncsv = { path = \"deps/csv\", may = [\"io\"] }\n\n[dependencies.json]\nfrom = \"github.com/someone/stilt-json\"\nversion = \"1.4.0\"\n";
    let m = read(text.as_bytes());
    assert_eq!(m.problems, []);
    assert_eq!(m.name.as_deref(), Some("app"));
    assert!(m.declares);
    assert_eq!(
        m.entries[0].source,
        Some(Source::Path("deps/csv".to_owned()))
    );
    assert!(m.entries[0].may.io);
    let json = &m.entries[1];
    assert_eq!(
        &text[usize::from(json.key.start())..usize::from(json.key.end())],
        "json"
    );
    let Some(Source::From { version, hash, .. }) = &json.source else {
        panic!("json comes from a repository");
    };
    assert_eq!(version.as_ref().map(|v| v.value.as_str()), Some("1.4.0"));
    assert_eq!(*hash, None);
    assert!(matches!(json.fill, Fill::Lines(_, ref prefix) if prefix.is_empty()));
}

#[test]
fn an_empty_file_is_a_manifest() {
    let m = read(b"");
    assert!(m.declares && m.name.is_none() && m.problems.is_empty());
}

#[test]
fn reports_keys_values_and_combinations() {
    let text = r#"edition = "2024"
[package]
name = "Json"
version = "1.0.0"
[dependencies]
a = "deps/a"
b = { path = ["deps"] }
c = { path = "deps/c", features = [] }
d = { path = "deps/d", from = "github.com/x/d" }
e = { may = ["io"] }
f = { from = "github.com/x/f", version = "1.04.0" }
g = { path = "deps/g", may = ["files", "io", "io"] }
h = { from = "github.com/x/h", hash = "b3:00" }
"#;
    assert_eq!(
        problems(text),
        [
            "E0600:edition",
            "E0600:\"Json\"",
            "E0600:version",
            "E0600:\"deps/a\"",
            "E0600:[\"deps\"]",
            "E0600:features",
            "E0600:d",
            "E0600:e",
            "E0600:\"1.04.0\"",
            "E0600:\"files\"",
            "E0600:\"io\"",
            "E0600:\"b3:00\"",
        ]
    );
    let m = read(text.as_bytes());
    assert!(m.entries.iter().all(|e| e.source.is_none()));
}

#[test]
fn grants_capabilities_or_io() {
    // facts.capability-grants: `io`, or capabilities, each once, and `io` never with one.
    let text = r#"[dependencies]
a = { path = "deps/a", may = ["console", "fs"] }
b = { path = "deps/b", may = ["io"] }
c = { path = "deps/c", may = ["fs", "fs"] }
d = { path = "deps/d", may = ["io", "fs"] }
e = { path = "deps/e", may = ["net", "io"] }
"#;
    assert_eq!(
        problems(text),
        ["E0600:\"fs\"", "E0600:\"fs\"", "E0600:\"io\""]
    );
    let m = read(text.as_bytes());
    let a = m.entries[0].may;
    let granted: Vec<Capability> = a.capabilities.iter().collect();
    assert_eq!(granted, [Capability::Fs, Capability::Console]);
    assert!(!a.io && m.entries[1].may.io && m.entries[1].may.capabilities.is_empty());
}

#[test]
fn a_file_that_isnt_toml_declares_nothing() {
    let m = read(b"[dependencies]\njson = { path = \"deps/json\" # no\n");
    assert!(!m.declares && m.entries.is_empty());
    assert_eq!(m.problems.len(), 1);
    assert_eq!(u32::from(m.problems[0].range.start()), 43);
}

#[test]
fn dependencies_that_arent_a_table_declare_nothing() {
    let m = read(b"dependencies = 3\n");
    assert!(!m.declares);
    assert_eq!(m.problems.len(), 1);
}

#[test]
fn reads_an_edition() {
    let m = read(b"[package]\nname = \"app\"\nedition = \"2027\"\n");
    assert_eq!(m.problems, []);
    assert_eq!(m.edition, Some("2027"));
    assert_eq!(read(b"[package]\nname = \"app\"\n").edition, None);
    let unknown = "[package]\nedition = \"2026\"\n";
    assert_eq!(problems(unknown), ["E0600:\"2026\""]);
    let message = &read(unknown.as_bytes()).problems[0].message;
    assert_eq!(
        message,
        "this manifest's edition is `2026`, and the editions are 2027"
    );
    assert_eq!(problems("[package]\nedition = 2027\n"), ["E0600:2027"]);
}

#[test]
fn writes_an_edition_where_it_belongs() {
    let written = |text: &str| String::from_utf8(with_edition(text.as_bytes(), "2028")).unwrap();
    let replaced = "[package]\nname = \"app\"\nedition = \"2027\"\n";
    assert_eq!(
        written(replaced),
        "[package]\nname = \"app\"\nedition = \"2028\"\n"
    );
    let named = "[package]\nname = \"app\"\n\n[dependencies]\n";
    let after_name = "[package]\nname = \"app\"\nedition = \"2028\"\n\n[dependencies]\n";
    assert_eq!(written(named), after_name);
    assert_eq!(written("[package]\n"), "[package]\nedition = \"2028\"\n");
    assert_eq!(written(""), "[package]\nedition = \"2028\"\n\n");
}
