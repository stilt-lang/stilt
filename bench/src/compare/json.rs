//! The results as JSON, for other programs to read: the machine, the toolchains, and each
//! version's runs.

use std::fmt::Write;

use super::sample::Runs;
use super::{Outcome, Results, Row};

/// A JSON value.
#[derive(Debug)]
enum Value {
    Null,
    Number(f64),
    Count(u64),
    Text(String),
    List(Vec<Value>),
    Object(Vec<(&'static str, Value)>),
}

fn text(s: &str) -> Value {
    Value::Text(s.to_owned())
}

/// The results, as a JSON document.
pub(crate) fn results(r: &Results) -> String {
    let m = &r.machine;
    let toolchains = r.toolchains.iter().map(|t| {
        Value::Object(vec![
            ("language", text(t.language.name())),
            ("version", text(&t.version)),
            ("build", text(&t.build_line())),
            ("run", t.run_line().map_or(Value::Null, Value::Text)),
        ])
    });
    let missing = r.missing.iter().map(|(language, why)| {
        Value::Object(vec![
            ("language", text(language.name())),
            ("reason", text(why.trim())),
        ])
    });
    let suites = r.suites.iter().map(|(suite, rows)| {
        Value::Object(vec![
            ("suite", text(suite.key)),
            ("title", text(suite.title)),
            ("programs", Value::List(rows.iter().map(row).collect())),
        ])
    });
    let document = Value::Object(vec![
        ("date", text(&r.date)),
        (
            "machine",
            Value::Object(vec![
                ("processor", text(&m.processor)),
                ("cores", text(&m.cores)),
                ("memory", Value::Count(m.memory)),
                ("system", text(&m.system)),
            ]),
        ),
        ("load_before", text(&r.load.0)),
        ("load_after", text(&r.load.1)),
        ("least_runs", Value::Count(r.runs as u64)),
        ("least_seconds", Value::Number(r.seconds)),
        ("toolchains", Value::List(toolchains.collect())),
        ("missing", Value::List(missing.collect())),
        ("suites", Value::List(suites.collect())),
    ]);
    let mut out = String::new();
    write(&document, 0, &mut out);
    out.push('\n');
    out
}

fn row(row: &Row) -> Value {
    let results = row.results.iter().map(|(language, outcome)| {
        let mut fields = vec![("language", text(language.name()))];
        match outcome {
            Outcome::Measured(runs) => fields.extend(measured(runs)),
            Outcome::Failed(status, error) => {
                fields.push(("status", Value::Number(f64::from(*status))));
                fields.push(("error", text(error)));
            }
            Outcome::Wrong => fields.push(("error", text("prints something else"))),
        }
        Value::Object(fields)
    });
    Value::Object(vec![
        ("program", text(&row.program)),
        ("results", Value::List(results.collect())),
    ])
}

/// A measured version's fields: its time and spread, each run's time, in seconds, its
/// instructions and its peak memory, in bytes.
fn measured(runs: &Runs) -> Vec<(&'static str, Value)> {
    vec![
        ("time", Value::Number(runs.time().as_secs_f64())),
        ("spread", Value::Number(runs.spread())),
        (
            "times",
            Value::List(runs.times().into_iter().map(Value::Number).collect()),
        ),
        (
            "instructions",
            runs.instructions().map_or(Value::Null, Value::Count),
        ),
        ("peak", Value::Count(runs.peak())),
    ]
}

fn write(value: &Value, indent: usize, out: &mut String) {
    let pad = |n: usize| "  ".repeat(n);
    match value {
        Value::Number(n) if n.is_finite() => {
            let _ = write!(out, "{n}");
        }
        Value::Null | Value::Number(_) => out.push_str("null"),
        Value::Count(n) => {
            let _ = write!(out, "{n}");
        }
        Value::Text(s) => quote(s, out),
        Value::List(items) if items.is_empty() => out.push_str("[]"),
        Value::List(items) => {
            out.push('[');
            for (i, item) in items.iter().enumerate() {
                out.push_str(if i == 0 { "\n" } else { ",\n" });
                out.push_str(&pad(indent + 1));
                write(item, indent + 1, out);
            }
            let _ = write!(out, "\n{}]", pad(indent));
        }
        Value::Object(fields) => {
            out.push('{');
            for (i, (key, item)) in fields.iter().enumerate() {
                out.push_str(if i == 0 { "\n" } else { ",\n" });
                out.push_str(&pad(indent + 1));
                quote(key, out);
                out.push_str(": ");
                write(item, indent + 1, out);
            }
            let _ = write!(out, "\n{}}}", pad(indent));
        }
    }
}

pub(crate) fn quote(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c if u32::from(c) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", u32::from(c));
            }
            c => out.push(c),
        }
    }
    out.push('"');
}
