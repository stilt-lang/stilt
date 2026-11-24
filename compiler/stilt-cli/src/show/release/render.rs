//! The performance report as text for people, one function after another with a blank line
//! between two, and as JSON records, one per function and line (builds.performance-report).
//!
//! ```text
//! fn totals<K: Hash + Eq>(rows: List<Row>, key: fn(Row) -> K) -> Map<K, f64>
//!   compiled for: K = str, K = i64
//!   references: 4 operations (lines 12 and 15), 2 copies (line 15)
//!   checks: 3 proved and dropped (bounds, lines 9 and 10; overflow, line 11), 1 kept (missing-key, line 14)
//! ```

use std::fmt::Write as _;

use serde_json::{Value, json};

use super::costs::Check;
use super::{Compiled, Entry};

/// The entries as text.
pub(super) fn text(entries: &[Entry]) -> String {
    let mut out = String::new();
    for e in entries {
        if !out.is_empty() {
            out.push('\n');
        }
        let _ = writeln!(out, "{}", e.header);
        let _ = writeln!(out, "  {}", compiled(&e.compiled));
        if !e.dictionaries.is_empty() {
            let calls: Vec<String> = (e.dictionaries.iter())
                .map(|(line, reason)| format!("line {line}, {reason}"))
                .collect();
            let _ = writeln!(out, "  dictionaries: {}", calls.join("; "));
        }
        let _ = writeln!(out, "  references: {}", references(&e.costs.references));
        let _ = writeln!(out, "  checks: {}", checks(&e.costs.proved, &e.costs.kept));
        if !e.dropped.is_empty() {
            let n = e.dropped.len();
            let s = if n == 1 { "" } else { "s" };
            let _ = writeln!(
                out,
                "  profile: {n} line{s} dropped, as the body changed since"
            );
            for line in &e.dropped {
                let _ = writeln!(out, "    {}", line.text());
            }
        }
    }
    out
}

fn compiled(c: &Compiled) -> String {
    match c {
        Compiled::Unreached => "no instantiation: no root reaches it".to_owned(),
        Compiled::Once => "compiled once".to_owned(),
        Compiled::For(lists) => format!("compiled for: {}", instantiations(lists)),
        Compiled::Kept(lists) if lists.is_empty() => "compiled once with dictionaries".to_owned(),
        Compiled::Kept(lists) => {
            format!(
                "compiled once with dictionaries, called at: {}",
                instantiations(lists)
            )
        }
    }
}

/// Lists of arguments, as in `K = str, K = i64`, each in parentheses when it has several.
fn instantiations(lists: &[Vec<(String, String)>]) -> String {
    let one = |args: &Vec<(String, String)>| {
        let pairs: Vec<String> = args.iter().map(|(n, t)| format!("{n} = {t}")).collect();
        match pairs.as_slice() {
            [single] => single.clone(),
            _ => format!("({})", pairs.join(", ")),
        }
    };
    lists.iter().map(one).collect::<Vec<_>>().join(", ")
}

/// The reference-count operations, by their lines, and the copies among them.
fn references(ops: &[(u32, bool)]) -> String {
    if ops.is_empty() {
        return "none".to_owned();
    }
    let all: Vec<u32> = ops.iter().map(|(l, _)| *l).collect();
    let copies: Vec<u32> = ops.iter().filter(|(_, c)| *c).map(|(l, _)| *l).collect();
    let n = ops.len();
    let mut out = format!("{n} operation{} ({})", plural(n), lines(&all));
    match copies.len() {
        0 => out.push_str(", no copy"),
        m => {
            let _ = write!(
                out,
                ", {m} cop{} ({})",
                if m == 1 { "y" } else { "ies" },
                lines(&copies)
            );
        }
    }
    out
}

/// The checks proved and dropped and those kept, each by kind and lines.
fn checks(proved: &[Check], kept: &[Check]) -> String {
    let mut parts = Vec::new();
    if !proved.is_empty() {
        parts.push(format!(
            "{} proved and dropped ({})",
            proved.len(),
            by_kind(proved)
        ));
    }
    if !kept.is_empty() {
        parts.push(format!("{} kept ({})", kept.len(), by_kind(kept)));
    }
    if parts.is_empty() {
        return "none".to_owned();
    }
    parts.join(", ")
}

/// Checks by kind, each kind in the order of its first line, as in `bounds, lines 9 and 10;
/// overflow, line 11`.
fn by_kind(checks: &[Check]) -> String {
    let mut kinds: Vec<&str> = Vec::new();
    for (kind, _) in checks {
        if !kinds.contains(kind) {
            kinds.push(kind);
        }
    }
    let each = |kind: &str| {
        let at: Vec<u32> = checks
            .iter()
            .filter(|(k, _)| *k == kind)
            .map(|(_, l)| *l)
            .collect();
        format!("{kind}, {}", lines(&at))
    };
    kinds.into_iter().map(each).collect::<Vec<_>>().join("; ")
}

/// Lines, each once and in order, as in `line 9`, `lines 9 and 10` or `lines 9, 10 and 12`.
fn lines(at: &[u32]) -> String {
    let mut at = at.to_vec();
    at.sort_unstable();
    at.dedup();
    let shown: Vec<String> = at.iter().map(u32::to_string).collect();
    match shown.as_slice() {
        [] => String::new(),
        [one] => format!("line {one}"),
        [init @ .., last] => format!("lines {} and {last}", init.join(", ")),
    }
}

fn plural(n: usize) -> &'static str {
    if n == 1 { "" } else { "s" }
}

/// The entries as JSON records, one per line.
pub(super) fn json(entries: &[Entry]) -> String {
    let mut out = String::new();
    for e in entries {
        let _ = writeln!(out, "{}", record(e));
    }
    out
}

fn record(e: &Entry) -> Value {
    let (reached, kept, lists) = match &e.compiled {
        Compiled::Unreached => (false, false, &[][..]),
        Compiled::Once => (true, false, &[][..]),
        Compiled::For(lists) => (true, false, lists.as_slice()),
        Compiled::Kept(lists) => (true, true, lists.as_slice()),
    };
    let instantiations: Vec<Value> = (lists.iter())
        .map(|args| {
            let pairs = args
                .iter()
                .map(|(n, t)| json!({ "parameter": n, "argument": t }));
            Value::Array(pairs.collect())
        })
        .collect();
    let mut by_line: Vec<(u32, usize, usize)> = Vec::new();
    for &(line, copy) in &e.costs.references {
        match by_line.last_mut() {
            Some((l, n, c)) if *l == line => (*n, *c) = (*n + 1, *c + usize::from(copy)),
            _ => by_line.push((line, 1, usize::from(copy))),
        }
    }
    let check = |cs: &[Check]| -> Vec<Value> {
        cs.iter()
            .map(|(kind, line)| json!({ "kind": kind, "line": line }))
            .collect()
    };
    json!({
        "at": e.at,
        "body": e.body,
        "file": e.file,
        "line": e.line,
        "header": e.header,
        "reached": reached,
        "dictionaries": kept,
        "instantiations": instantiations,
        "calls": e.dictionaries.iter().map(|(line, reason)| json!({ "line": line, "reason": reason })).collect::<Vec<_>>(),
        "references": by_line.iter().map(|(line, n, c)| json!({ "line": line, "operations": n, "copies": c })).collect::<Vec<_>>(),
        "checks": { "proved": check(&e.costs.proved), "kept": check(&e.costs.kept) },
        "dropped": e.dropped.iter().map(crate::profile::Line::text).collect::<Vec<_>>(),
    })
}
