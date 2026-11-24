//! Every native of the standard library that performs nothing has an entry that runs it, so that no
//! macro's run stops where the reference interpreter's goes on (macros.procedural-bodies and
//! macros.running).

use std::path::Path;

use stilt_hir::hir::{Item, Name};
use stilt_types::tast::Callee;

/// A native item of a module of the standard library, as its source declares it.
#[derive(Debug)]
struct Declared {
    module: String,
    owner: Option<String>,
    name: String,
    constant: bool,
    io: bool,
}

/// The type an `impl` line opens the block of.
fn impl_owner(line: &str) -> Option<String> {
    let rest = line.strip_prefix("impl")?;
    let rest = match rest.strip_prefix('<') {
        Some(generics) => {
            let mut depth = 1;
            let end = generics.char_indices().find_map(|(i, c)| {
                match c {
                    '<' => depth += 1,
                    '>' => depth -= 1,
                    _ => {}
                }
                (depth == 0).then_some(i)
            })?;
            &generics[end + 1..]
        }
        None => rest,
    };
    let rest = rest.trim_start();
    let end = rest
        .find(|c: char| !c.is_alphanumeric() && c != '_')
        .unwrap_or(rest.len());
    (!rest.contains(" for ")).then(|| rest[..end].to_owned())
}

/// Whether a native function's own row, after its parameters, names `io`.
fn performs_io(signature: &str) -> bool {
    let Some(open) = signature.find('(') else {
        return false;
    };
    let mut depth = 0;
    let close = signature[open..].char_indices().find_map(|(i, c)| {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            _ => {}
        }
        (depth == 0).then_some(open + i)
    });
    let rest = close.map_or("", |c| &signature[c + 1..]);
    let row = rest.split_once(" / ").map_or("", |(_, row)| row);
    row.split(|c: char| !c.is_alphanumeric() && c != '_')
        .any(|word| word == "io")
}

/// The native items of the file `text` of the module `module`.
fn declared(module: &str, text: &str) -> Vec<Declared> {
    let mut out = Vec::new();
    let mut owner = None;
    for line in text.lines() {
        if line.starts_with("impl") {
            owner = impl_owner(line);
        } else if line.starts_with('}') {
            owner = None;
        }
        let Some(head) = line.trim().strip_suffix("= ?") else {
            continue;
        };
        let head = head.trim_start_matches("pub ");
        let (constant, rest) = if let Some(rest) = head.strip_prefix("fn ") {
            (false, rest)
        } else if let Some(rest) = head.strip_prefix("const ") {
            (true, rest)
        } else {
            continue;
        };
        let end = rest
            .find(|c: char| !c.is_alphanumeric() && c != '_')
            .unwrap_or(rest.len());
        out.push(Declared {
            module: module.to_owned(),
            owner: owner.clone(),
            name: rest[..end].to_owned(),
            constant,
            io: !constant && performs_io(rest),
        });
    }
    out
}

/// Every native function and constant of the standard library.
fn natives() -> Vec<Declared> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std");
    let mut files: Vec<_> = std::fs::read_dir(&dir)
        .expect("the standard library's sources")
        .map(|e| e.expect("an entry of the standard library").path())
        .filter(|p| p.extension().is_some_and(|x| x == "lt"))
        .collect();
    files.sort();
    let mut out = Vec::new();
    for path in files {
        let stem = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or_default();
        let text = std::fs::read_to_string(&path).expect("a source of the standard library");
        out.extend(declared(&format!("std.{stem}"), &text));
    }
    out
}

/// Whether the evaluation of calls runs the native: `into`, `part` and `split` of `std.view`.
fn takes_a_place(module: &str, name: &str) -> bool {
    let item = Item {
        home: Name::from(module),
        name: Name::from(name),
    };
    crate::eval::windows::window_native(&Callee::Function(item)).is_some()
}

#[test]
fn every_native_that_performs_nothing_has_an_entry() {
    let natives = natives();
    assert!(natives.len() > 500, "found only {} natives", natives.len());
    let mut missing = Vec::new();
    for n in natives.iter().filter(|n| !n.io) {
        let found = if n.constant {
            n.owner
                .as_deref()
                .is_some_and(|o| super::has_constant(o, &n.name))
        } else {
            super::native(&n.module, n.owner.as_deref(), &n.name).is_some()
                || (n.owner.is_none() && takes_a_place(&n.module, &n.name))
        };
        if !found {
            missing.push(format!(
                "{}.{}{}",
                n.module,
                n.owner
                    .as_deref()
                    .map_or(String::new(), |o| format!("{o}.")),
                n.name
            ));
        }
    }
    assert!(missing.is_empty(), "natives without an entry: {missing:?}");
}

#[test]
fn no_native_that_performs_io_has_an_entry() {
    let io: Vec<_> = natives().into_iter().filter(|n| n.io).collect();
    assert!(io.iter().any(|n| n.name == "print"));
    for n in io {
        assert!(
            super::native(&n.module, n.owner.as_deref(), &n.name).is_none(),
            "{n:?} performs io, which no macro's run reaches (macros.procedural-bodies)"
        );
    }
}
