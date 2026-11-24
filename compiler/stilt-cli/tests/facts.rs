//! The facts suite (goal shown-facts). Each program under `tests/facts/` marks, at the end of
//! each line that causes a fact of its function, the fact the Reference gives that line, and
//! `stilt show --json` must show exactly those facts at exactly those lines, with each
//! module's tier ([its README](../../../tests/facts/README.md)), the modes of modes.show among them
//! (modes.facts-suite), the sources of views (views.show), `div`, `copy` and in-place parameters
//! (facts.visibility), the capabilities below `io` (facts.visibility), the checks that verification
//! proves (facts.shown-proofs), at a type's first line, the fields and variants through which it
//! can form a cycle (cycles.can-form-cycle), and the `unsafe` blocks and the foreign functions each
//! function names (c.unsafe-and-foreign).

mod common;

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use common::suite;
use serde_json::Value;

/// A fact at a line of a file: `CONSUMES` and the parameter's name, `LOST-REUSE` and the
/// place's, `ESCAPES` and `SHARED` and the binding's, `ONCE` and the binding's for a bound
/// closure or a parameter, `ONCE` alone for an unbound closure, `VIEWS` and the source's
/// (views.show), `IN-PLACE` and the parameter's (facts.facts-suite), `REFLECTS` and the type
/// parameter's (meta.reflects), `PROVED` and what a proved check rules out, as `PROVED bounds`
/// (facts.shown-proofs), `CYCLE` and the field's or variant's (cycles.can-form-cycle), `PANIC`,
/// `OVERFLOW` (effects.overflow-effect), `ALLOC`, `DIV`, `COPY`, `LOCKS` (shared.locks), `ATOMIC`
/// (par.atomic-sites) or `UNSAFE`, `FOREIGN` and the foreign function's name
/// (c.unsafe-and-foreign), or a capability's, such as `FS` (facts.visibility).
type Fact = (String, u32, String);

/// The tier that a file's header expects, and the facts its lines expect.
fn expected(path: &Path, file: &str) -> Result<(Option<String>, BTreeSet<Fact>), String> {
    let text = fs::read_to_string(path).map_err(|e| format!("{file}: {e}"))?;
    let (mut tier, mut facts, mut header) = (None, BTreeSet::new(), true);
    for (n, line) in (1..).zip(text.lines()) {
        let code = line.trim_start();
        header = header && (code.is_empty() || code.starts_with("//"));
        let Some((before, annotation)) = line.split_once("//~") else {
            continue;
        };
        if header && before.trim().is_empty() {
            let value = annotation.trim().strip_prefix("tier:");
            tier = Some(
                value
                    .ok_or(format!("{file}:{n}: an unknown header key"))?
                    .trim()
                    .to_owned(),
            );
            continue;
        }
        let mut words = annotation.split_whitespace().peekable();
        while let Some(word) = words.next() {
            let fact = match word {
                "PANIC" | "OVERFLOW" | "ALLOC" | "DIV" | "COPY" | "LOCKS" | "ATOMIC" | "UNSAFE"
                | "FS" | "NET" | "CLOCK" | "ENV" | "CONSOLE" | "RAND" | "SPAWN" | "EXEC" => {
                    word.to_owned()
                }
                "CONSUMES" | "LOST-REUSE" | "ESCAPES" | "SHARED" | "VIEWS" | "WRITES"
                | "IN-PLACE" | "REFLECTS" | "CYCLE" | "FOREIGN" => {
                    format!("{word} {}", words.next().unwrap_or_default())
                }
                "PROVED" => match words.next() {
                    Some(kind @ ("bounds" | "divide-by-zero" | "missing-key")) => {
                        format!("PROVED {kind}")
                    }
                    other => {
                        return Err(format!(
                            "{file}:{n}: an unknown proof `{}`",
                            other.unwrap_or_default()
                        ));
                    }
                },
                // A binding's name, which no entry is, follows `ONCE` unless the closure is
                // unbound (modes.facts-suite).
                "ONCE" => match words.next_if(|w| w.starts_with(|c: char| !c.is_ascii_uppercase()))
                {
                    Some(name) => format!("ONCE {name}"),
                    None => "ONCE".to_owned(),
                },
                _ => return Err(format!("{file}:{n}: an unknown entry `{word}`")),
            };
            facts.insert((file.to_owned(), n, fact));
        }
    }
    Ok((tier, facts))
}

/// The tier and the facts that `stilt show --json` gives a module of the program.
fn shown(program: &Path, module: &str) -> Result<(String, BTreeSet<Fact>), String> {
    let record = suite::show_module(program, module)?;
    let mut facts = BTreeSet::new();
    for f in record["functions"].as_array().into_iter().flatten() {
        let file = f["file"].as_str().unwrap_or_default().to_owned();
        let line = |c: &Value| u32::try_from(c["line"].as_u64().unwrap_or(0)).unwrap_or(0);
        for (key, name, fact) in [
            ("consumes", "param", "CONSUMES"),
            ("lost_reuse", "place", "LOST-REUSE"),
            ("escapes", "name", "ESCAPES"),
            ("shared", "name", "SHARED"),
            ("once", "name", "ONCE"),
            ("views", "name", "VIEWS"),
            ("writes", "name", "WRITES"),
            ("in_place", "param", "IN-PLACE"),
            ("foreign", "name", "FOREIGN"),
        ] {
            for c in f[key].as_array().into_iter().flatten() {
                let shown = match c[name].as_str() {
                    Some(name) => format!("{fact} {name}"),
                    None => fact.to_owned(),
                };
                facts.insert((file.clone(), line(c), shown));
            }
        }
        for (key, fact) in [
            ("panic", "PANIC"),
            ("overflow", "OVERFLOW"),
            ("alloc", "ALLOC"),
            ("div", "DIV"),
            ("copy", "COPY"),
            ("locks", "LOCKS"),
            ("atomic", "ATOMIC"),
            ("unsafe", "UNSAFE"),
        ] {
            for c in f[key].as_array().into_iter().flatten() {
                facts.insert((file.clone(), line(c), fact.to_owned()));
            }
        }
        // A check that verification proves, at its line (facts.shown-proofs).
        for c in f["proved"].as_array().into_iter().flatten() {
            let shown = format!("PROVED {}", c["proved"].as_str().unwrap_or_default());
            facts.insert((file.clone(), line(c), shown));
        }
        // A type parameter it reflects on, at its signature (meta.reflects).
        for t in f["reflects"].as_array().into_iter().flatten() {
            let shown = format!("REFLECTS {}", t.as_str().unwrap_or_default());
            facts.insert((file.clone(), line(f), shown));
        }
        for (capability, causes) in f["capabilities"].as_object().into_iter().flatten() {
            for c in causes.as_array().into_iter().flatten() {
                let fact = capability.to_ascii_uppercase();
                facts.insert((file.clone(), line(c), fact));
            }
        }
    }
    cycles(&record, &mut facts);
    Ok((
        record["tier"].as_str().unwrap_or_default().to_owned(),
        facts,
    ))
}

/// Adds the fields and variants through which each type of a module's record can form a cycle,
/// at the type's first line (cycles.can-form-cycle).
fn cycles(record: &Value, facts: &mut BTreeSet<Fact>) {
    for d in record["declarations"].as_array().into_iter().flatten() {
        let file = d["file"].as_str().unwrap_or_default();
        let line = u32::try_from(d["line"].as_u64().unwrap_or(0)).unwrap_or(0);
        for name in d["cycle"].as_array().into_iter().flatten() {
            let shown = format!("CYCLE {}", name.as_str().unwrap_or_default());
            facts.insert((file.to_owned(), line, shown));
        }
    }
}

/// What differs between a module's expected and shown facts, if anything does.
fn compare(program: &Path, module: &str, file: &str) -> Result<(), String> {
    let (tier, expected) = expected(&suite::source(program, file), file)?;
    let (shown_tier, shown) = shown(program, module)?;
    let mut problems = Vec::new();
    if tier.as_deref() != Some(shown_tier.as_str()) {
        problems.push(format!("{file}: the tier is {shown_tier}, not {tier:?}"));
    }
    for (file, line, fact) in expected.difference(&shown) {
        problems.push(format!("{file}:{line}: {fact} expected, not shown"));
    }
    for (file, line, fact) in shown.difference(&expected) {
        problems.push(format!("{file}:{line}: {fact} shown, not expected"));
    }
    if problems.is_empty() {
        Ok(())
    } else {
        Err(problems.join("\n"))
    }
}

/// The failures of the programs of a suite.
fn failures(programs: &[std::path::PathBuf]) -> Vec<String> {
    programs
        .iter()
        .flat_map(|p| {
            suite::modules(p)
                .into_iter()
                .map(move |(module, file)| (p, module, file))
        })
        .filter_map(|(program, module, file)| compare(program, &module, &file).err())
        .collect()
}

#[test]
fn proved_checks_are_read_and_shown() {
    // This crate's own program, apart from the suite, which pins `PROVED` and its near misses.
    let program = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/facts/proved.lt");
    let found = failures(&[program]);
    assert!(found.is_empty(), "{}", found.join("\n"));
}

#[test]
fn a_proved_check_names_its_rule() {
    // facts.shown-proofs: `show --json` gives the rule that proves each check under `rule`, and its
    // line's comment names it after what it rules out.
    let program = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/facts/proved.lt");
    let record = suite::show_module(&program, "main").expect("the program shows");
    let proved: Vec<(u64, String, String)> = record["functions"]
        .as_array()
        .into_iter()
        .flatten()
        .flat_map(|f| f["proved"].as_array().cloned().unwrap_or_default())
        .map(|p| {
            let field = |key: &str| p[key].as_str().unwrap_or_default().to_owned();
            (
                p["line"].as_u64().unwrap_or_default(),
                field("rule"),
                field("cause"),
            )
        })
        .collect();
    let expected = [
        (7, "guard", "proved bounds by a guard"),
        (17, "range loop", "proved bounds by a range loop"),
        (23, "divisor", "proved divide-by-zero by a divisor"),
        (29, "key", "proved missing-key by a key"),
    ]
    .map(|(line, rule, cause)| (line, rule.to_owned(), cause.to_owned()));
    assert_eq!(proved, expected);
}

#[test]
fn every_function_shows_the_facts_the_records_give() {
    let programs = suite::programs(&suite::root("facts"));
    assert!(!programs.is_empty(), "the suite has programs");
    let failures = failures(&programs);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
