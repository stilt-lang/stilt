//! The registry of diagnostic codes, `reference/errors.toml`, read and checked.
//!
//! The registry is a table per code, `[E0311]`, and an array of tables of its examples,
//! `[[E0311.examples]]`, holding one-line basic strings, multi-line literal strings whose
//! closing `'''` stands on a line of its own, integers and booleans. That is all of TOML that
//! this reader takes: anything else in the registry is an error, as is a key that no entry has.

use std::collections::BTreeMap;

/// The phases a code may be checked in (errors.registry-phases).
pub(crate) const PHASES: [&str; 6] = [
    "syntax", "items", "types", "analyses", "warnings", "refusal",
];

/// The tiers in which a code may first occur (program.tiers).
pub(crate) const TIERS: [&str; 4] = ["core", "advanced", "meta", "systems"];

/// A code's entry.
#[derive(Debug)]
pub(crate) struct Entry {
    /// The code, such as `E0311`.
    pub(crate) code: String,
    /// A short title, in lowercase.
    pub(crate) title: String,
    /// The ID of the paragraph that defines the code, its home.
    pub(crate) reference: String,
    pub(crate) tier: String,
    pub(crate) phase: String,
    /// What to do about the diagnostic and why Stilt works this way, for the person who
    /// made the mistake.
    pub(crate) help: String,
    /// Where the diagnostic is reported (errors.primary-spans).
    pub(crate) span: String,
    pub(crate) retired: bool,
    /// The mistakes the code is about, each with its fix.
    pub(crate) examples: Vec<Example>,
}

/// A program that makes a mistake, and the same program with the mistake fixed.
#[derive(Debug)]
pub(crate) struct Example {
    /// The program with the mistake, a file `main.lt`.
    pub(crate) wrong: String,
    /// The line of `wrong` at which the code is reported.
    pub(crate) line: u32,
    /// The program fixed, which has no diagnostic.
    pub(crate) right: String,
}

/// A value of the registry.
#[derive(Debug, PartialEq)]
enum Value {
    String(String),
    Integer(u32),
    Bool(bool),
}

/// A table: its keys and values, with the line of each key.
type Table = BTreeMap<String, (usize, Value)>;

/// The entries of `text`, the registry, in its order, or every error in it.
pub(crate) fn read(text: &str) -> Result<Vec<Entry>, Vec<String>> {
    let (tables, mut errors) = tables(text);
    let mut entries = Vec::new();
    for (code, table, examples) in tables {
        match entry(&code, table, examples) {
            Ok(entry) => entries.push(entry),
            Err(mut found) => errors.append(&mut found),
        }
    }
    if errors.is_empty() {
        Ok(entries)
    } else {
        Err(errors)
    }
}

/// The tables of the registry: each code's, with the tables of its examples.
type Tables = Vec<(String, Table, Vec<Table>)>;

/// The tables of `text`, and the errors of its lines.
fn tables(text: &str) -> (Tables, Vec<String>) {
    let mut tables: Tables = Vec::new();
    let mut errors = Vec::new();
    let mut lines = text.lines().enumerate().map(|(i, l)| (i + 1, l));
    while let Some((number, line)) = lines.next() {
        let fail = |what: &str| format!("reference/errors.toml:{number}: {what}");
        if line.trim().is_empty() || line.starts_with('#') {
            continue;
        }
        if let Some(name) = line.strip_prefix("[[").and_then(|l| l.strip_suffix("]]")) {
            match (name.split_once('.'), tables.last_mut()) {
                (Some((code, "examples")), Some((last, _, examples))) if code == last => {
                    examples.push(Table::new());
                }
                _ => errors.push(fail("expected `[[CODE.examples]]` after `[CODE]`")),
            }
            continue;
        }
        if let Some(code) = line.strip_prefix('[').and_then(|l| l.strip_suffix(']')) {
            tables.push((code.to_owned(), Table::new(), Vec::new()));
            continue;
        }
        let Some((key, written)) = line.split_once(" = ") else {
            errors.push(fail("expected `key = value`"));
            continue;
        };
        let value = if written == "'''" {
            multiline(&mut lines).ok_or_else(|| fail("a `'''` string that never closes"))
        } else {
            scalar(written).ok_or_else(|| fail("expected a string, an integer or a boolean"))
        };
        let table = match tables.last_mut() {
            Some((_, _, examples)) if !examples.is_empty() => examples.last_mut(),
            Some((_, table, _)) => Some(table),
            None => None,
        };
        match (value, table) {
            (Ok(value), Some(table)) => {
                if table.insert(key.to_owned(), (number, value)).is_some() {
                    errors.push(fail(&format!("`{key}` given twice")));
                }
            }
            (Err(error), _) => errors.push(error),
            (_, None) => errors.push(fail("a key before the first code")),
        }
    }
    (tables, errors)
}

/// The lines of a multi-line literal string, after the line that opens it, up to the line
/// that holds only `'''`, each with its newline.
fn multiline<'a>(lines: &mut impl Iterator<Item = (usize, &'a str)>) -> Option<Value> {
    let mut text = String::new();
    for (_, line) in lines {
        if line == "'''" {
            return Some(Value::String(text));
        }
        text.push_str(line);
        text.push('\n');
    }
    None
}

/// A one-line value: a basic string, an integer or a boolean.
fn scalar(written: &str) -> Option<Value> {
    match written {
        "true" => return Some(Value::Bool(true)),
        "false" => return Some(Value::Bool(false)),
        _ => {}
    }
    if let Ok(n) = written.parse() {
        return Some(Value::Integer(n));
    }
    let mut chars = written.strip_prefix('"')?.strip_suffix('"')?.chars();
    let mut value = String::new();
    while let Some(c) = chars.next() {
        if c == '"' {
            return None;
        }
        if c != '\\' {
            value.push(c);
            continue;
        }
        value.push(match chars.next()? {
            '\\' => '\\',
            '"' => '"',
            'n' => '\n',
            't' => '\t',
            'u' => {
                let hex: String = chars.by_ref().take(4).collect();
                char::from_u32(u32::from_str_radix(&hex, 16).ok()?)?
            }
            _ => return None,
        });
    }
    Some(Value::String(value))
}

/// The entry of `code`, from its table and its examples' tables.
fn entry(code: &str, mut table: Table, examples: Vec<Table>) -> Result<Entry, Vec<String>> {
    let mut errors = Vec::new();
    let well_formed = code.len() == 5
        && code.starts_with(['E', 'W'])
        && code[1..].bytes().all(|b| b.is_ascii_digit());
    if !well_formed {
        errors.push(format!(
            "`{code}` isn't a code, a letter E or W and four digits"
        ));
    }
    let mut take = |key: &str| string(code, &mut table, key, &mut errors);
    let title = take("title");
    let reference = take("reference");
    let tier = take("tier");
    let phase = take("phase");
    let help = take("help");
    let span = take("span");
    let retired = match table.remove("retired") {
        None => false,
        Some((_, Value::Bool(b))) => b,
        Some((line, _)) => {
            errors.push(format!(
                "reference/errors.toml:{line}: `retired` is a boolean"
            ));
            false
        }
    };
    if !TIERS.contains(&tier.as_str()) {
        errors.push(format!(
            "{code}: `{tier}` is no tier; the tiers are {}",
            TIERS.join(", ")
        ));
    }
    if !PHASES.contains(&phase.as_str()) {
        let phases = PHASES.join(", ");
        errors.push(format!(
            "{code}: `{phase}` is no phase; the phases are {phases}"
        ));
    }
    unknown(code, &table, &mut errors);
    let examples = examples
        .into_iter()
        .filter_map(|t| example(code, t, &mut errors))
        .collect();
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(Entry {
        code: code.to_owned(),
        title,
        reference,
        tier,
        phase,
        help,
        span,
        retired,
        examples,
    })
}

/// The example of `code` that `table` holds, or `None` with its errors added to `errors`.
fn example(code: &str, mut table: Table, errors: &mut Vec<String>) -> Option<Example> {
    let before = errors.len();
    let wrong = string(code, &mut table, "wrong", errors);
    let right = string(code, &mut table, "right", errors);
    let line = match table.remove("line") {
        Some((_, Value::Integer(n))) if n > 0 && n as usize <= wrong.lines().count() => n,
        Some((line, _)) => {
            errors.push(format!(
                "reference/errors.toml:{line}: `line` is a line of the example"
            ));
            0
        }
        None => {
            errors.push(format!("{code}: an example has no `line`"));
            0
        }
    };
    unknown(code, &table, errors);
    (errors.len() == before).then_some(Example { wrong, line, right })
}

/// The string that `key` gives in `table`, taken out of it, or an empty string with an error.
fn string(code: &str, table: &mut Table, key: &str, errors: &mut Vec<String>) -> String {
    match table.remove(key) {
        Some((_, Value::String(s))) if !s.trim().is_empty() => s,
        Some((line, _)) => {
            errors.push(format!(
                "reference/errors.toml:{line}: `{key}` is a string with text"
            ));
            String::new()
        }
        None => {
            errors.push(format!("{code} has no `{key}`"));
            String::new()
        }
    }
}

/// An error for each key left in `table`, which no entry has.
fn unknown(code: &str, table: &Table, errors: &mut Vec<String>) {
    for (key, (line, _)) in table {
        errors.push(format!(
            "reference/errors.toml:{line}: {code} has a key `{key}` that no entry has"
        ));
    }
}

#[cfg(test)]
mod tests {
    use super::read;

    const ENTRY: &str = "[E0001]\ntitle = \"a \\\"b\\\"\"\nreference = \"lexical.source-text\"\n\
        tier = \"core\"\nphase = \"syntax\"\nhelp = \"h\"\nspan = \"s\"\n";

    #[test]
    fn reads_an_entry_and_its_examples() {
        let text = format!(
            "# A comment.\n\n{ENTRY}\n[[E0001.examples]]\nwrong = '''\nfn f() {{\n'''\n\
             line = 1\nright = '''\nfn f() {{}}\n'''\n"
        );
        let entries = read(&text).expect("the registry is well formed");
        assert_eq!(entries[0].title, "a \"b\"");
        assert_eq!(entries[0].examples[0].wrong, "fn f() {\n");
        assert_eq!(entries[0].examples[0].line, 1);
        assert!(!entries[0].retired);
    }

    #[test]
    fn rejects_missing_and_unknown_keys() {
        let text = ENTRY.replace("help = \"h\"\n", "why = \"w\"\n");
        let errors = read(&text).expect_err("the entry lacks `help`");
        assert_eq!(errors.len(), 2, "{errors:?}");
        assert!(errors[0].contains("has no `help`"), "{errors:?}");
        assert!(errors[1].contains("a key `why`"), "{errors:?}");
    }

    #[test]
    fn rejects_an_unknown_phase_and_a_line_past_the_example() {
        let text = format!(
            "{}[[E0001.examples]]\nwrong = \"x\"\nline = 2\nright = \"y\"\n",
            ENTRY.replace("\"syntax\"", "\"later\"")
        );
        let errors = read(&text).expect_err("the entry is wrong twice");
        assert!(
            errors.iter().any(|e| e.contains("`later` is no phase")),
            "{errors:?}"
        );
        assert!(
            errors.iter().any(|e| e.contains("`line` is a line")),
            "{errors:?}"
        );
    }
}
