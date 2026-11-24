//! The standard library as the documents show it: each row of a table of functions, methods or
//! items in the guide and the Reference writes a signature that `std` declares, as `stilt doc
//! --std --json` prints it, and each row of a table of variants a variant that one of its types
//! declares, so that no document drifts from the library it describes.
//!
//! A row may name a function through its module or its type (`fs.read`, `Deque.new`), leave out
//! its type parameters, name a type through its module (`net.Stream`), and write a capital letter
//! alone for a type, which then stands for the same type wherever the row writes it, so that
//! `to_U(self) -> Option<U>` is `to_i8(self) -> Option<i8>`. A path without a call in a row, such
//! as a name after a signature (`checked_sub`) or a constant (`T.MAX`), names something `std`
//! declares, and a type's definition (`Delim = | Paren | Bracket | Brace`) is part of one of
//! its types'.

mod common;

use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

use serde_json::Value;

/// The headers of the tables whose rows are checked.
const SIGNATURES: [&str; 3] = ["Function", "Method", "Item"];
const VARIANTS: &str = "Variant";

/// What `std` declares: each function's signatures, as tokens, by its name; every name; and the
/// signature of each type, with its spaces made single.
#[derive(Default)]
struct Library {
    signatures: HashMap<String, Vec<Vec<String>>>,
    names: HashSet<String>,
    types: Vec<String>,
}

impl Library {
    fn read() -> Library {
        let out = common::stilt(&["doc", "--std", "--json"], None);
        assert!(out.status.success(), "{}", common::stderr(&out));
        let json: Value = serde_json::from_slice(&out.stdout).expect("the pages are JSON");
        let mut library = Library::default();
        for module in json["modules"].as_array().expect("the modules") {
            library.add(&module["items"]);
        }
        library
    }

    fn add(&mut self, items: &Value) {
        for item in items.as_array().into_iter().flatten() {
            let name = item["name"].as_str().unwrap_or_default();
            let signature = item["signature"].as_str().unwrap_or_default();
            self.names.insert(name.to_owned());
            match item["kind"].as_str() {
                Some("fn") => {
                    let declared = from_name(&tokens(signature));
                    self.signatures
                        .entry(name.to_owned())
                        .or_default()
                        .push(declared);
                }
                Some("type") => self.types.push(spaced(signature)),
                _ => {}
            }
            self.add(&item["members"]);
        }
    }

    /// Why the code `span` of a row with the header `header` isn't what `std` declares, if it
    /// isn't.
    fn wrong(&self, header: &str, span: &str) -> Option<String> {
        let all = tokens(span);
        let defines =
            all.get(1).is_some_and(|t| t == "=") && all[0].starts_with(char::is_uppercase);
        if header == VARIANTS || defines {
            let written = spaced(span);
            let declared = self.types.iter().any(|t| t.contains(&written));
            return (!declared).then(|| "no type of std declares this".to_owned());
        }
        if !span.contains('(') {
            // A letter alone stands for a type, and code that is no path, as `xs[i] = v`, names
            // nothing.
            let path = all.iter().all(|t| is_word(t) || t == ".");
            let name = all.last().filter(|n| path && placeholder(n).is_none())?;
            let known = self.names.contains(name);
            return (!known).then(|| format!("std declares nothing named `{name}`"));
        }
        let written = from_name(&all);
        let name = written.first()?;
        let declared = self.candidates(name);
        if declared.iter().any(|d| matches(&written, d)) {
            return None;
        }
        let shown: Vec<String> = declared.iter().map(|d| shown(d)).collect();
        Some(match shown.as_slice() {
            [] => format!("std declares no function `{name}`"),
            _ => format!("std declares `{name}` as {}", shown.join(" or ")),
        })
    }

    /// The signatures a row's function name can be: its own, or, for a name that ends in a
    /// type's letter, as `to_U`, every one with the same stem.
    fn candidates(&self, name: &str) -> Vec<&Vec<String>> {
        match named_placeholder(name) {
            Some((stem, _)) => (self.signatures.iter())
                .filter(|(n, _)| n.len() > stem.len() && n.starts_with(stem))
                .flat_map(|(_, s)| s)
                .collect(),
            None => self.signatures.get(name).into_iter().flatten().collect(),
        }
    }
}

/// The tokens of code: words, `->`, and each other character but spaces on its own.
fn tokens(code: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut chars = code.chars().peekable();
    while let Some(c) = chars.next() {
        if c.is_alphanumeric() || c == '_' {
            let mut word = c.to_string();
            while let Some(&d) = chars.peek() {
                if !(d.is_alphanumeric() || d == '_') {
                    break;
                }
                word.push(d);
                chars.next();
            }
            out.push(word);
        } else if c == '-' && chars.peek() == Some(&'>') {
            chars.next();
            out.push("->".to_owned());
        } else if !c.is_whitespace() {
            out.push(c.to_string());
        }
    }
    out
}

/// A signature's tokens from its function's name on, which leaves out `pub`, `fn` and the module
/// or type a row names it through, with no module before a type's name.
fn from_name(tokens: &[String]) -> Vec<String> {
    let open = (tokens.iter())
        .position(|t| t == "(" || t == "<")
        .unwrap_or(tokens.len());
    let rest = &tokens[open.saturating_sub(1)..];
    let mut out = Vec::new();
    let mut i = 0;
    while i < rest.len() {
        let qualifies = rest[i].starts_with(|c: char| c.is_ascii_lowercase())
            && rest.get(i + 1).is_some_and(|t| t == ".")
            && (rest.get(i + 2)).is_some_and(|t| t.starts_with(|c: char| c.is_ascii_uppercase()));
        if qualifies {
            i += 2;
        } else {
            out.push(rest[i].clone());
            i += 1;
        }
    }
    out
}

/// Whether a row's tokens `written` are the declared ones, each capital letter alone in the row
/// standing for one type throughout, with the type parameters after the name written or not.
fn matches(written: &[String], declared: &[String]) -> bool {
    let mut bound: HashMap<char, Vec<String>> = HashMap::new();
    let mut bind = |letter: char, ty: Vec<String>| -> bool {
        let earlier = bound.entry(letter).or_insert_with(|| ty.clone());
        !ty.is_empty() && *earlier == ty
    };
    let (mut i, mut j) = (0, 0);
    while i < written.len() {
        let token = &written[i];
        if i == 1 && token == "(" && declared.get(j).is_some_and(|t| t == "<") {
            j = balanced(declared, j);
            continue;
        }
        if let Some(letter) = placeholder(token) {
            let end = type_end(declared, j);
            if !bind(letter, declared[j..end].to_vec()) {
                return false;
            }
            j = end;
        } else if let Some((stem, letter)) = named_placeholder(token) {
            let Some(rest) = declared.get(j).and_then(|t| t.strip_prefix(stem)) else {
                return false;
            };
            if !bind(letter, vec![rest.to_owned()]) {
                return false;
            }
            j += 1;
        } else if declared.get(j) == Some(token) {
            j += 1;
        } else {
            return false;
        }
        i += 1;
    }
    j == declared.len()
}

/// The letter of a token that is a capital letter alone, which stands for a type.
fn placeholder(token: &str) -> Option<char> {
    let mut chars = token.chars();
    let letter = chars.next().filter(char::is_ascii_uppercase)?;
    chars.next().is_none().then_some(letter)
}

/// The stem and the letter of a name that ends in a type's letter, as `to_U`.
fn named_placeholder(token: &str) -> Option<(&str, char)> {
    let (stem, last) = token.rsplit_once('_')?;
    let letter = placeholder(last)?;
    Some((&token[..=stem.len()], letter))
}

/// Where the type that starts at `j` ends: a name, with its arguments; a tuple; or a function's
/// type, with its result.
fn type_end(tokens: &[String], j: usize) -> usize {
    match tokens.get(j).map(String::as_str) {
        Some("(") => balanced(tokens, j),
        Some("fn") => {
            let end = balanced(tokens, j + 1);
            match tokens.get(end).map(String::as_str) {
                Some("->") => type_end(tokens, end + 1),
                _ => end,
            }
        }
        Some(word) if is_word(word) => match tokens.get(j + 1).map(String::as_str) {
            Some("<") => balanced(tokens, j + 1),
            _ => j + 1,
        },
        _ => j,
    }
}

/// The token after the bracket that closes the one at `j`.
fn balanced(tokens: &[String], j: usize) -> usize {
    let mut depth = 0usize;
    for (k, token) in tokens.iter().enumerate().skip(j) {
        match token.as_str() {
            "(" | "<" | "[" | "{" => depth += 1,
            ")" | ">" | "]" | "}" => depth = depth.saturating_sub(1),
            _ => {}
        }
        if depth == 0 {
            return k + 1;
        }
    }
    tokens.len()
}

/// Tokens written back as code, with a space between two words, after `,` and `:`, and around
/// `->` and `/`.
fn shown(tokens: &[String]) -> String {
    let mut out = String::new();
    let mut last = "";
    for token in tokens {
        let t = token.as_str();
        let spaced = (is_word(last) && is_word(t))
            || matches!(last, "," | ":" | "->" | "/")
            || matches!(t, "->" | "/");
        if spaced && !out.is_empty() {
            out.push(' ');
        }
        out.push_str(t);
        last = t;
    }
    format!("`{out}`")
}

fn is_word(token: &str) -> bool {
    token.starts_with(|c: char| c.is_alphanumeric() || c == '_')
}

fn spaced(code: &str) -> String {
    code.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// A row of a checked table: where it is, its table's header, and the code of its first cell.
struct Row {
    at: String,
    header: String,
    spans: Vec<String>,
}

/// The rows of the tables of `path` whose header is one this test checks.
fn rows(path: &Path) -> Vec<Row> {
    let text = fs::read_to_string(path).expect("the document is readable");
    let lines: Vec<&str> = text.lines().collect();
    let mut out = Vec::new();
    let mut header = String::new();
    for (n, line) in lines.iter().enumerate() {
        if !line.starts_with('|') {
            header.clear();
            continue;
        }
        if line.starts_with("| ---") {
            header = n
                .checked_sub(1)
                .and_then(|h| cells(lines[h]).first().map(|c| c.trim().to_owned()))
                .unwrap_or_default();
            continue;
        }
        let checked = SIGNATURES.contains(&header.as_str()) || header == VARIANTS;
        if let (true, Some(first)) = (checked, cells(line).first()) {
            out.push(Row {
                at: format!("{}:{}", path.display(), n + 1),
                header: header.clone(),
                spans: code_spans(first),
            });
        }
    }
    out
}

/// The cells of a table's row, split at the bars outside its code.
fn cells(line: &str) -> Vec<String> {
    let mut out = vec![String::new()];
    let mut code = false;
    let mut escaped = false;
    for c in line.trim().trim_start_matches('|').chars() {
        match c {
            '`' => code = !code,
            '|' if !code && !escaped => {
                out.push(String::new());
                continue;
            }
            _ => {}
        }
        escaped = c == '\\';
        out.last_mut().expect("a cell").push(c);
    }
    out.pop();
    out
}

/// The code of a cell, in which Markdown writes a bar `\|`.
fn code_spans(cell: &str) -> Vec<String> {
    (cell.split('`').skip(1).step_by(2))
        .map(|code| code.replace("\\|", "|"))
        .collect()
}

/// The documents whose tables are checked.
fn documents() -> Vec<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut out = Vec::new();
    for dir in ["docs/guide", "reference"] {
        let entries = fs::read_dir(root.join(dir)).expect("the directory is readable");
        for entry in entries.map(|e| e.expect("an entry").path()) {
            if entry.extension().is_some_and(|e| e == "md") {
                out.push(entry);
            }
        }
    }
    out.sort();
    out
}

#[test]
fn every_signature_the_documents_show_is_the_library_s() {
    let library = Library::read();
    let mut wrong = Vec::new();
    let mut checked = 0;
    for row in documents().iter().flat_map(|d| rows(d)) {
        for span in &row.spans {
            checked += 1;
            if let Some(why) = library.wrong(&row.header, span) {
                wrong.push(format!("{}: `{span}`: {why}", row.at));
            }
        }
    }
    assert!(checked > 300, "only {checked} spans were found");
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn a_row_matches_through_its_letters_and_names() {
    let t = |s: &str| from_name(&tokens(s));
    let declared = t("pub fn to_i8(self) -> Option<i8>");
    assert!(matches(&t("to_U(self) -> Option<U>"), &declared));
    assert!(!matches(&t("to_U(self) -> Option<i16>"), &declared));
    let generic = t("pub fn fill<T, n: i64>(x: T) -> Array<T, n>");
    assert!(matches(&t("array.fill(x: T) -> Array<T, n>"), &generic));
    let qualified = t("pub fn accept(inout self) -> Stream / io");
    assert!(matches(
        &t("accept(inout self) -> net.Stream / io"),
        &qualified
    ));
    assert!(!matches(&t("accept(inout self) -> net.Stream"), &qualified));
}
