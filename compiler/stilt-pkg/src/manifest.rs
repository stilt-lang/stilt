//! A package's manifest, `stilt.toml`: its form and its keys (packages.manifest,
//! packages.package-table and packages.dependencies; facts.capability-grants; editions.edition).
//!
//! Every error of a manifest is an E0600, at the key or the value it is about. A dependency's
//! entry with an E0600 still declares its name, so that the packages that use it get the error
//! type rather than more errors (packages.manifests-with-errors).

mod entry;

pub(crate) use entry::is_version;

use stilt_diag::{Diagnostic, codes};
use stilt_syntax::capability::Capabilities;
use stilt_syntax::{TextRange, TextSize};

use crate::toml::{self, Table, Value, ValueKind};

/// What a manifest says, with its errors.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Manifest {
    /// The name of `[package]`, when it gives a valid one.
    pub name: Option<String>,
    /// The edition that `[package]` names, when it names a valid one (editions.edition).
    pub edition: Option<&'static str>,
    /// Where `migrate` writes an edition: the span of the value of `edition`, or the end of
    /// the line of `name`, or the end of the `[package]` header's line, or nowhere.
    pub edition_at: EditionAt,
    /// Whether it declares dependencies: it is TOML 1.0, and its `[dependencies]`, when it has
    /// one, is a table (packages.manifests-with-errors).
    pub declares: bool,
    /// The entries of the `[dependencies]` table.
    pub entries: Vec<Entry>,
    /// The C libraries of `[package]`'s `link`, each with the span of its string, in order
    /// (c.linking).
    pub links: Vec<(String, TextRange)>,
    /// Its E0600s.
    pub problems: Vec<Diagnostic>,
}

/// An entry of `[dependencies]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    /// The name of the dependency.
    pub name: String,
    /// The span of its key: the key before its `=`, or the name in its header.
    pub key: TextRange,
    /// Where it comes from, or `None` when the entry has an E0600.
    pub source: Option<Source>,
    /// What its `may` grants (packages.grants; facts.capability-grants).
    pub may: Grant,
    /// The span of its `may`'s value, when it has one.
    pub may_at: Option<TextRange>,
    /// Where `check` writes the keys it fills in (packages.filling-in).
    pub fill: Fill,
}

/// What an entry's `may` grants: `io`, which grants every capability and `io` without one, or
/// capabilities, which grant themselves (facts.capability-grants), and `unsafe`, which grants the
/// package's own `unsafe` blocks, and which `io` doesn't grant (c.granting-unsafe).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Grant {
    /// Whether `io` is granted.
    pub io: bool,
    /// The capabilities granted.
    pub capabilities: Capabilities,
    /// Whether the package may hold `unsafe` blocks.
    pub unsafe_code: bool,
}

/// Where `stilt migrate` writes a package's edition (editions.migrate).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum EditionAt {
    /// The span of the value of `edition`, which it replaces.
    Value(TextRange),
    /// The end of a line of `[package]`, after which it writes a line of its own.
    After(TextSize),
    /// Nowhere in the manifest: it writes a `[package]` table first.
    #[default]
    Nowhere,
}

/// Where a dependency comes from (packages.dependencies).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Source {
    /// A directory, relative to the manifest's, with `/` as the separator.
    Path(String),
    /// A git repository, with the version and hash that pin it, when the entry gives them.
    From {
        /// The repository the package comes from.
        from: String,
        /// The version it asks for, if one.
        version: Option<Pinned>,
        /// The hash it pins, if one.
        hash: Option<Pinned>,
    },
}

/// A pinned value, and the span of its string in the manifest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pinned {
    /// The text of the string.
    pub value: String,
    /// Where the string is in the manifest.
    pub at: TextRange,
}

/// Where the keys that an entry lacks are written.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Fill {
    /// In an inline table, after its last value: `, version = "…"`.
    Inline(TextSize),
    /// On lines of their own after this offset, the end of the entry's last line, each key
    /// written with this prefix: empty in a table of its own, `NAME.` for dotted keys.
    Lines(TextSize, String),
}

/// Reads a manifest. A file that isn't TOML 1.0 declares no name and no dependency.
#[must_use]
pub fn read(bytes: &[u8]) -> Manifest {
    let root = match toml::parse(bytes) {
        Ok(root) => root,
        Err(e) => {
            let message = format!("this manifest isn't TOML 1.0: {}", e.message);
            return Manifest {
                problems: vec![Diagnostic::new(codes::E0600, point(e.at), message)],
                ..Manifest::default()
            };
        }
    };
    let mut manifest = Reader {
        text: std::str::from_utf8(bytes).unwrap_or_default(),
        out: Manifest {
            declares: true,
            ..Manifest::default()
        },
    };
    for e in &root.entries {
        match e.key.as_str() {
            "package" => manifest.package(e.at, &e.value),
            "dependencies" => match &e.value.kind {
                ValueKind::Table(table) => manifest.dependencies(table),
                other => {
                    manifest.out.declares = false;
                    manifest.wrong("`[dependencies]`", "a table", other, &e.value);
                }
            },
            key => {
                let what = match e.value.kind {
                    ValueKind::Table(_) | ValueKind::Tables(_) => "table",
                    _ => "key",
                };
                let at = manifest.key(e.at);
                manifest.problem(at, format!("a manifest has no {what} `{key}`"));
            }
        }
    }
    manifest.out
}

/// A manifest being read, with its text, which places its keys.
struct Reader<'a> {
    text: &'a str,
    out: Manifest,
}

impl Reader<'_> {
    fn problem(&mut self, at: TextRange, message: String) {
        self.out
            .problems
            .push(Diagnostic::new(codes::E0600, at, message));
    }

    /// The span of the key written at `at`: a bare key, or a quoted one with its quotes.
    fn key(&self, at: usize) -> TextRange {
        let rest = &self.text[at..];
        let len = match rest.chars().next() {
            Some(q @ ('"' | '\'')) => rest[1..]
                .char_indices()
                .find(|&(i, c)| c == q && (q == '\'' || !rest[1..=i].ends_with('\\')))
                .map_or(rest.len(), |(i, _)| i + 2),
            _ => rest
                .chars()
                .take_while(|&c| c.is_ascii_alphanumeric() || c == '_' || c == '-')
                .count(),
        };
        TextRange::at(
            TextSize::from(to_u32(at)),
            TextSize::from(to_u32(len.max(1))),
        )
    }

    /// An E0600 for a value of the wrong type.
    fn wrong(&mut self, what: &str, wanted: &str, kind: &ValueKind, value: &Value) {
        let message = format!("{what} is {wanted}, not {}", kind.describe());
        self.problem(range(value), message);
    }

    /// `[package]`, which gives the package's name, its edition and the C libraries it links
    /// (packages.package-table; editions.edition; c.linking).
    fn package(&mut self, at: usize, value: &Value) {
        let ValueKind::Table(table) = &value.kind else {
            self.wrong("`[package]`", "a table", &value.kind, value);
            return;
        };
        self.out.edition_at = EditionAt::After(self.line_end(at));
        for e in &table.entries {
            match e.key.as_str() {
                "name" => self.out.edition_at = EditionAt::After(self.line_end(e.value.end)),
                "edition" => {
                    self.edition(&e.value);
                    continue;
                }
                "link" => {
                    self.link(&e.value);
                    continue;
                }
                key => {
                    let message = format!("`[package]` has no key `{key}`");
                    self.problem(self.key(e.at), message);
                    continue;
                }
            }
            match &e.value.kind {
                ValueKind::String(name) if is_package_name(name) => {
                    self.out.name = Some(name.clone());
                }
                ValueKind::String(name) => {
                    let message = format!("`{name}` isn't a valid package name");
                    let d = Diagnostic::new(codes::E0600, range(&e.value), message)
                        .with_label(why_invalid(name));
                    self.out.problems.push(d);
                }
                other => self.wrong("a package's name", "a string", other, &e.value),
            }
        }
    }

    /// `edition`, which names one of the editions (editions.edition).
    fn edition(&mut self, value: &Value) {
        self.out.edition_at = EditionAt::Value(range(value));
        let ValueKind::String(name) = &value.kind else {
            return self.wrong("a package's edition", "a string", &value.kind, value);
        };
        if let Some(edition) = crate::edition::named(name) {
            self.out.edition = Some(edition.name);
        } else {
            let listed = crate::edition::listed();
            let message =
                format!("this manifest's edition is `{name}`, and the editions are {listed}");
            self.problem(range(value), message);
        }
    }

    /// The offset of the end of the line that holds `at`.
    fn line_end(&self, at: usize) -> TextSize {
        let rest = self.text.get(at..).unwrap_or_default();
        let end = rest.find('\n').map_or(self.text.len(), |n| at + n);
        TextSize::from(to_u32(end))
    }

    /// `link`, the C libraries that the package's foreign functions need, each a name of
    /// letters, digits, `_`, `-` and `.` (c.linking).
    fn link(&mut self, value: &Value) {
        let ValueKind::Array(names) = &value.kind else {
            self.wrong("`link`", "a list of strings", &value.kind, value);
            return;
        };
        for v in names {
            match &v.kind {
                ValueKind::String(name) if is_library_name(name) => {
                    self.out.links.push((name.clone(), range(v)));
                }
                ValueKind::String(name) => {
                    let message = format!(
                        "`{name}` isn't a C library's name, of letters, digits, `_`, `-` and `.`"
                    );
                    self.problem(range(v), message);
                }
                other => self.wrong("a C library's name", "a string", other, v),
            }
        }
    }

    /// `[dependencies]`, whose entries name the dependencies (packages.dependencies).
    fn dependencies(&mut self, table: &Table) {
        for e in &table.entries {
            let key = self.key(e.at);
            let entry = match &e.value.kind {
                ValueKind::Table(fields) => self.entry(&e.key, key, fields),
                other => {
                    let what = format!("the entry `{}`", e.key);
                    self.wrong(&what, "a table", other, &e.value);
                    Entry {
                        name: e.key.clone(),
                        key,
                        source: None,
                        may: Grant::default(),
                        may_at: None,
                        fill: Fill::Inline(TextSize::from(to_u32(e.value.end))),
                    }
                }
            };
            self.out.entries.push(entry);
        }
    }
}

/// The manifest `bytes` with its edition set to `edition`: in place of the value of `edition`,
/// or on a line of its own after `name`, or after the `[package]` header, or in a `[package]`
/// table written first (editions.migrate).
#[must_use]
pub fn with_edition(bytes: &[u8], edition: &str) -> Vec<u8> {
    let value = format!("\"{edition}\"");
    let (at, end, text) = match read(bytes).edition_at {
        EditionAt::Value(r) => (usize::from(r.start()), usize::from(r.end()), value),
        EditionAt::After(at) => {
            let at = usize::from(at);
            (at, at, format!("\nedition = {value}"))
        }
        EditionAt::Nowhere => (0, 0, format!("[package]\nedition = {value}\n\n")),
    };
    let mut out = bytes.to_vec();
    out.splice(at..end, text.into_bytes());
    out
}

/// Whether `name` is a C library's name: one or more letters, digits, `_`, `-` and `.`
/// (c.linking).
#[must_use]
pub fn is_library_name(name: &str) -> bool {
    !name.is_empty()
        && name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '.'))
}

/// Whether `name` is a valid package name: a valid first segment of a module's name other than
/// `main` (packages.package-table; program.module-names).
#[must_use]
pub fn is_package_name(name: &str) -> bool {
    stilt_syntax::is_module_segment(name) && name != "std" && name != "main"
}

fn why_invalid(name: &str) -> &'static str {
    match name {
        "std" => "`std` is the standard library's",
        "main" => "`main` is the name of a package's root module",
        _ if stilt_syntax::is_keyword(name) => "a reserved word",
        _ if stilt_syntax::is_primitive(name) => "a primitive type's name",
        _ => "a package's name is a lowercase identifier",
    }
}

pub(crate) fn to_u32(offset: usize) -> u32 {
    u32::try_from(offset).unwrap_or(u32::MAX)
}

/// The empty span at a byte offset.
fn point(at: usize) -> TextRange {
    TextRange::empty(TextSize::from(to_u32(at)))
}

/// The span of a value.
pub(crate) fn range(value: &Value) -> TextRange {
    TextRange::new(
        TextSize::from(to_u32(value.at)),
        TextSize::from(to_u32(value.end)),
    )
}

#[cfg(test)]
mod tests;
