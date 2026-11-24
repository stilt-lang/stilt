//! An entry of `[dependencies]`: its keys, the forms of their values, and how they combine
//! (packages.dependencies and packages.grants; facts.capability-grants).

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_syntax::{TextRange, TextSize};

use stilt_syntax::capability::Capability;

use super::{Entry, Fill, Grant, Pinned, Reader, Source, range, to_u32};
use crate::toml::{Defined, Table, Value, ValueKind};

/// The keys of an entry that the reader found well formed.
#[derive(Default)]
struct Keys {
    path: Option<String>,
    from: Option<String>,
    version: Option<Pinned>,
    hash: Option<Pinned>,
    may: Grant,
    may_at: Option<TextRange>,
}

impl Reader<'_> {
    /// The entry `name`, whose key is at `key`, from its table.
    pub(super) fn entry(&mut self, name: &str, key: TextRange, fields: &Table) -> Entry {
        let before = self.out.problems.len();
        let mut keys = Keys::default();
        for e in &fields.entries {
            let value = &e.value;
            match e.key.as_str() {
                "path" => keys.path = self.string(value, "`path`", is_path, "a relative path"),
                "from" => keys.from = self.string(value, "`from`", is_from, "a git repository"),
                "version" => keys.version = self.pinned(value, "`version`", is_version),
                "hash" => keys.hash = self.pinned(value, "`hash`", is_hash),
                "may" => (keys.may, keys.may_at) = (self.may(value), Some(range(value))),
                other => {
                    let message = format!("a dependency's entry has no key `{other}`");
                    self.problem(self.key(e.at), message);
                }
            }
        }
        let fill = fill(name, fields);
        let mut source = None;
        if self.out.problems.len() == before {
            match combination(&keys) {
                Ok(found) => source = Some(found),
                Err(message) => {
                    let message = format!("the entry `{name}` {message}");
                    self.problem(key, message);
                }
            }
        }
        Entry {
            name: name.to_owned(),
            key,
            source,
            may: keys.may,
            may_at: keys.may_at,
            fill,
        }
    }

    /// A string value of the form `ok` checks, named `what`, or `None` after its error.
    fn string(
        &mut self,
        value: &Value,
        what: &str,
        ok: fn(&str) -> bool,
        form: &str,
    ) -> Option<String> {
        match &value.kind {
            ValueKind::String(s) if ok(s) => Some(s.clone()),
            ValueKind::String(s) => {
                let message = format!("`{s}` isn't {form}");
                self.problem(range(value), message);
                None
            }
            other => {
                self.wrong(what, "a string", other, value);
                None
            }
        }
    }

    fn pinned(&mut self, value: &Value, what: &str, ok: fn(&str) -> bool) -> Option<Pinned> {
        let form = if what == "`version`" {
            "a version: three decimal numbers without leading zeros, as `1.4.0`"
        } else {
            "a content hash: `b3:` and 64 lowercase hexadecimal digits"
        };
        let found = self.string(value, what, ok, form)?;
        Some(Pinned {
            value: found,
            at: range(value),
        })
    }

    /// `may`, a list of what is granted: `io`, or capabilities (facts.capability-grants),
    /// and `unsafe` (c.granting-unsafe). Any other string, a string listed twice, and `io` listed
    /// with a capability are errors.
    fn may(&mut self, value: &Value) -> Grant {
        let ValueKind::Array(granted) = &value.kind else {
            self.wrong("`may`", "a list of strings", &value.kind, value);
            return Grant::default();
        };
        let mut grant = Grant::default();
        let mut seen: Vec<&str> = Vec::new();
        for g in granted {
            let ValueKind::String(s) = &g.kind else {
                self.wrong("an effect", "a string", &g.kind, g);
                continue;
            };
            let capability = Capability::named(s);
            let unsafe_code = s == "unsafe";
            // The capability that `io` would be listed with, if it would be.
            let beside = match capability {
                Some(c) if grant.io => Some(c),
                None if s == "io" => grant.capabilities.iter().next(),
                _ => None,
            };
            if s != "io" && !unsafe_code && capability.is_none() {
                let message = format!(
                    "`{s}` isn't an effect, a capability or `unsafe`, which a manifest grants"
                );
                let fix = Fix::new("grant `io`", vec![Edit::replace(range(g), "\"io\"")]);
                let d = Diagnostic::new(codes::E0600, range(g), message).with_fix(fix);
                self.out.problems.push(d);
            } else if seen.contains(&s.as_str()) {
                self.problem(range(g), format!("`{s}` is granted twice"));
            } else if let Some(c) = beside {
                let message = format!(
                    "`io` grants every capability, so it isn't listed with `{}`",
                    c.text()
                );
                self.problem(range(g), message);
            } else if unsafe_code {
                grant.unsafe_code = true;
            } else if let Some(c) = capability {
                grant.capabilities = grant.capabilities.with(c);
            } else {
                grant.io = true;
            }
            seen.push(s);
        }
        grant
    }
}

/// The source that the keys give, or why they don't combine (packages.dependencies).
fn combination(keys: &Keys) -> Result<Source, &'static str> {
    match (&keys.path, &keys.from) {
        (Some(_), Some(_)) => Err("has both `path` and `from`"),
        (None, None) => Err("has neither `path` nor `from`"),
        (Some(_), None) if keys.version.is_some() => Err("has a `version`, which goes with `from`"),
        (Some(_), None) if keys.hash.is_some() => Err("has a `hash`, which goes with `from`"),
        (Some(path), None) => Ok(Source::Path(path.clone())),
        (None, Some(_)) if keys.hash.is_some() && keys.version.is_none() => {
            Err("has a `hash` without the `version` it pins")
        }
        (None, Some(from)) => Ok(Source::From {
            from: from.clone(),
            version: keys.version.clone(),
            hash: keys.hash.clone(),
        }),
    }
}

/// Where the keys that the entry lacks go.
fn fill(name: &str, fields: &Table) -> Fill {
    let end = TextSize::from(to_u32(fields.end));
    match fields.defined {
        Defined::Inline => Fill::Inline(end),
        Defined::Dotted => Fill::Lines(end, format!("{name}.")),
        Defined::Header | Defined::Implicitly => Fill::Lines(end, String::new()),
    }
}

fn is_path(s: &str) -> bool {
    !s.is_empty() && !s.starts_with('/') && !s.contains('\\')
}

/// `HOST/PATH`, whose host may give a port, as `HOST:PORT`, or a `file://` URL of an absolute
/// path.
fn is_from(s: &str) -> bool {
    if let Some(path) = s.strip_prefix("file://") {
        return path.starts_with('/') && path.len() > 1;
    }
    let Some((authority, path)) = s.split_once('/') else {
        return false;
    };
    let (host, port) = authority.split_once(':').unwrap_or((authority, "0"));
    !host.is_empty()
        && host
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'.' || b == b'-')
        && !port.is_empty()
        && port.bytes().all(|b| b.is_ascii_digit())
        && path.split('/').all(|segment| {
            !segment.is_empty()
                && !segment
                    .chars()
                    .any(|c| c.is_whitespace() || "\\?#".contains(c))
        })
}

/// `MAJOR.MINOR.PATCH`: three decimal numbers without leading zeros.
pub(crate) fn is_version(s: &str) -> bool {
    let parts: Vec<&str> = s.split('.').collect();
    parts.len() == 3
        && parts.iter().all(|p| {
            !p.is_empty()
                && p.bytes().all(|b| b.is_ascii_digit())
                && (p.len() == 1 || !p.starts_with('0'))
                && p.parse::<u64>().is_ok()
        })
}

/// `b3:` and 64 lowercase hexadecimal digits.
fn is_hash(s: &str) -> bool {
    s.strip_prefix("b3:").is_some_and(|hex| {
        hex.len() == 64
            && hex
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    })
}
