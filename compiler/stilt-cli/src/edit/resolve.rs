//! What each edit of a command names and whether it may apply (edits.command-line, edits.new-text,
//! edits.refusals and edits.all-or-nothing): every edit is checked against the files as they are,
//! before any applies.

use stilt_diag::{Code, codes};
use stilt_edit::{Address, Kind, Syntax, check_text};

use super::load::Loaded;

/// An edit as the command line gives it.
#[derive(Clone, Debug)]
pub(crate) struct Raw {
    /// Its address as written.
    pub(crate) at: String,
    /// Its text as written: `-` for standard input.
    pub(crate) text: String,
}

/// The part an edit replaces.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Target {
    pub(crate) file: usize,
    pub(crate) part: usize,
}

/// Why an edit is refused, with what its rendering needs.
#[derive(Clone, Debug)]
pub(crate) enum Why {
    /// The address is malformed, or reads standard input again: the reason, and the span of
    /// the address it is about.
    Malformed(String, std::ops::Range<usize>),
    /// No part has the address.
    Missing,
    /// Two parts have the address and its hash.
    Ambiguous(Target, Target),
    /// The hash is not the current one of the part, whose current hash is `now`.
    Stale { given: String, target: Target },
    /// The text isn't the part.
    Text(Option<Syntax>),
    /// Edit `other` changes the same code, which is the edit with this index.
    Overlap(usize),
}

/// A refused edit.
#[derive(Clone, Debug)]
pub(crate) struct Refusal {
    pub(crate) code: Code,
    pub(crate) why: Why,
    /// The part's address with its current hash, when one part has the edit's path.
    pub(crate) now: Option<String>,
}

/// An edit that may apply: its target and its new text.
#[derive(Clone, Debug)]
pub(crate) struct Ready {
    pub(crate) target: Target,
    pub(crate) text: String,
}

/// Resolves the edits against the loaded files. `stdin` is the text that `-` stands for, and
/// `Err` for a second `-`.
pub(crate) fn resolve(loaded: &Loaded, raws: &[Raw], stdin: &str) -> Vec<Result<Ready, Refusal>> {
    let mut read = false;
    let mut found: Vec<Result<Ready, Refusal>> = raws
        .iter()
        .map(|raw| {
            let text = if raw.text == "-" {
                if std::mem::replace(&mut read, true) {
                    let why = Why::Malformed("reads standard input again".to_owned(), 0..0);
                    return Err(Refusal {
                        code: codes::E0700,
                        why,
                        now: None,
                    });
                }
                stdin.to_owned()
            } else {
                raw.text.clone()
            };
            one(loaded, &raw.at, text)
        })
        .collect();
    overlaps(loaded, &mut found);
    found
}

fn refuse(code: Code, why: Why, now: Option<String>) -> Refusal {
    Refusal { code, why, now }
}

/// Resolves one edit.
fn one(loaded: &Loaded, at: &str, text: String) -> Result<Ready, Refusal> {
    let address = Address::parse(at, true)
        .map_err(|m| refuse(codes::E0700, Why::Malformed(m.reason, m.at), None))?;
    let given = address.hash.clone().unwrap_or_default();
    let hits = loaded.find(&format!(
        "{}{}",
        address.path,
        if address.body { "/body" } else { "" }
    ));
    let now = |t: Target| Some(loaded.files[t.file].address(t.part));
    let target = |&(file, part): &(usize, usize)| Target { file, part };
    let [first, ..] = hits.as_slice() else {
        return Err(refuse(codes::E0701, Why::Missing, None));
    };
    let current = |t: Target| loaded.files[t.file].hash(t.part);
    let matching: Vec<Target> = hits
        .iter()
        .map(target)
        .filter(|&t| current(t) == given)
        .collect();
    let chosen = match matching.as_slice() {
        [t] => *t,
        [a, b, ..] => {
            return Err(refuse(codes::E0702, Why::Ambiguous(*a, *b), None));
        }
        [] => {
            let t = target(first);
            let single = hits.len() == 1;
            let why = Why::Stale { given, target: t };
            return Err(refuse(codes::E0703, why, single.then(|| now(t)).flatten()));
        }
    };
    let part = &loaded.files[chosen.file].parts[chosen.part];
    check_text(part, &text).map_err(|syntax| {
        let single = hits.len() == 1;
        refuse(
            codes::E0704,
            Why::Text(syntax),
            single.then(|| now(chosen)).flatten(),
        )
    })?;
    Ok(Ready {
        target: chosen,
        text,
    })
}

/// Refuses every edit that changes the same code as another: both address one part, or one
/// addresses a declaration and the other its body, or a trait and one of its methods
/// (edits.refusals).
fn overlaps(loaded: &Loaded, found: &mut [Result<Ready, Refusal>]) {
    let ready: Vec<(usize, Target)> = found
        .iter()
        .enumerate()
        .filter_map(|(i, r)| r.as_ref().ok().map(|r| (i, r.target)))
        .collect();
    let extent = |t: Target| &loaded.files[t.file].parts[t.part].extent;
    let mut clash = vec![None; found.len()];
    for (n, &(i, a)) in ready.iter().enumerate() {
        for &(j, b) in &ready[n + 1..] {
            let (ea, eb) = (extent(a), extent(b));
            if a.file == b.file && ea.start < eb.end && eb.start < ea.end {
                clash[i].get_or_insert(j);
                clash[j].get_or_insert(i);
            }
        }
    }
    for (i, other) in clash.into_iter().enumerate() {
        if let Some(other) = other {
            let target = found[i].as_ref().ok().map(|r| r.target);
            let now = target.map(|t| loaded.files[t.file].address(t.part));
            found[i] = Err(refuse(codes::E0705, Why::Overlap(other), now));
        }
    }
}

/// The word for a kind of declaration.
pub(crate) fn kind_name(kind: Kind) -> &'static str {
    match kind {
        Kind::Fn => "function",
        Kind::Type => "type",
        Kind::Trait => "trait",
        Kind::Const => "constant",
        Kind::Test => "test",
        Kind::Macro => "macro",
        Kind::Effect => "effect",
    }
}
