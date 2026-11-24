//! The lines of a profile (builds.profile-form): one for each count that isn't 0,
//! `ADDRESS HASH KIND LINE:COL [CALLEE] COUNT`, in sorted order, each count rounded down to a
//! power of two, which merging adds and rounds down again.

use std::cmp::Ordering;
use std::ops::Range;

/// What a line counts.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Kind {
    Entry,
    Arm,
    Loop,
    Call,
}

impl Kind {
    fn name(self) -> &'static str {
        match self {
            Kind::Entry => "entry",
            Kind::Arm => "arm",
            Kind::Loop => "loop",
            Kind::Call => "call",
        }
    }

    fn named(name: &str) -> Option<Self> {
        Some(match name {
            "entry" => Kind::Entry,
            "arm" => Kind::Arm,
            "loop" => Kind::Loop,
            "call" => Kind::Call,
            _ => return None,
        })
    }
}

/// A line of a profile: a count of a body's, at a place relative to the body's start, its
/// first line being line 1, of a function reached for a call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Line {
    /// The body's address and hash (edits.body-addresses and edits.hash).
    pub(crate) address: String,
    pub(crate) hash: String,
    pub(crate) kind: Kind,
    /// The place, its line and column, relative to the body's start.
    pub(crate) place: (u32, u32),
    /// For a call, the address of the function it reaches.
    pub(crate) callee: Option<String>,
    pub(crate) count: u64,
}

impl Line {
    /// What the line counts, which two lines of one profile never share.
    fn key(&self) -> (&str, &str, u32, u32, Kind, Option<&str>) {
        (
            &self.address,
            &self.hash,
            self.place.0,
            self.place.1,
            self.kind,
            self.callee.as_deref(),
        )
    }

    /// The line's text, without its newline.
    pub(crate) fn text(&self) -> String {
        let callee = self
            .callee
            .as_ref()
            .map_or(String::new(), |c| format!(" {c}"));
        format!(
            "{} {} {} {}:{}{callee} {}",
            self.address,
            self.hash,
            self.kind.name(),
            self.place.0,
            self.place.1,
            self.count
        )
    }
}

/// The largest power of two that is at most `n`, or 0 for 0.
pub(crate) fn round_down(n: u64) -> u64 {
    if n == 0 { 0 } else { 1 << n.ilog2() }
}

/// A line of a profile that isn't of its form: its number, from 1, its bytes in the file, and
/// what is wrong with it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Malformed {
    pub(crate) number: usize,
    pub(crate) range: Range<usize>,
    pub(crate) reason: String,
}

/// The lines of a profile's text, or the first that isn't of the form.
pub(crate) fn parse(text: &str) -> Result<Vec<Line>, Malformed> {
    let mut lines = Vec::new();
    let mut start = 0;
    for (number, raw) in (1..).zip(text.split_inclusive('\n')) {
        let written = raw.strip_suffix('\n').unwrap_or(raw);
        let range = start..start + written.len();
        start += raw.len();
        let line = parse_line(written).map_err(|reason| Malformed {
            number,
            range,
            reason,
        })?;
        lines.push(line);
    }
    Ok(lines)
}

/// A line of the form, or what is wrong with it.
fn parse_line(text: &str) -> Result<Line, String> {
    let words: Vec<&str> = text.split(' ').collect();
    let (address, hash, kind, place) = match words.as_slice() {
        [a, h, k, p, _, ..] => (*a, *h, *k, *p),
        _ => return Err("it has fewer than five words".to_owned()),
    };
    let body = stilt_edit::Address::parse(address, false)
        .ok()
        .filter(|a| a.body && a.hash.is_none());
    if body.is_none() {
        return Err(format!("`{address}` isn't the address of a body"));
    }
    if hash.len() != 4
        || !hash
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(format!(
            "`{hash}` isn't a hash of four lowercase hexadecimal digits"
        ));
    }
    let kind = Kind::named(kind)
        .ok_or_else(|| format!("`{kind}` isn't `entry`, `arm`, `loop` or `call`"))?;
    let at = place
        .split_once(':')
        .and_then(|(l, c)| Some((number(l)?, number(c)?)))
        .ok_or_else(|| format!("`{place}` isn't a place `LINE:COL`"))?;
    let (callee, count) = match (kind, &words[4..]) {
        (Kind::Call, [callee, count]) => (Some(callee_address(callee)?), *count),
        (Kind::Call, _) => return Err("a `call` names its callee, then its count".to_owned()),
        (_, [count]) => (None, *count),
        (_, _) => return Err("only a `call` names a callee".to_owned()),
    };
    let count = number(count)
        .map(u64::from)
        .or_else(|| {
            count
                .parse::<u64>()
                .ok()
                .filter(|n| *n > 0 && no_sign(count))
        })
        .filter(|n| n.is_power_of_two())
        .ok_or_else(|| format!("`{count}` isn't a count, a power of two"))?;
    Ok(Line {
        address: address.to_owned(),
        hash: hash.to_owned(),
        kind,
        place: at,
        callee,
        count,
    })
}

/// The address of a function that a call reaches, as a line writes it.
fn callee_address(text: &str) -> Result<String, String> {
    match stilt_edit::Address::parse(text, false) {
        Ok(a) if !a.body && a.hash.is_none() => Ok(text.to_owned()),
        _ => Err(format!("`{text}` isn't the address of a function")),
    }
}

/// A number from 1 written in decimal digits alone, as a place's line and column are.
fn number(text: &str) -> Option<u32> {
    (no_sign(text) && !text.starts_with('0'))
        .then(|| text.parse().ok())
        .flatten()
}

fn no_sign(text: &str) -> bool {
    !text.is_empty() && text.bytes().all(|b| b.is_ascii_digit())
}

/// The lines of `old` with the counts of `new` added, each sum rounded down, and every line
/// in sorted order.
pub(crate) fn merge(old: Vec<Line>, new: Vec<Line>) -> Vec<Line> {
    let mut all = old;
    all.extend(new);
    all.sort_by(order);
    let mut merged: Vec<Line> = Vec::with_capacity(all.len());
    for line in all {
        match merged.last_mut() {
            Some(last) if last.key() == line.key() => {
                last.count = last.count.saturating_add(line.count);
            }
            _ => merged.push(line),
        }
    }
    for line in &mut merged {
        line.count = round_down(line.count);
    }
    merged.retain(|l| l.count > 0);
    merged
}

/// The order of a profile's lines: by body, then by place, then by what they count.
fn order(a: &Line, b: &Line) -> Ordering {
    a.key().cmp(&b.key())
}

/// A profile's text: its lines, sorted, each ended by a newline.
pub(crate) fn render(lines: &[Line]) -> String {
    let mut sorted: Vec<&Line> = lines.iter().collect();
    sorted.sort_by(|a, b| order(a, b));
    sorted.iter().fold(String::new(), |mut out, l| {
        out.push_str(&l.text());
        out.push('\n');
        out
    })
}
