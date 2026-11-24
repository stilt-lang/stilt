//! Where a profile's counts are: the bodies of the program's own files (edits.bodies), each
//! with its address, its hash and the place it starts, which turn the location words of what
//! a profiled run counts into lines, each place relative to its body's start, and a profile's
//! lines back into the location words that a release build's marks hold.

use stilt_db::{Database, Program};
use stilt_diag::LineIndex;
use stilt_mir::mir::Counted;
use stilt_runtime::profile as counts;

use super::lines::{Kind, Line};
use stilt_ide::show::parts::FileParts;

/// A body of the program: its address and hash, its file's index, the places, line and
/// column, where it starts and where it ends, and the place of its declaration's name, where
/// lowering marks its entry.
#[derive(Clone, Debug)]
pub(crate) struct Body {
    pub(crate) address: String,
    pub(crate) hash: String,
    file: u32,
    start: (u32, u32),
    end: (u32, u32),
    named: (u32, u32),
}

impl Body {
    /// The location word of a place of the body, given as a profile's line gives it.
    pub(crate) fn word(&self, line: u32, col: u32) -> u64 {
        location(self.file, self.start.0 + line - 1, col)
    }

    /// The location word of the body's entry, which lowering marks at its declaration's name,
    /// and a profile counts at the body's start.
    pub(crate) fn entry(&self) -> u64 {
        location(self.file, self.named.0, self.named.1)
    }
}

/// The location word of a place, as `stilt_runtime::location` reads it.
fn location(file: u32, line: u32, col: u32) -> u64 {
    u64::from(file) << 44 | (u64::from(line) & 0xff_ffff) << 20 | u64::from(col) & 0xf_ffff
}

/// The bodies of the program's own files.
#[derive(Debug, Default)]
pub(crate) struct Bodies {
    pub(crate) all: Vec<Body>,
}

impl Bodies {
    pub(crate) fn of(db: &Database, program: Program) -> Self {
        let mut all = Vec::new();
        for (index, &file) in (0..).zip(program.files(db)) {
            let parts = FileParts::of(db, program, file);
            let lines = LineIndex::new(&parts.text);
            let at = |offset: usize| {
                let p = lines.position(&parts.text, u32::try_from(offset).unwrap_or(0).into());
                (p.line, p.col)
            };
            for (i, part) in parts.parts.iter().enumerate() {
                if part.body && !part.broken {
                    all.push(Body {
                        address: part.address(),
                        hash: parts.hash(i),
                        file: index,
                        start: at(part.extent.start),
                        end: at(part.extent.end),
                        named: at(parts.parts[part.decl].name.start),
                    });
                }
            }
        }
        Self { all }
    }

    /// The body that holds the place of a location word.
    fn holding(&self, word: u64) -> Option<&Body> {
        let file = u32::try_from(word >> 44 & 0xffff).ok()?;
        let place = (
            u32::try_from(word >> 20 & 0xff_ffff).ok()?,
            u32::try_from(word & 0xf_ffff).ok()?,
        );
        self.all
            .iter()
            .find(|b| b.file == file && b.start <= place && place < b.end)
    }

    /// The body at an address, as it is now.
    pub(crate) fn at(&self, address: &str) -> Option<&Body> {
        self.all.iter().find(|b| b.address == address)
    }

    /// A profiled run's counts as a profile's lines, each place in the body that holds it,
    /// relative to its start: none for a place outside every body of the program's files.
    pub(crate) fn lines(&self, counted: &[(counts::Counted, u64)]) -> Vec<Line> {
        counted
            .iter()
            .filter_map(|(c, n)| {
                let kind = match c.kind {
                    counts::ENTRY => Kind::Entry,
                    counts::ARM => Kind::Arm,
                    counts::LOOP => Kind::Loop,
                    _ => Kind::Call,
                };
                let (body, line, col) = if kind == Kind::Entry {
                    let body = self.all.iter().find(|b| b.entry() == c.at)?;
                    (body, 1, body.start.1)
                } else {
                    let body = self.holding(c.at)?;
                    let line = u32::try_from(c.at >> 20 & 0xff_ffff).ok()? - body.start.0 + 1;
                    (body, line, u32::try_from(c.at & 0xf_ffff).ok()?)
                };
                Some(Line {
                    address: body.address.clone(),
                    hash: body.hash.clone(),
                    kind,
                    place: (line, col),
                    callee: c.callee.clone(),
                    count: *n,
                })
            })
            .collect()
    }
}

/// What a mark of the MIR counts, for a line that counts what a mark marks.
pub(crate) fn counted(kind: Kind) -> Option<Counted> {
    match kind {
        Kind::Entry => Some(Counted::Entry),
        Kind::Arm => Some(Counted::Arm),
        Kind::Loop => Some(Counted::Loop),
        Kind::Call => None,
    }
}
