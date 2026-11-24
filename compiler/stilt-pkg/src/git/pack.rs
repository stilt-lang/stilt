//! Packs: the files in which git keeps objects compressed together, each found through its
//! index (version 2), and stored whole or as a delta against another object.

use std::fs;
use std::path::Path;

use super::{Bases, Id, Kind, MAX_OBJECT, inflate};

/// How long a chain of deltas may be: git's own limit, which `git repack --depth` can't pass.
pub(super) const MAX_DEPTH: usize = 4095;

/// Where an index of version 2 lists its objects' ids, after its header and fan-out table.
const IDS: usize = 8 + 256 * 4;

/// A pack and its index.
#[derive(Debug)]
pub(super) struct Pack {
    index: Vec<u8>,
    data: Vec<u8>,
}

impl Pack {
    /// The packs in a repository's `objects/pack`.
    pub(super) fn all(dir: &Path) -> Result<Vec<Self>, String> {
        let Ok(entries) = fs::read_dir(dir) else {
            return Ok(Vec::new());
        };
        let mut packs = Vec::new();
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().is_some_and(|e| e == "idx") {
                let read =
                    |p: &Path| fs::read(p).map_err(|e| format!("cannot read {}: {e}", p.display()));
                let index = read(&path)?;
                let data = read(&path.with_extension("pack"))?;
                packs.push(Self::new(index, data).ok_or_else(|| {
                    format!("{} isn't a pack index of version 2", path.display())
                })?);
            }
        }
        Ok(packs)
    }

    /// The pack `data` with its index, when the index is one of version 2 long enough for the
    /// objects its fan-out table counts.
    pub(super) fn new(index: Vec<u8>, data: Vec<u8>) -> Option<Self> {
        if index.get(..8)? != [0xff, b't', b'O', b'c', 0, 0, 0, 2] {
            return None;
        }
        let pack = Self { index, data };
        let count = pack.count()?;
        // Each object's id, checksum and offset, then the two checksums of the pack and index.
        let least = count.checked_mul(20 + 4 + 4)?.checked_add(IDS + 40)?;
        (pack.index.len() >= least).then_some(pack)
    }

    fn word(&self, at: usize) -> Option<usize> {
        let bytes: [u8; 4] = self.index.get(at..at.checked_add(4)?)?.try_into().ok()?;
        Some(u32::from_be_bytes(bytes) as usize)
    }

    /// How many objects the index lists.
    pub(super) fn count(&self) -> Option<usize> {
        self.word(8 + 4 * 255)
    }

    /// The id of the `i`th object the index lists.
    pub(super) fn id(&self, i: usize) -> Option<Id> {
        let at = IDS.checked_add(i.checked_mul(20)?)?;
        self.index.get(at..at.checked_add(20)?)?.try_into().ok()
    }

    /// The offset in the pack of the object `id`, if the pack holds it.
    pub(super) fn find(&self, id: &Id) -> Option<usize> {
        let fanout = |i: usize| self.word(8 + 4 * i);
        let count = self.count()?;
        let first = usize::from(id[0]);
        let (mut low, mut high) = (
            if first == 0 { 0 } else { fanout(first - 1)? },
            fanout(first)?.min(count),
        );
        while low < high {
            let mid = usize::midpoint(low, high);
            match self.id(mid)?.cmp(id) {
                std::cmp::Ordering::Less => low = mid + 1,
                std::cmp::Ordering::Greater => high = mid,
                std::cmp::Ordering::Equal => return self.offset(count, mid),
            }
        }
        None
    }

    fn offset(&self, count: usize, i: usize) -> Option<usize> {
        let offsets = IDS + 24 * count;
        let small = self.word(offsets + 4 * i)?;
        if small & 0x8000_0000 == 0 {
            return Some(small);
        }
        let at = offsets + 4 * count + 8 * (small & 0x7fff_ffff);
        let bytes: [u8; 8] = self.index.get(at..at + 8)?.try_into().ok()?;
        usize::try_from(u64::from_be_bytes(bytes)).ok()
    }

    /// The object at `offset`, with its deltas applied, whose bases `bases` finds by id. A
    /// chain of deltas is followed down to its whole object, then applied back up, so a
    /// chain's length costs memory for its deltas, not stack.
    pub(super) fn read(&self, offset: usize, bases: &dyn Bases) -> Result<(Kind, Vec<u8>), String> {
        let corrupt = || "a corrupt pack".to_owned();
        let (mut pack, mut offset) = (self, offset);
        let mut deltas = Vec::new();
        let (kind, mut data) = loop {
            if deltas.len() > MAX_DEPTH {
                return Err(format!(
                    "a pack whose deltas chain more than {MAX_DEPTH} deep"
                ));
            }
            let (kind, at, base) = pack.entry(offset).ok_or_else(corrupt)?;
            let data = inflate(pack.data.get(at..).ok_or_else(corrupt)?)?;
            match base {
                Base::None => break (whole(kind).ok_or_else(corrupt)?, data),
                Base::Back(base) => offset = base,
                Base::Id(id) => match bases.find(id)? {
                    Found::Packed(other, at) => (pack, offset) = (other, at),
                    Found::Whole(kind, base) => {
                        deltas.push(data);
                        break (kind, base);
                    }
                },
            }
            deltas.push(data);
        };
        for delta in deltas.iter().rev() {
            data = apply(&data, delta).ok_or_else(corrupt)?;
        }
        Ok((kind, data))
    }

    /// The entry at `offset`: its kind, where its compressed bytes start, and its base.
    fn entry(&self, offset: usize) -> Option<(u8, usize, Base)> {
        let mut at = offset;
        let mut byte = *self.data.get(at)?;
        let kind = (byte >> 4) & 7;
        while byte & 0x80 != 0 {
            at += 1;
            byte = *self.data.get(at)?;
        }
        at += 1;
        let base = match kind {
            6 => {
                let mut byte = *self.data.get(at)?;
                let mut back = usize::from(byte & 0x7f);
                while byte & 0x80 != 0 {
                    at += 1;
                    byte = *self.data.get(at)?;
                    back = back.checked_add(1)?.checked_mul(128)? | usize::from(byte & 0x7f);
                }
                at += 1;
                // A base starts before its delta: a distance of 0 would be the delta itself.
                Base::Back(offset.checked_sub(back).filter(|_| back > 0)?)
            }
            7 => {
                let id: Id = self.data.get(at..at + 20)?.try_into().ok()?;
                at += 20;
                Base::Id(id)
            }
            _ => Base::None,
        };
        Some((kind, at, base))
    }
}

/// What an entry of a pack is a delta against.
enum Base {
    None,
    Back(usize),
    Id(Id),
}

/// Where an object is: at an offset of a pack, or whole, read from elsewhere.
pub(super) enum Found<'a> {
    Packed(&'a Pack, usize),
    Whole(Kind, Vec<u8>),
}

/// The kind of an entry stored whole.
fn whole(kind: u8) -> Option<Kind> {
    match kind {
        1 => Some(Kind::Commit),
        2 => Some(Kind::Tree),
        3 => Some(Kind::Blob),
        4 => Some(Kind::Tag),
        _ => None,
    }
}

/// A size as a delta writes it: seven bits a byte, least significant first.
fn size(delta: &[u8], at: &mut usize) -> Option<usize> {
    let (mut value, mut shift) = (0, 0);
    loop {
        let byte = *delta.get(*at)?;
        *at += 1;
        value |= usize::from(byte & 0x7f).checked_shl(shift)?;
        shift += 7;
        if byte & 0x80 == 0 {
            return Some(value);
        }
    }
}

/// The object that `delta` makes of `base`: copies from the base and inserted bytes.
pub(super) fn apply(base: &[u8], delta: &[u8]) -> Option<Vec<u8>> {
    let mut at = 0;
    if size(delta, &mut at)? != base.len() {
        return None;
    }
    let target = size(delta, &mut at)?;
    if target > MAX_OBJECT {
        return None;
    }
    // The size a delta declares bounds what it may write, not what it holds: reserve no more
    // than its own bytes could make before writing them.
    let mut out = Vec::with_capacity(target.min(delta.len().saturating_mul(16)));
    while at < delta.len() {
        let op = delta[at];
        at += 1;
        if op & 0x80 == 0 {
            let n = usize::from(op);
            out.extend_from_slice(delta.get(at..at + n)?);
            at += n;
            if out.len() > target {
                return None;
            }
            continue;
        }
        let mut field = |bits: u8, count: usize| -> Option<usize> {
            let mut value = 0;
            for i in 0..count {
                if bits & (1 << i) != 0 {
                    value |= usize::from(*delta.get(at)?) << (8 * i);
                    at += 1;
                }
            }
            Some(value)
        };
        let offset = field(op, 4)?;
        let length = match field(op >> 4, 3)? {
            0 => 0x10000,
            n => n,
        };
        out.extend_from_slice(base.get(offset..offset + length)?);
        if out.len() > target {
            return None;
        }
    }
    (out.len() == target).then_some(out)
}
