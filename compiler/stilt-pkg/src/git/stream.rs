//! A pack as a remote sends it (packages.fetching): its objects in order, each whole or a delta
//! against another, read without an index, and each named by the SHA-1 of its kind, size and
//! bytes, as git names objects.

use std::collections::HashMap;

use miniz_oxide::inflate::stream::{InflateState, inflate};
use miniz_oxide::{DataFormat, MZError, MZFlush, MZStatus};

use super::pack::apply;
use super::{Id, Kind, MAX_OBJECT, Objects};

/// The objects of a pack, by id.
#[derive(Debug, Default)]
pub(super) struct Loaded {
    objects: HashMap<Id, (Kind, Vec<u8>)>,
}

impl Loaded {
    /// How many objects the pack held.
    pub(super) fn count(&self) -> usize {
        self.objects.len()
    }
}

impl Objects for Loaded {
    fn object(&self, id: Id) -> Result<(Kind, Vec<u8>), String> {
        (self.objects.get(&id).cloned())
            .ok_or_else(|| format!("the repository sent no object {}", super::to_hex(&id)))
    }
}

/// The objects of the pack `pack`.
pub(super) fn read(pack: &[u8]) -> Result<Loaded, String> {
    let corrupt = || "the repository sent a corrupt pack".to_owned();
    if pack.get(..4) != Some(b"PACK") {
        return Err(corrupt());
    }
    let count = u32::from_be_bytes(pack.get(8..12).ok_or_else(corrupt)?.try_into().expect("4"));
    let mut loaded = Loaded::default();
    let mut by_offset: HashMap<usize, Id> = HashMap::new();
    let mut at = 12;
    for _ in 0..count {
        let start = at;
        let (kind, size) = header(pack, &mut at).ok_or_else(corrupt)?;
        let base = match kind {
            6 => {
                let back = offset(pack, &mut at).ok_or_else(corrupt)?;
                let id = start.checked_sub(back).and_then(|o| by_offset.get(&o));
                Some(*id.ok_or_else(corrupt)?)
            }
            7 => {
                let id: Id = pack
                    .get(at..at + 20)
                    .ok_or_else(corrupt)?
                    .try_into()
                    .expect("20");
                at += 20;
                Some(id)
            }
            _ => None,
        };
        let (data, used) =
            inflated(pack.get(at..).ok_or_else(corrupt)?, size).ok_or_else(corrupt)?;
        at += used;
        let (kind, data) = match base {
            Some(id) => {
                let (kind, base) = loaded.object(id)?;
                (kind, apply(&base, &data).ok_or_else(corrupt)?)
            }
            None => (whole(kind).ok_or_else(corrupt)?, data),
        };
        let id = named(kind, &data);
        by_offset.insert(start, id);
        loaded.objects.insert(id, (kind, data));
    }
    Ok(loaded)
}

/// An object's header: its type and its size, four bits then seven a byte.
fn header(pack: &[u8], at: &mut usize) -> Option<(u8, usize)> {
    let mut byte = *pack.get(*at)?;
    let kind = (byte >> 4) & 7;
    let mut size = usize::from(byte & 15);
    let mut shift = 4;
    while byte & 0x80 != 0 {
        *at += 1;
        byte = *pack.get(*at)?;
        size |= usize::from(byte & 0x7f).checked_shl(shift)?;
        shift += 7;
    }
    *at += 1;
    Some((kind, size))
}

/// How far back a delta's base starts, as an offset delta writes it.
fn offset(pack: &[u8], at: &mut usize) -> Option<usize> {
    let mut byte = *pack.get(*at)?;
    let mut back = usize::from(byte & 0x7f);
    while byte & 0x80 != 0 {
        *at += 1;
        byte = *pack.get(*at)?;
        back = ((back + 1) << 7) | usize::from(byte & 0x7f);
    }
    *at += 1;
    Some(back)
}

/// The `size` bytes that the zlib stream at the start of `input` holds, and how many bytes of
/// `input` it takes. The size is what the pack declares, so the buffer grows with what the
/// stream writes rather than starting at it: a few bytes can't claim a gigabyte.
fn inflated(input: &[u8], size: usize) -> Option<(Vec<u8>, usize)> {
    if size > MAX_OBJECT {
        return None;
    }
    let mut state = InflateState::new_boxed(DataFormat::Zlib);
    let mut out = vec![0; size.min(1 << 16) + 1];
    let (mut read, mut written) = (0, 0);
    loop {
        let result = inflate(
            &mut state,
            &input[read..],
            &mut out[written..],
            MZFlush::None,
        );
        read += result.bytes_consumed;
        written += result.bytes_written;
        match result.status {
            Ok(MZStatus::StreamEnd) if written == size => {
                out.truncate(size);
                return Some((out, read));
            }
            Ok(MZStatus::Ok) | Err(MZError::Buf) if written == out.len() && written <= size => {
                out.resize(out.len().saturating_mul(2).min(size + 1), 0);
            }
            Ok(MZStatus::Ok) if result.bytes_consumed + result.bytes_written > 0 => {}
            _ => return None,
        }
    }
}

fn whole(kind: u8) -> Option<Kind> {
    match kind {
        1 => Some(Kind::Commit),
        2 => Some(Kind::Tree),
        3 => Some(Kind::Blob),
        4 => Some(Kind::Tag),
        _ => None,
    }
}

/// The id git gives an object: the SHA-1 of `KIND SIZE\0` and its bytes.
fn named(kind: Kind, data: &[u8]) -> Id {
    let word = match kind {
        Kind::Commit => "commit",
        Kind::Tree => "tree",
        Kind::Blob => "blob",
        Kind::Tag => "tag",
    };
    let mut sha = sha1_smol::Sha1::new();
    sha.update(format!("{word} {}\0", data.len()).as_bytes());
    sha.update(data);
    sha.digest().bytes()
}
