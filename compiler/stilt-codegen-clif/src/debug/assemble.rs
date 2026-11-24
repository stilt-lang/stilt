//! The DWARF of a set of functions, put together from their pieces ([`super::piece`]): one
//! compile unit for the program, whose entries are each function's subprogram and locals, in
//! the order of the functions, then the types they show, its line table, whose sequences are
//! the functions', its location lists, its ranges and its call frames. A build writes only what
//! spans every function: the unit's header and entry, the line table's header, which lists the
//! program's files, the types and the ranges; the rest is each piece's bytes, with what it
//! leaves open filled in.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use cranelift_module::DataId;
use gimli::SectionId;
use gimli::constants as dw;
use gimli::write::{
    Address, CommonInformationEntry, DebugFrame, FrameDescriptionEntry, FrameTable, Sections,
    Writer,
};

use super::encode::{self, Bytes, Chunk, Patch};
use super::piece::{LINE_BASE, LINE_RANGE, OPCODE_BASE, Piece};
use super::sections::Relocating;
use super::types::Types;

/// What the DWARF of a set of functions needs beyond their pieces.
pub(crate) struct Unit<'a> {
    pub(crate) pieces: &'a [Arc<Piece>],
    /// The program's files, by the indices that locations give.
    pub(crate) files: &'a [PathBuf],
    /// The address of the start of each function's code, by its index in `pieces`.
    pub(crate) start: &'a dyn Fn(usize) -> Address,
    /// The address of each object of static data that a local's constant points to.
    pub(crate) data: &'a dyn Fn(DataId) -> Address,
    /// The common information of the target's call frames, which `.debug_frame` starts with.
    pub(crate) cie: Option<CommonInformationEntry>,
}

/// How a build fills in a place that a piece leaves open.
enum Fill {
    Address(Address),
    Word(u32),
    Offset(usize, SectionId),
}

/// The DWARF sections of `unit`, with section offsets written as they are when `plain_offsets`,
/// and otherwise relocated.
pub(crate) fn assemble(
    unit: &Unit<'_>,
    plain_offsets: bool,
) -> Result<Sections<Relocating>, String> {
    let failed = |e: gimli::write::Error| format!("cannot write the DWARF: {e}");
    let mut sections = Sections::new(Relocating::new(plain_offsets));
    (sections.debug_abbrev.0)
        .write(&encode::table())
        .map_err(failed)?;
    let locs = locations(unit, &mut sections.debug_loc.0).map_err(failed)?;
    info(unit, &locs, &mut sections.debug_info.0).map_err(failed)?;
    lines(unit, &mut sections.debug_line.0).map_err(failed)?;
    ranges(unit, &mut sections.debug_ranges.0).map_err(failed)?;
    if let Some(cie) = &unit.cie {
        frames(unit, cie, &mut sections.debug_frame.0).map_err(failed)?;
    }
    Ok(sections)
}

/// The address `offset` bytes after `address`.
fn after(address: Address, offset: i64) -> Address {
    match address {
        Address::Constant(a) => Address::Constant(a.wrapping_add_signed(offset)),
        Address::Symbol { symbol, addend } => Address::Symbol {
            symbol,
            addend: addend + offset,
        },
    }
}

/// Appends `chunk` to `w`, filling in each place it leaves open as `fill` gives it.
fn put(
    w: &mut Relocating,
    chunk: &Chunk,
    fill: impl Fn(Patch) -> Fill,
) -> gimli::write::Result<()> {
    let base = w.len();
    w.write(&chunk.bytes)?;
    for &(at, patch) in chunk.patches.iter() {
        let at = base + at as usize;
        match fill(patch) {
            Fill::Address(address) => w.address_at(at, address)?,
            Fill::Word(value) => w.write_udata_at(at, u64::from(value), 4)?,
            Fill::Offset(value, section) => w.write_offset_at(at, value, section, 4)?,
        }
    }
    Ok(())
}

/// What a piece's places that every section shares are filled in with: its code's address and
/// its data's.
fn common(unit: &Unit<'_>, i: usize, patch: Patch) -> Fill {
    match patch {
        Patch::Code(addend) => Fill::Address(after((unit.start)(i), addend)),
        Patch::Data(k) => {
            let data = unit.pieces[i].data.get(k as usize).copied();
            Fill::Address(data.map_or(Address::Constant(0), unit.data))
        }
        Patch::Cie => Fill::Offset(0, SectionId::DebugFrame),
        Patch::Type(_) | Patch::Loc(_) => Fill::Word(0),
    }
}

/// The location lists of every piece, one after the other: the offset of each piece's.
fn locations(unit: &Unit<'_>, w: &mut Relocating) -> gimli::write::Result<Vec<usize>> {
    let mut bases = Vec::with_capacity(unit.pieces.len());
    for (i, piece) in unit.pieces.iter().enumerate() {
        bases.push(w.len());
        put(w, &piece.loc, |p| common(unit, i, p))?;
    }
    Ok(bases)
}

/// The unit: its header and entry, each piece's entries, then the types they name.
fn info(unit: &Unit<'_>, locs: &[usize], w: &mut Relocating) -> gimli::write::Result<()> {
    let main = unit.files.first().map_or_else(PathBuf::new, Clone::clone);
    let mut head = Bytes::default();
    head.uleb(encode::UNIT);
    head.string("stilt");
    // No language code is Stilt's: C's makes debuggers show words as plain values.
    head.u16(dw::DW_LANG_C99.0);
    head.string(&main.to_string_lossy());
    head.string(&directory(&main));
    // The header's 11 bytes, then the entry, its line table, low address and ranges last.
    let entry = 11 + head.len();
    let functions: usize = unit.pieces.iter().map(|p| p.info.bytes.len()).sum();
    let mut types = Types::new(u32::try_from(entry + 16 + functions).unwrap_or(u32::MAX));
    let offsets: Vec<Vec<u32>> = (unit.pieces.iter())
        .map(|p| p.types.iter().map(|t| types.of(t)).collect())
        .collect();
    w.write_u32(0)?;
    w.write_u16(encode::VERSION)?;
    w.write_offset(0, SectionId::DebugAbbrev, 4)?;
    w.write_u8(8)?;
    w.write(&head.0)?;
    w.write_offset(0, SectionId::DebugLine, 4)?;
    w.write_u64(0)?;
    w.write_offset(0, SectionId::DebugRanges, 4)?;
    for (i, piece) in unit.pieces.iter().enumerate() {
        put(w, &piece.info, |p| match p {
            Patch::Type(k) => Fill::Word(offsets[i].get(k as usize).copied().unwrap_or(0)),
            Patch::Loc(at) => Fill::Offset(locs[i] + at as usize, SectionId::DebugLoc),
            _ => common(unit, i, p),
        })?;
    }
    w.write(&types.out.0)?;
    w.write_u8(0)?;
    let length = u64::try_from(w.len() - 4).unwrap_or(0);
    w.write_udata_at(0, length, 4)
}

fn directory(path: &Path) -> String {
    path.parent()
        .map_or_else(String::new, |d| d.to_string_lossy().into_owned())
}

/// The line table: its header, which lists the program's files, then each piece's sequence.
fn lines(unit: &Unit<'_>, w: &mut Relocating) -> gimli::write::Result<()> {
    let main = unit.files.first().map_or_else(PathBuf::new, Clone::clone);
    let comp_dir = directory(&main);
    let mut directories: Vec<String> = Vec::new();
    let mut files = Bytes::default();
    for path in unit.files {
        let dir = directory(path);
        let index = if dir == comp_dir {
            0
        } else if let Some(i) = directories.iter().position(|d| *d == dir) {
            i + 1
        } else {
            directories.push(dir);
            directories.len()
        };
        let name = path.file_name().map_or_else(
            || "main.lt".to_owned(),
            |n| n.to_string_lossy().into_owned(),
        );
        files.string(&name);
        files.uleb(index as u64);
        files.uleb(0);
        files.uleb(0);
    }
    files.u8(0);
    let mut header = Bytes::default();
    // The least instruction, the operations of one, whether rows start statements.
    header.0.extend_from_slice(&[1, 1, 1]);
    header.0.extend(LINE_BASE.to_le_bytes());
    header.0.extend_from_slice(&[LINE_RANGE, OPCODE_BASE]);
    header
        .0
        .extend_from_slice(&[0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1]);
    for dir in &directories {
        header.string(dir);
    }
    header.u8(0);
    header.0.extend_from_slice(&files.0);
    w.write_u32(0)?;
    w.write_u16(encode::VERSION)?;
    w.write_u32(u32::try_from(header.len()).unwrap_or(0))?;
    w.write(&header.0)?;
    for (i, piece) in unit.pieces.iter().enumerate() {
        put(w, &piece.line, |p| common(unit, i, p))?;
    }
    let length = u64::try_from(w.len() - 4).unwrap_or(0);
    w.write_udata_at(0, length, 4)
}

/// The unit's ranges: each function's code.
fn ranges(unit: &Unit<'_>, w: &mut Relocating) -> gimli::write::Result<()> {
    for (i, piece) in unit.pieces.iter().enumerate() {
        let start = (unit.start)(i);
        w.write_address(start, 8)?;
        w.write_address(after(start, i64::from(piece.size)), 8)?;
    }
    w.write_u64(0)?;
    w.write_u64(0)
}

/// The call frames: the common information entry, then each piece's description of its frame.
fn frames(
    unit: &Unit<'_>,
    cie: &CommonInformationEntry,
    w: &mut Relocating,
) -> gimli::write::Result<()> {
    let mut table = FrameTable::default();
    let id = table.add_cie(cie.clone());
    table.add_fde(id, FrameDescriptionEntry::new(Address::Constant(0), 0));
    let mut first = DebugFrame(Relocating::new(true));
    table.write_debug_frame(&mut first)?;
    let all = first.0.data.slice();
    let length = all
        .get(..4)
        .and_then(|b| b.try_into().ok())
        .map(u32::from_le_bytes);
    let end = 4 + length.unwrap_or(0) as usize;
    w.write(all.get(..end).unwrap_or_default())?;
    for (i, piece) in unit.pieces.iter().enumerate() {
        put(w, &piece.frame, |p| common(unit, i, p))?;
    }
    Ok(())
}
