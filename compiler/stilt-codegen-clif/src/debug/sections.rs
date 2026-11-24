//! Writing DWARF sections: into the object of `stilt build`, with the relocations a linker
//! applies, or with every address known, for the JIT's images.

use std::path::PathBuf;
use std::sync::Arc;

use cranelift_module::DataId;
use cranelift_object::ObjectProduct;
use gimli::write::{Address, CommonInformationEntry, EndianVec, Sections, Writer};
use gimli::{LittleEndian, SectionId};
use object::write::{Object, Relocation, StandardSegment, SymbolId, SymbolSection};
use object::{BinaryFormat, RelocationEncoding, RelocationFlags, RelocationKind, SectionKind};

use super::assemble::{Unit, assemble};
use super::piece::Piece;
pub(crate) use placing::Placing;

mod placing;

/// A section's bytes, and the relocations its addresses and offsets need.
#[derive(Clone, Debug)]
pub(crate) struct Relocating {
    pub(crate) data: EndianVec<LittleEndian>,
    pub(crate) relocations: Vec<(usize, u8, Target, i64)>,
    /// Whether offsets into other sections are written as they are, as Mach-O's linker, which
    /// leaves DWARF in the objects, needs, rather than relocated, as ELF's, which joins it.
    plain_offsets: bool,
}

/// What a relocation is against: a symbol, by its index among the functions of the facts and
/// then the data their locals point into, or the start of a DWARF section.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Target {
    Function(usize),
    Section(SectionId),
}

impl Relocating {
    pub(crate) fn new(plain_offsets: bool) -> Self {
        Self {
            data: EndianVec::new(LittleEndian),
            relocations: Vec::new(),
            plain_offsets,
        }
    }

    /// Writes `address` over the 8 zero bytes at `offset`, or relocates them against it.
    pub(crate) fn address_at(
        &mut self,
        offset: usize,
        address: Address,
    ) -> gimli::write::Result<()> {
        match address {
            Address::Constant(value) => self.data.write_udata_at(offset, value, 8),
            Address::Symbol { symbol, addend } => {
                self.relocations
                    .push((offset, 8, Target::Function(symbol), addend));
                Ok(())
            }
        }
    }
}

impl Writer for Relocating {
    type Endian = LittleEndian;

    fn endian(&self) -> LittleEndian {
        LittleEndian
    }

    fn len(&self) -> usize {
        self.data.len()
    }

    fn write(&mut self, bytes: &[u8]) -> gimli::write::Result<()> {
        self.data.write(bytes)
    }

    fn write_at(&mut self, offset: usize, bytes: &[u8]) -> gimli::write::Result<()> {
        self.data.write_at(offset, bytes)
    }

    fn write_address(&mut self, address: Address, size: u8) -> gimli::write::Result<()> {
        match address {
            Address::Constant(value) => self.data.write_udata(value, size),
            Address::Symbol { symbol, addend } => {
                let offset = self.data.len();
                self.relocations
                    .push((offset, size, Target::Function(symbol), addend));
                self.data.write_udata(0, size)
            }
        }
    }

    fn write_offset(
        &mut self,
        value: usize,
        section: SectionId,
        size: u8,
    ) -> gimli::write::Result<()> {
        let offset = self.data.len();
        self.write_offset_at(offset, value, section, size)?;
        Ok(())
    }

    fn write_offset_at(
        &mut self,
        offset: usize,
        value: usize,
        section: SectionId,
        size: u8,
    ) -> gimli::write::Result<()> {
        if self.plain_offsets {
            return write_udata_at(&mut self.data, offset, value as u64, size);
        }
        let addend = i64::try_from(value).map_err(|_| gimli::write::Error::OffsetOutOfBounds)?;
        self.relocations
            .push((offset, size, Target::Section(section), addend));
        write_udata_at(&mut self.data, offset, 0, size)
    }
}

/// Writes `value` at `offset`, or appends it when `offset` is the end of the data.
fn write_udata_at(
    data: &mut EndianVec<LittleEndian>,
    offset: usize,
    value: u64,
    size: u8,
) -> gimli::write::Result<()> {
    if offset == data.len() {
        data.write_udata(value, size)
    } else {
        data.write_udata_at(offset, value, size)
    }
}

/// Adds the DWARF of the functions of `pieces` to the object of `product`, `files` being the
/// program's files.
///
/// ELF's linker joins the DWARF of every object, so its addresses and offsets are relocated
/// against the sections they point into. Mach-O's leaves the DWARF in the object for
/// `dsymutil` to gather, which keeps what a relocated address describes when the executable
/// kept the code or data at it: its offsets are written as they are, and its addresses are
/// relocated against their sections, holding where they are in the object, as Mach-O's
/// relocations against a section do. What the object's layout adds to them is given back
/// ([`Placing`]), to add once the object is written.
pub(crate) fn add_to_object(
    product: &mut ObjectProduct,
    pieces: &[Arc<Piece>],
    files: &[PathBuf],
    cie: Option<CommonInformationEntry>,
) -> Result<Placing, String> {
    let data = data_ids(pieces);
    let mut symbols: Vec<SymbolId> = pieces
        .iter()
        .map(|f| product.function_symbol(f.id))
        .collect();
    symbols.extend(data.iter().map(|&d| product.data_symbol(d)));
    let macho = product.object.format() == BinaryFormat::MachO;
    let address = |i: usize| Address::Symbol {
        symbol: i,
        addend: 0,
    };
    let start = |i: usize| address(i);
    let index: rustc_hash::FxHashMap<DataId, usize> = (data.iter().copied()).zip(0..).collect();
    let data_address = |d: DataId| address(pieces.len() + index.get(&d).copied().unwrap_or(0));
    let unit = Unit {
        pieces,
        files,
        start: &start,
        data: &data_address,
        cie,
    };
    let sections = assemble(&unit, macho)?;
    let ids = add_sections(&mut product.object, &sections, macho)?;
    let mut placing = Placing::default();
    let placed = macho.then_some(&mut placing);
    relocate(&mut product.object, &sections, &ids, (&symbols, placed))?;
    Ok(placing)
}

/// The static data that the constants of the functions' locals point into, each once.
fn data_ids(pieces: &[Arc<Piece>]) -> Vec<DataId> {
    let mut seen = rustc_hash::FxHashSet::default();
    let all = pieces.iter().flat_map(|p| p.data.iter().copied());
    all.filter(|&d| seen.insert(d)).collect()
}

/// Adds the sections that hold data to the object, each with its id.
fn add_sections(
    object: &mut Object<'_>,
    sections: &Sections<Relocating>,
    macho: bool,
) -> Result<Vec<(SectionId, object::write::SectionId)>, String> {
    let mut ids = Vec::new();
    sections.for_each(|id, w: &Relocating| -> Result<(), String> {
        if !w.data.slice().is_empty() {
            let segment = object.segment_name(StandardSegment::Debug).to_vec();
            let name = if macho {
                id.name().replacen('.', "__", 1).into_bytes()
            } else {
                id.name().as_bytes().to_vec()
            };
            let section = object.add_section(segment, name, SectionKind::Debug);
            object.set_section_data(section, w.data.slice().to_vec(), 1);
            ids.push((id, section));
        }
        Ok(())
    })?;
    Ok(ids)
}

/// Adds the relocations of the DWARF sections, each against the section of its target, at the
/// target's offset there, so that a linker that moves the sections moves the addresses and
/// offsets with them. For Mach-O, whose relocations against a section hold its address in the
/// object too, `placing` notes each address, to add that once the object is laid out.
fn relocate(
    object: &mut Object<'_>,
    sections: &Sections<Relocating>,
    ids: &[(SectionId, object::write::SectionId)],
    (targets, mut placing): (&[SymbolId], Option<&mut Placing>),
) -> Result<(), String> {
    sections.for_each(|id, w: &Relocating| -> Result<(), String> {
        let Some(&(_, section)) = ids.iter().find(|(s, _)| *s == id) else {
            return Ok(());
        };
        for &(offset, size, target, addend) in &w.relocations {
            let (symbol, addend) = match target {
                Target::Function(i) => {
                    let symbol = object.symbol(targets[i]);
                    let SymbolSection::Section(base) = symbol.section else {
                        return Err("a relocation's target is in no section".to_owned());
                    };
                    let place = i64::try_from(symbol.value).unwrap_or(0);
                    if let Some(placing) = placing.as_deref_mut() {
                        placing.note(object, (section, offset as u64), base);
                    }
                    (object.section_symbol(base), place + addend)
                }
                Target::Section(s) => {
                    let Some(&(_, target)) = ids.iter().find(|(t, _)| *t == s) else {
                        return Err(format!("no section {}", s.name()));
                    };
                    (object.section_symbol(target), addend)
                }
            };
            let relocation = Relocation {
                offset: offset as u64,
                symbol,
                addend,
                flags: RelocationFlags::Generic {
                    kind: RelocationKind::Absolute,
                    encoding: RelocationEncoding::Generic,
                    size: size * 8,
                },
            };
            object
                .add_relocation(section, relocation)
                .map_err(|e| format!("cannot relocate the DWARF: {e}"))?;
        }
        Ok(())
    })
}

/// The DWARF sections of functions whose code is at known addresses, `start` giving each
/// function's, by its index in `pieces`, and `data` each object of static data's.
pub(crate) fn with_addresses(
    pieces: &[Arc<Piece>],
    files: &[PathBuf],
    start: &dyn Fn(usize) -> u64,
    data: &dyn Fn(DataId) -> u64,
    cie: Option<CommonInformationEntry>,
) -> Result<Vec<(SectionId, Vec<u8>)>, String> {
    let address = |i: usize| Address::Constant(start(i));
    let data_address = |d: DataId| Address::Constant(data(d));
    let unit = Unit {
        pieces,
        files,
        start: &address,
        data: &data_address,
        cie,
    };
    let sections = assemble(&unit, true)?;
    let mut out = Vec::new();
    sections.for_each(|id, w: &Relocating| -> Result<(), String> {
        if !w.data.slice().is_empty() {
            out.push((id, w.data.slice().to_vec()));
        }
        Ok(())
    })?;
    Ok(out)
}
