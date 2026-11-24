//! The encoding of DWARF that the pieces of [`super::piece`] and the unit that
//! [`super::assemble`] puts them in share: the abbreviations of every entry, one table for the
//! whole unit, so that the entries of each function can be written apart and put side by side,
//! and the bytes of a piece with the places a build fills in.

use std::sync::Arc;

use gimli::constants::{self as dw, DwAt, DwForm, DwTag};

/// The encoding of the DWARF: version 4, which every debugger reads, of 64-bit addresses and
/// 32-bit offsets.
pub(crate) const VERSION: u16 = 4;

/// The code of each abbreviation, as [`table`] declares it.
pub(crate) const UNIT: u64 = 1;
/// A subprogram's: without the file and line it is declared at, then with them; without
/// locals, then with them.
pub(crate) const SUBPROGRAM: [[u64; 2]; 2] = [[2, 3], [4, 5]];
/// A local's, by where it lives: an expression, a location list, or nowhere; a variable's,
/// then a parameter's.
pub(crate) const LOCAL: [[u64; 3]; 2] = [[6, 7, 8], [9, 10, 11]];
pub(crate) const BASE: u64 = 12;
pub(crate) const POINTER: u64 = 13;
pub(crate) const TYPEDEF: u64 = 14;
pub(crate) const ENUMERATION: u64 = 15;
pub(crate) const ENUMERATOR: u64 = 16;
pub(crate) const ARRAY: u64 = 17;
pub(crate) const COUNTED: u64 = 18;
pub(crate) const SUBRANGE: u64 = 19;
pub(crate) const STRUCTURE: u64 = 20;
pub(crate) const MEMBER: u64 = 21;

/// An abbreviation: its tag, whether its entries have children, and its attributes.
type Abbreviation = (DwTag, bool, &'static [(DwAt, DwForm)]);

const NAMED_LOCAL: [(DwAt, DwForm); 3] = [
    (dw::DW_AT_name, dw::DW_FORM_string),
    (dw::DW_AT_type, dw::DW_FORM_ref4),
    (dw::DW_AT_location, dw::DW_FORM_exprloc),
];
const LISTED_LOCAL: [(DwAt, DwForm); 3] = [
    (dw::DW_AT_name, dw::DW_FORM_string),
    (dw::DW_AT_type, dw::DW_FORM_ref4),
    (dw::DW_AT_location, dw::DW_FORM_sec_offset),
];
const SUBPROGRAM_AT: [(DwAt, DwForm); 6] = [
    (dw::DW_AT_name, dw::DW_FORM_string),
    (dw::DW_AT_low_pc, dw::DW_FORM_addr),
    (dw::DW_AT_high_pc, dw::DW_FORM_data4),
    (dw::DW_AT_frame_base, dw::DW_FORM_exprloc),
    (dw::DW_AT_decl_file, dw::DW_FORM_udata),
    (dw::DW_AT_decl_line, dw::DW_FORM_udata),
];
const TYPED: [(DwAt, DwForm); 2] = [
    (dw::DW_AT_name, dw::DW_FORM_string),
    (dw::DW_AT_type, dw::DW_FORM_ref4),
];

/// The abbreviations, by their codes from 1.
const ABBREVIATIONS: [Abbreviation; 21] = [
    (
        dw::DW_TAG_compile_unit,
        true,
        &[
            (dw::DW_AT_producer, dw::DW_FORM_string),
            (dw::DW_AT_language, dw::DW_FORM_data2),
            (dw::DW_AT_name, dw::DW_FORM_string),
            (dw::DW_AT_comp_dir, dw::DW_FORM_string),
            (dw::DW_AT_stmt_list, dw::DW_FORM_sec_offset),
            (dw::DW_AT_low_pc, dw::DW_FORM_addr),
            (dw::DW_AT_ranges, dw::DW_FORM_sec_offset),
        ],
    ),
    (dw::DW_TAG_subprogram, false, SUBPROGRAM_AT.split_at(4).0),
    (dw::DW_TAG_subprogram, true, SUBPROGRAM_AT.split_at(4).0),
    (dw::DW_TAG_subprogram, false, &SUBPROGRAM_AT),
    (dw::DW_TAG_subprogram, true, &SUBPROGRAM_AT),
    (dw::DW_TAG_variable, false, &NAMED_LOCAL),
    (dw::DW_TAG_variable, false, &LISTED_LOCAL),
    (dw::DW_TAG_variable, false, &TYPED),
    (dw::DW_TAG_formal_parameter, false, &NAMED_LOCAL),
    (dw::DW_TAG_formal_parameter, false, &LISTED_LOCAL),
    (dw::DW_TAG_formal_parameter, false, &TYPED),
    (
        dw::DW_TAG_base_type,
        false,
        &[
            (dw::DW_AT_name, dw::DW_FORM_string),
            (dw::DW_AT_encoding, dw::DW_FORM_data1),
            (dw::DW_AT_byte_size, dw::DW_FORM_data1),
        ],
    ),
    (
        dw::DW_TAG_pointer_type,
        false,
        &[
            (dw::DW_AT_byte_size, dw::DW_FORM_data1),
            (dw::DW_AT_type, dw::DW_FORM_ref4),
        ],
    ),
    (dw::DW_TAG_typedef, false, &TYPED),
    (
        dw::DW_TAG_enumeration_type,
        true,
        &[
            (dw::DW_AT_name, dw::DW_FORM_string),
            (dw::DW_AT_byte_size, dw::DW_FORM_data1),
            (dw::DW_AT_type, dw::DW_FORM_ref4),
        ],
    ),
    (
        dw::DW_TAG_enumerator,
        false,
        &[
            (dw::DW_AT_name, dw::DW_FORM_string),
            (dw::DW_AT_const_value, dw::DW_FORM_udata),
        ],
    ),
    (
        dw::DW_TAG_array_type,
        true,
        &[(dw::DW_AT_type, dw::DW_FORM_ref4)],
    ),
    (
        dw::DW_TAG_subrange_type,
        false,
        &[(dw::DW_AT_count, dw::DW_FORM_udata)],
    ),
    (dw::DW_TAG_subrange_type, false, &[]),
    (
        dw::DW_TAG_structure_type,
        true,
        &[
            (dw::DW_AT_name, dw::DW_FORM_string),
            (dw::DW_AT_byte_size, dw::DW_FORM_udata),
        ],
    ),
    (
        dw::DW_TAG_member,
        false,
        &[
            (dw::DW_AT_name, dw::DW_FORM_string),
            (dw::DW_AT_type, dw::DW_FORM_ref4),
            (dw::DW_AT_data_member_location, dw::DW_FORM_udata),
        ],
    ),
];

/// The `.debug_abbrev` section: every abbreviation, by its code.
pub(crate) fn table() -> Vec<u8> {
    let mut out = Bytes::default();
    for (code, (tag, children, attributes)) in (1..).zip(ABBREVIATIONS) {
        out.uleb(code);
        out.uleb(u64::from(tag.0));
        out.u8(u8::from(children));
        for (at, form) in attributes {
            out.uleb(u64::from(at.0));
            out.uleb(u64::from(form.0));
        }
        out.u8(0);
        out.u8(0);
    }
    out.u8(0);
    out.0
}

/// Bytes of DWARF, little-endian.
#[derive(Clone, Debug, Default)]
pub(crate) struct Bytes(pub(crate) Vec<u8>);

impl Bytes {
    pub(crate) fn u8(&mut self, value: u8) {
        self.0.push(value);
    }

    pub(crate) fn u16(&mut self, value: u16) {
        self.0.extend_from_slice(&value.to_le_bytes());
    }

    pub(crate) fn u32(&mut self, value: u32) {
        self.0.extend_from_slice(&value.to_le_bytes());
    }

    pub(crate) fn u64(&mut self, value: u64) {
        self.0.extend_from_slice(&value.to_le_bytes());
    }

    pub(crate) fn uleb(&mut self, mut value: u64) {
        loop {
            let byte = (value & 0x7f) as u8;
            value >>= 7;
            if value == 0 {
                self.0.push(byte);
                return;
            }
            self.0.push(byte | 0x80);
        }
    }

    pub(crate) fn sleb(&mut self, mut value: i64) {
        loop {
            let byte = u8::try_from(value & 0x7f).unwrap_or(0);
            value >>= 7;
            let done = (value == 0 && byte & 0x40 == 0) || (value == -1 && byte & 0x40 != 0);
            if done {
                self.0.push(byte);
                return;
            }
            self.0.push(byte | 0x80);
        }
    }

    /// A string, ended by a zero byte, as `DW_FORM_string` writes it.
    pub(crate) fn string(&mut self, s: &str) {
        self.0.extend_from_slice(s.as_bytes());
        self.0.push(0);
    }

    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }
}

/// A place in a piece that a build fills in, as the unit it puts the piece in gives it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Patch {
    /// The address of the function's code, plus this: 8 bytes.
    Code(i64),
    /// The address of the data object that the piece's data `k` is: 8 bytes.
    Data(u32),
    /// The offset in the unit of the piece's type `k`: 4 bytes.
    Type(u32),
    /// The offset in `.debug_loc` of the piece's location lists, plus this: 4 bytes.
    Loc(u32),
    /// The offset in `.debug_frame` of the common information entry: 4 bytes.
    Cie,
}

impl Patch {
    /// The bytes it fills.
    pub(crate) const fn size(self) -> u8 {
        match self {
            Self::Code(_) | Self::Data(_) => 8,
            Self::Type(_) | Self::Loc(_) | Self::Cie => 4,
        }
    }
}

/// The bytes of a piece of a section, and the places a build fills in, each by its offset.
#[derive(Clone, Debug, Default)]
pub(crate) struct Chunk {
    pub(crate) bytes: Arc<[u8]>,
    pub(crate) patches: Arc<[(u32, Patch)]>,
}

/// A chunk as it is written.
#[derive(Debug, Default)]
pub(crate) struct Writing {
    pub(crate) out: Bytes,
    patches: Vec<(u32, Patch)>,
}

impl Writing {
    /// Leaves room for `patch`, which a build fills in.
    pub(crate) fn patch(&mut self, patch: Patch) {
        let at = u32::try_from(self.out.len()).unwrap_or(u32::MAX);
        self.patches.push((at, patch));
        self.out
            .0
            .extend(std::iter::repeat_n(0, usize::from(patch.size())));
    }

    pub(crate) fn finish(self) -> Chunk {
        Chunk {
            bytes: self.out.0.into(),
            patches: self.patches.into(),
        }
    }
}
