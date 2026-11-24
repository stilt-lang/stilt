//! The DWARF that a build puts together from functions' pieces, read back as a debugger reads
//! it: each subprogram at its function's address, a local's location list in its function's
//! code, its type by its name, and the line table's rows.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

use cranelift_module::FuncId;
use gimli::constants as dw;
use gimli::read::{AttributeValue, Dwarf, EndianSlice, Reader, Unit};
use gimli::{LittleEndian, SectionId};
use stilt_mir::mir::{Shown, ShownKind};

use super::piece::Piece;
use super::sections::with_addresses;
use super::{Facts, Place, Row, Var};

type R<'a> = EndianSlice<'a, LittleEndian>;

fn shown(name: &str) -> Shown {
    Shown {
        name: name.into(),
        kind: ShownKind::Signed(64),
        by_ref: false,
        variants: Arc::new([]),
        elements: None,
    }
}

/// A function of 16 bytes whose local `x` lives in register 0 from byte 4 to byte 8, and whose
/// code comes from lines 3 and 4 of the program's first file.
fn function(id: u32, name: &str) -> Arc<Piece> {
    let row = |offset, line| Row {
        offset,
        file: 0,
        line,
        col: 1,
    };
    let facts = Facts {
        id: FuncId::from_u32(id),
        name: name.to_owned(),
        size: 16,
        rows: vec![row(0, 3), row(4, 4)],
        vars: vec![Var {
            name: "x".into(),
            shown: shown("i64"),
            param: false,
            ranges: vec![(4, 8, Place::Reg(0))],
            constant: None,
        }],
        unwind: None,
    };
    Arc::new(Piece::new(&facts, 29, None))
}

/// The DWARF of two functions at 0x1000 and 0x2000.
fn sections() -> HashMap<SectionId, Vec<u8>> {
    let pieces = [function(0, "main.f"), function(1, "main.g")];
    let files = [PathBuf::from("/p/main.lt")];
    let starts = [0x1000, 0x2000];
    let out = with_addresses(&pieces, &files, &|i| starts[i], &|_| 0, None).expect("DWARF");
    out.into_iter().collect()
}

fn string<'a>(dwarf: &Dwarf<R<'a>>, unit: &Unit<R<'a>>, value: AttributeValue<R<'a>>) -> String {
    let s = dwarf.attr_string(unit, value).expect("a string");
    s.to_string_lossy().into_owned()
}

#[test]
fn a_built_unit_reads_back_with_each_function_at_its_address() {
    let sections = sections();
    let load = |id: SectionId| -> Result<R<'_>, gimli::Error> {
        let bytes = sections.get(&id).map_or(&[][..], Vec::as_slice);
        Ok(EndianSlice::new(bytes, LittleEndian))
    };
    let dwarf = Dwarf::load(load).expect("loaded");
    let header = dwarf.units().next().expect("read").expect("a unit");
    let unit = dwarf.unit(header).expect("its unit");
    let mut entries = unit.entries();
    let (mut subprograms, mut locals) = (Vec::new(), Vec::new());
    while let Some(entry) = entries.next_dfs().expect("an entry") {
        let name = entry
            .attr_value(dw::DW_AT_name)
            .map(|v| string(&dwarf, &unit, v));
        if entry.tag() == dw::DW_TAG_subprogram {
            let Some(AttributeValue::Addr(low)) = entry.attr_value(dw::DW_AT_low_pc) else {
                panic!("a subprogram without its address");
            };
            subprograms.push((name.expect("a name"), low));
        }
        if entry.tag() == dw::DW_TAG_variable {
            let Some(AttributeValue::UnitRef(ty)) = entry.attr_value(dw::DW_AT_type) else {
                panic!("a local without its type");
            };
            let ty = unit.entry(ty).expect("its type");
            let ty_name = ty
                .attr_value(dw::DW_AT_name)
                .map(|v| string(&dwarf, &unit, v));
            let location = entry.attr_value(dw::DW_AT_location).expect("a location");
            let mut list = dwarf
                .attr_locations(&unit, location)
                .expect("read")
                .expect("a list");
            let first = list.next().expect("read").expect("an entry");
            let expr = first.data.0.to_slice().expect("bytes").into_owned();
            locals.push((ty_name, first.range.begin, first.range.end, expr));
        }
    }
    let names = |n: &str, a: u64| (n.to_owned(), a);
    assert_eq!(
        subprograms,
        [names("main.f", 0x1000), names("main.g", 0x2000)]
    );
    let reg0 = vec![dw::DW_OP_reg0.0];
    let i64 = Some("i64".to_owned());
    assert_eq!(
        locals,
        [
            (i64.clone(), 0x1004, 0x1008, reg0.clone()),
            (i64, 0x2004, 0x2008, reg0)
        ]
    );
}

#[test]
fn a_built_line_table_maps_each_function_s_code_to_its_lines() {
    let sections = sections();
    let load = |id: SectionId| -> Result<R<'_>, gimli::Error> {
        let bytes = sections.get(&id).map_or(&[][..], Vec::as_slice);
        Ok(EndianSlice::new(bytes, LittleEndian))
    };
    let dwarf = Dwarf::load(load).expect("loaded");
    let header = dwarf.units().next().expect("read").expect("a unit");
    let unit = dwarf.unit(header).expect("its unit");
    let program = unit.line_program.clone().expect("a line table");
    let mut rows = program.rows();
    let mut found = Vec::new();
    while let Some((header, row)) = rows.next_row().expect("a row") {
        let file = row.file(header).expect("its file");
        let name = string(&dwarf, &unit, file.path_name());
        found.push((
            row.address(),
            row.line().map(u64::from),
            name,
            row.end_sequence(),
        ));
    }
    let row = |a: u64, line: Option<u64>, end| (a, line, "main.lt".to_owned(), end);
    assert_eq!(
        found,
        [
            row(0x1000, Some(3), false),
            row(0x1004, Some(4), false),
            row(0x1010, Some(4), true),
            row(0x2000, Some(3), false),
            row(0x2004, Some(4), false),
            row(0x2010, Some(4), true),
        ]
    );
}
