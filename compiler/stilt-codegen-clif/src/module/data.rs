//! The static data of a compiled program: the immortal objects of its constant strings and data
//! objects, as `stilt-runtime` lays objects out.

use cranelift_module::{DataDescription, DataId, Module};
use stilt_mir::mir::Const;

use super::{Answer, Asked, HEADER, Registry};

const DATA: u8 = 0;
const STR: u8 = 1;

impl Registry {
    /// The static, immortal object of a constant string or data object.
    pub(crate) fn data(&mut self, module: &mut dyn Module, c: &Const) -> Result<DataId, String> {
        let id = self.data_of(module, c)?;
        self.ask(|| Asked::Data(c.clone()), Answer::Data(id));
        Ok(id)
    }

    fn data_of(&mut self, module: &mut dyn Module, c: &Const) -> Result<DataId, String> {
        if let Some(&id) = self.data.get(c) {
            return Ok(id);
        }
        let mut desc = DataDescription::new();
        desc.set_align(8);
        match c {
            Const::Str(s) => desc.define(string_bytes(s).into_boxed_slice()),
            Const::Data(tag, fields) => self.data_object(module, &mut desc, *tag, fields)?,
            Const::Word(_) | Const::Code(_) => return Err("a word is no data".to_owned()),
        }
        let id = self.fresh_data(module, false)?;
        module.define_data(id, &desc).map_err(|e| e.to_string())?;
        self.data.insert(c.clone(), id);
        Ok(id)
    }

    fn data_object(
        &mut self,
        module: &mut dyn Module,
        desc: &mut DataDescription,
        tag: u16,
        fields: &[(Const, bool)],
    ) -> Result<(), String> {
        let len = fields.len();
        let mut masks = vec![0u64; len.div_ceil(64)];
        for (i, (_, heap)) in fields.iter().enumerate() {
            if *heap {
                masks[i / 64] |= 1 << (i % 64);
            }
        }
        let first = masks.first().copied().unwrap_or(0);
        let mut bytes = header(DATA, tag, stilt_runtime::layout::data_layout(len, first));
        if len <= stilt_runtime::layout::INLINE_FIELDS {
            masks.clear();
        }
        let mut relocations: Vec<(u32, &Const)> = Vec::new();
        for (field, _) in fields {
            let offset = u32::try_from(bytes.len()).map_err(|e| e.to_string())?;
            match field {
                Const::Word(w) => bytes.extend_from_slice(&w.to_le_bytes()),
                other => {
                    bytes.extend_from_slice(&0u64.to_le_bytes());
                    relocations.push((offset, other));
                }
            }
        }
        for m in masks {
            bytes.extend_from_slice(&m.to_le_bytes());
        }
        desc.define(bytes.into_boxed_slice());
        for (offset, field) in relocations {
            match field {
                Const::Code(f) => {
                    let slot = self.slot_in(module, f, &[])?;
                    let gv = module.declare_data_in_data(slot, desc);
                    desc.write_data_addr(offset, gv, 0);
                }
                other => {
                    let id = self.data_of(module, other)?;
                    let gv = module.declare_data_in_data(id, desc);
                    desc.write_data_addr(offset, gv, 0);
                }
            }
        }
        Ok(())
    }
}

/// The header of an immortal object: a count of 0.
fn header(kind: u8, tag: u16, extent: u32) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(HEADER as usize);
    bytes.extend_from_slice(&0u32.to_le_bytes());
    bytes.push(kind);
    bytes.push(0);
    bytes.extend_from_slice(&tag.to_le_bytes());
    bytes.extend_from_slice(&extent.to_le_bytes());
    bytes.extend_from_slice(&0u32.to_le_bytes());
    bytes
}

/// A string object: its header, its length and its bytes.
fn string_bytes(s: &str) -> Vec<u8> {
    let mut bytes = header(STR, 0, 0);
    bytes.extend_from_slice(&(s.len() as u64).to_le_bytes());
    bytes.extend_from_slice(s.as_bytes());
    while !bytes.len().is_multiple_of(8) {
        bytes.push(0);
    }
    bytes
}
