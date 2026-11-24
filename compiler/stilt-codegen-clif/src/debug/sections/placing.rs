//! The addresses that a Mach-O object's DWARF holds, which its layout places: a relocation
//! against a section holds the address in the object of what it points to, and the object
//! crate lays the object out only as it writes it. Each address is written as its offset in its
//! section, and once the object is written, the section's address is added to it from the
//! object's headers, so that a build lays the object out once.

use object::Endianness;
use object::read::macho::MachOFile64;
use object::read::{Object as _, ObjectSection as _};
use object::write::{Object, SectionId};

/// A section's segment's name and its own, which name it in the object.
type Names = (Vec<u8>, Vec<u8>);

/// The addresses to place: for each, the DWARF section it is in, its offset there, and the
/// section it points into, each section by its names.
#[derive(Debug, Default)]
pub(crate) struct Placing {
    sections: Vec<(SectionId, Names)>,
    addresses: Vec<(usize, u64, usize)>,
}

impl Placing {
    /// Notes the address at `offset` in `section`, which points into `target`.
    pub(crate) fn note(
        &mut self,
        object: &Object<'_>,
        (section, offset): (SectionId, u64),
        target: SectionId,
    ) {
        let (section, target) = (self.index(object, section), self.index(object, target));
        self.addresses.push((section, offset, target));
    }

    /// The index of `section` among those noted, noted if it isn't.
    fn index(&mut self, object: &Object<'_>, section: SectionId) -> usize {
        if let Some(i) = self.sections.iter().position(|(s, _)| *s == section) {
            return i;
        }
        let s = object.section(section);
        let names = (
            s.segment().unwrap_or_default().as_bytes().to_vec(),
            s.name().unwrap_or_default().as_bytes().to_vec(),
        );
        self.sections.push((section, names));
        self.sections.len() - 1
    }

    /// Adds to each address noted the address of the section it points into, in `bytes`, the
    /// object as written.
    ///
    /// # Errors
    ///
    /// Fails when `bytes` isn't a 64-bit Mach-O object that holds every section noted.
    pub(crate) fn place(&self, bytes: &mut [u8]) -> Result<(), String> {
        if self.addresses.is_empty() {
            return Ok(());
        }
        let laid = self.layout(bytes)?;
        for &(section, offset, target) in &self.addresses {
            let (_, start) = laid[section];
            let at = usize::try_from(start + offset).map_err(|e| e.to_string())?;
            let word = bytes
                .get_mut(at..at + 8)
                .ok_or("an address past its section")?;
            let held = u64::from_le_bytes(word.try_into().map_err(|_| "a short address")?);
            word.copy_from_slice(&(held + laid[target].0).to_le_bytes());
        }
        Ok(())
    }

    /// The address of each section noted, and where its data starts in `bytes`.
    fn layout(&self, bytes: &[u8]) -> Result<Vec<(u64, u64)>, String> {
        let file = MachOFile64::<Endianness>::parse(bytes).map_err(|e| e.to_string())?;
        let found: Vec<(Names, (u64, u64))> = (file.sections())
            .filter_map(|s| {
                let segment = s.segment_name_bytes().ok()??.to_vec();
                let names = (segment, s.name_bytes().ok()?.to_vec());
                let start = s.file_range().map_or(0, |(start, _)| start);
                Some((names, (s.address(), start)))
            })
            .collect();
        (self.sections.iter())
            .map(|(_, (segment, name))| {
                let place = (found.iter()).find(|((s, n), _)| s == segment && n == name);
                place.map(|&(_, at)| at).ok_or_else(|| {
                    format!("no section {} in the object", String::from_utf8_lossy(name))
                })
            })
            .collect()
    }
}
