//! The JIT's code given to debuggers through the GDB JIT interface, which gdb reads and lldb
//! too, with `settings set plugin.jit-loader.gdb.enable on` on macOS (goal debuggable-builds).
//!
//! Each load of an image writes an ELF file in memory that holds the DWARF of the functions it
//! compiled, their code's addresses written in, and a `.text` section without contents that
//! covers that code. It is linked into the list that `__jit_debug_descriptor` heads, and
//! `__jit_debug_register_code` is called, on which a debugger stops to read the list.

use std::path::PathBuf;
use std::ptr;
use std::sync::{Arc, Mutex};

use cranelift_module::{DataId, FuncId};
use gimli::SectionId;
use object::Endianness;
use object::elf;
use object::write::StringId;
use object::write::elf::{FileHeader, SectionHeader, Writer};

use super::piece::Piece;
use super::sections::with_addresses;

/// An entry of the list, as the interface defines it.
#[repr(C)]
struct CodeEntry {
    next: *mut CodeEntry,
    prev: *mut CodeEntry,
    file: *const u8,
    size: u64,
}

/// The head of the list, as the interface defines it.
#[repr(C)]
pub(crate) struct Descriptor {
    version: u32,
    action: u32,
    relevant: *mut CodeEntry,
    first: *mut CodeEntry,
}

const REGISTER: u32 = 1;
const UNREGISTER: u32 = 2;

/// The head of the list, which debuggers find by its name.
#[unsafe(no_mangle)]
static mut __jit_debug_descriptor: Descriptor = Descriptor {
    version: 1,
    action: 0,
    relevant: ptr::null_mut(),
    first: ptr::null_mut(),
};

/// The function on which a debugger stops to read the list. It must not be inlined or removed.
#[unsafe(no_mangle)]
#[inline(never)]
extern "C" fn __jit_debug_register_code() {
    std::hint::black_box(());
}

/// Serializes changes of the list.
static LIST: Mutex<()> = Mutex::new(());

/// An ELF file in the list, which leaves it when it is dropped.
#[derive(Debug)]
pub(crate) struct Registration {
    entry: *mut CodeEntry,
    _file: Box<[u8]>,
}

// SAFETY: the entry is only read and written under `LIST`.
unsafe impl Send for Registration {}

impl Registration {
    /// Adds `file` to the list, and tells any debugger.
    pub(crate) fn new(file: Vec<u8>) -> Self {
        let file = file.into_boxed_slice();
        let entry = Box::into_raw(Box::new(CodeEntry {
            next: ptr::null_mut(),
            prev: ptr::null_mut(),
            file: file.as_ptr(),
            size: file.len() as u64,
        }));
        let _guard = LIST
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        // SAFETY: the list is changed only under `LIST`, and its entries are alive until they
        // leave it.
        unsafe {
            let descriptor = &raw mut __jit_debug_descriptor;
            (*entry).next = (*descriptor).first;
            if !(*descriptor).first.is_null() {
                (*(*descriptor).first).prev = entry;
            }
            (*descriptor).first = entry;
            (*descriptor).relevant = entry;
            (*descriptor).action = REGISTER;
        }
        __jit_debug_register_code();
        Self { entry, _file: file }
    }
}

impl Drop for Registration {
    fn drop(&mut self) {
        let _guard = LIST
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        // SAFETY: as in `new`; the entry is in the list until here.
        unsafe {
            let descriptor = &raw mut __jit_debug_descriptor;
            let entry = self.entry;
            if (*entry).prev.is_null() {
                (*descriptor).first = (*entry).next;
            } else {
                (*(*entry).prev).next = (*entry).next;
            }
            if !(*entry).next.is_null() {
                (*(*entry).next).prev = (*entry).prev;
            }
            (*descriptor).relevant = entry;
            (*descriptor).action = UNREGISTER;
            __jit_debug_register_code();
            drop(Box::from_raw(entry));
        }
    }
}

/// Gives debuggers the DWARF of the functions of `facts`, whose code `address` finds, and the
/// static data their locals' constants point to `data`, unless there are none.
pub(crate) fn register(
    facts: &[Arc<Piece>],
    files: &[PathBuf],
    address: impl Fn(FuncId) -> u64,
    data: impl Fn(DataId) -> u64,
    cie: Option<gimli::write::CommonInformationEntry>,
) -> Result<Option<Registration>, String> {
    if facts.is_empty() {
        return Ok(None);
    }
    let starts: Vec<u64> = facts.iter().map(|f| address(f.id)).collect();
    let low = starts.iter().copied().min().unwrap_or(0);
    let high = facts
        .iter()
        .zip(&starts)
        .map(|(f, &s)| s + u64::from(f.size))
        .max()
        .unwrap_or(low);
    let sections = with_addresses(facts, files, &|i| starts[i], &data, cie)?;
    Ok(Some(Registration::new(elf_file(&sections, low, high))))
}

/// An ELF file for the host that holds `sections` and a `.text` section from `low` to `high`.
pub(crate) fn elf_file(sections: &[(SectionId, Vec<u8>)], low: u64, high: u64) -> Vec<u8> {
    let mut out = Vec::new();
    let mut w = Writer::new(Endianness::Little, true, &mut out);
    w.reserve_file_header();
    w.reserve_null_section_index();
    let text = w.add_section_name(b".text");
    w.reserve_section_index();
    let mut placed: Vec<(StringId, u64, &[u8])> = sections
        .iter()
        .map(|(id, data)| {
            let name = w.add_section_name(id.name().as_bytes());
            w.reserve_section_index();
            (name, 0, data.as_slice())
        })
        .collect();
    for p in &mut placed {
        p.1 = w.reserve(p.2.len() as u64, 1);
    }
    w.reserve_shstrtab_section_index();
    // The names were all added, so the table can be laid out.
    let _ = w.reserve_shstrtab();
    w.reserve_section_headers();
    let header = FileHeader {
        os_abi: elf::ELFOSABI_NONE,
        abi_version: 0,
        e_type: elf::ET_EXEC,
        e_machine: if cfg!(target_arch = "aarch64") {
            elf::EM_AARCH64
        } else {
            elf::EM_X86_64
        },
        e_entry: 0,
        e_flags: elf::FileFlags::default(),
    };
    // The writer reserved exactly what it writes, so writing can't fail.
    let _ = w.write_file_header(&header);
    for p in &placed {
        w.write(p.2);
    }
    w.write_shstrtab();
    w.write_null_section_header();
    let code = elf::SectionFlags(elf::SHF_ALLOC.0 | elf::SHF_EXECINSTR.0);
    let header = section(w.section_name_offset(Some(text)), elf::SHT_NOBITS, code);
    w.write_section_header(&SectionHeader {
        sh_addr: low,
        sh_size: high - low,
        sh_addralign: 16,
        ..header
    });
    for &(name, offset, data) in &placed {
        let header = section(
            w.section_name_offset(Some(name)),
            elf::SHT_PROGBITS,
            elf::SectionFlags::default(),
        );
        w.write_section_header(&SectionHeader {
            sh_offset: offset,
            sh_size: data.len() as u64,
            ..header
        });
    }
    w.write_shstrtab_section_header();
    out
}

/// The header of a section of the name at `name` in the table of names, of `kind`.
fn section(name: u32, kind: elf::SectionType, flags: elf::SectionFlags) -> SectionHeader {
    SectionHeader {
        sh_name: name,
        sh_type: kind,
        sh_flags: flags,
        sh_addr: 0,
        sh_offset: 0,
        sh_size: 0,
        sh_link: 0,
        sh_info: 0,
        sh_addralign: 1,
        sh_entsize: 0,
    }
}
