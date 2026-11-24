//! The stub of macOS's `libSystem` that an aarch64 macOS link takes in place of the SDK's: a
//! text-based library that lists the symbols the program and the runtime take from the system
//! (goal cross-compilation).
//!
//! A macOS executable names, for each symbol it imports, the library it was found in at link
//! time, and the loader looks it up there when the program starts. `libSystem` re-exports the
//! system's C library, its maths library, its threads and its loader, so every symbol the
//! runtime takes from the system is found through it, and the stub need only say that it
//! exports each of them.

use std::collections::{BTreeSet, HashSet};

use object::read::archive::ArchiveFile;
use object::{Object, ObjectSymbol};

/// The library every macOS executable links, by its install name.
const INSTALL_NAME: &str = "/usr/lib/libSystem.B.dylib";

/// The symbol through which the loader binds a lazy import, which the linker references itself.
const STUB_BINDER: &str = "dyld_stub_binder";

/// The symbols that the objects `programs` and the archive `library` use and none defines,
/// which come from the system.
pub(crate) fn system_symbols(
    programs: &[&[u8]],
    library: &[u8],
) -> Result<BTreeSet<String>, String> {
    let mut defined = HashSet::new();
    let mut used = BTreeSet::new();
    for program in programs {
        scan(program, &mut defined, &mut used)
            .map_err(|e| format!("cannot read the object: {e}"))?;
    }
    let archive =
        ArchiveFile::parse(library).map_err(|e| format!("cannot read the runtime: {e}"))?;
    for member in archive.members() {
        let member = member.map_err(|e| format!("cannot read the runtime: {e}"))?;
        let data = member
            .data(library)
            .map_err(|e| format!("cannot read the runtime: {e}"))?;
        // An archive may hold members that aren't objects, such as its symbol table.
        let _ = scan(data, &mut defined, &mut used);
    }
    used.retain(|name| !defined.contains(name));
    used.insert(STUB_BINDER.to_owned());
    Ok(used)
}

/// Adds the global symbols the object `data` defines to `defined`, and those it uses to `used`.
fn scan(
    data: &[u8],
    defined: &mut HashSet<String>,
    used: &mut BTreeSet<String>,
) -> Result<(), object::Error> {
    let file = object::File::parse(data)?;
    for symbol in file.symbols() {
        let name = symbol.name()?;
        if symbol.is_undefined() {
            used.insert(name.to_owned());
        } else if symbol.is_global() {
            defined.insert(name.to_owned());
        }
    }
    Ok(())
}

/// The text of the stub: `libSystem`, exporting `symbols` to arm64 macOS.
pub(crate) fn lib_system(symbols: &BTreeSet<String>) -> String {
    let quoted: Vec<String> = symbols.iter().map(|s| format!("'{s}'")).collect();
    format!(
        "--- !tapi-tbd\ntbd-version: 4\ntargets: [ arm64-macos ]\ninstall-name: '{INSTALL_NAME}'\nexports:\n  - targets: [ arm64-macos ]\n    symbols: [ {} ]\n...\n",
        quoted.join(", ")
    )
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::lib_system;

    #[test]
    fn the_stub_lists_each_symbol_once_quoted() {
        let symbols: BTreeSet<String> = ["_malloc", "_free"].map(String::from).into();
        let text = lib_system(&symbols);
        assert!(text.starts_with("--- !tapi-tbd\n"));
        assert!(text.contains("install-name: '/usr/lib/libSystem.B.dylib'"));
        assert!(text.contains("symbols: [ '_free', '_malloc' ]"));
    }
}
