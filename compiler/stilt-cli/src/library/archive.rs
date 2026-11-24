//! A static library's archive (c.static-library): its members in a fixed order,
//! each with the time 0, the owner 0 and the mode 644, so that one build's archive is the same
//! bytes as another's, and a table of the symbols they define, as the target's linker reads it:
//! GNU's for ELF, and Darwin's for Mach-O.

use object::read::archive::ArchiveFile;
use object::{Object, ObjectSymbol};

/// A member of an archive: its name and its bytes.
#[derive(Debug)]
pub(crate) struct Member {
    pub(crate) name: String,
    pub(crate) bytes: Vec<u8>,
}

/// The members of an archive, in order, without its tables of symbols and of long names.
pub(crate) fn members(archive: &[u8]) -> Result<Vec<Member>, String> {
    let file = ArchiveFile::parse(archive).map_err(|e| format!("the runtime library: {e}"))?;
    let mut found = Vec::new();
    for member in file.members() {
        let member = member.map_err(|e| format!("the runtime library: {e}"))?;
        let name = String::from_utf8_lossy(member.name()).into_owned();
        if name.starts_with("__.SYMDEF") {
            continue;
        }
        let bytes = member
            .data(archive)
            .map_err(|e| format!("the runtime library: {e}"))?;
        found.push(Member {
            name,
            bytes: bytes.to_vec(),
        });
    }
    Ok(found)
}

/// The global symbols that an object defines, or none for a member that isn't an object.
fn defined(bytes: &[u8]) -> Vec<Vec<u8>> {
    let Ok(file) = object::File::parse(bytes) else {
        return Vec::new();
    };
    file.symbols()
        .filter(|s| s.is_global() && s.is_definition())
        .filter_map(|s| s.name_bytes().ok().map(<[u8]>::to_vec))
        .collect()
}

/// The archive of `members`, in their order, in Darwin's format when `darwin` and in GNU's
/// otherwise.
pub(crate) fn archive(members: &[Member], darwin: bool) -> Vec<u8> {
    let symbols: Vec<Vec<Vec<u8>>> = members.iter().map(|m| defined(&m.bytes)).collect();
    if darwin {
        darwin_archive(members, &symbols)
    } else {
        gnu_archive(members, &symbols)
    }
}

/// A member's header: its name field, the time, owner and group 0, the mode 644 and its size.
fn header(out: &mut Vec<u8>, name: &str, size: usize) {
    let field = |out: &mut Vec<u8>, text: &str, width: usize| {
        out.extend_from_slice(text.as_bytes());
        out.extend(std::iter::repeat_n(b' ', width - text.len()));
    };
    field(out, name, 16);
    field(out, "0", 12);
    field(out, "0", 6);
    field(out, "0", 6);
    field(out, "644", 8);
    field(out, &size.to_string(), 10);
    out.extend_from_slice(b"`\n");
}

/// Pads `out` to an even length, as every member's data is.
fn pad(out: &mut Vec<u8>) {
    if out.len() % 2 == 1 {
        out.push(b'\n');
    }
}

/// GNU's format: the table of symbols, `/`, of big-endian offsets of the members that define
/// them, then the table of names longer than 15 bytes, `//`, then the members.
fn gnu_archive(members: &[Member], symbols: &[Vec<Vec<u8>>]) -> Vec<u8> {
    let mut names = Vec::new();
    let fields: Vec<String> = members
        .iter()
        .map(|m| {
            if m.name.len() <= 15 {
                format!("{}/", m.name)
            } else {
                let field = format!("/{}", names.len());
                names.extend_from_slice(m.name.as_bytes());
                names.extend_from_slice(b"/\n");
                field
            }
        })
        .collect();
    let count: usize = symbols.iter().map(Vec::len).sum();
    let strings: usize = symbols.iter().flatten().map(|s| s.len() + 1).sum();
    let table = 4 + 4 * count + strings;
    let mut at = 8 + 60 + table + table % 2;
    if !names.is_empty() {
        at += 60 + names.len() + names.len() % 2;
    }
    let mut offsets = Vec::with_capacity(members.len());
    for m in members {
        offsets.push(at);
        at += 60 + m.bytes.len() + m.bytes.len() % 2;
    }
    let mut out = b"!<arch>\n".to_vec();
    header(&mut out, "/", table);
    out.extend_from_slice(&u32::try_from(count).unwrap_or(u32::MAX).to_be_bytes());
    for (defined, &offset) in symbols.iter().zip(&offsets) {
        for _ in defined {
            out.extend_from_slice(&u32::try_from(offset).unwrap_or(u32::MAX).to_be_bytes());
        }
    }
    for name in symbols.iter().flatten() {
        out.extend_from_slice(name);
        out.push(0);
    }
    pad(&mut out);
    if !names.is_empty() {
        header(&mut out, "//", names.len());
        out.extend_from_slice(&names);
        pad(&mut out);
    }
    for (m, field) in members.iter().zip(&fields) {
        header(&mut out, field, m.bytes.len());
        out.extend_from_slice(&m.bytes);
        pad(&mut out);
    }
    out
}

/// The length of a Darwin member's name field, after a header at `at`: the name and a NUL at
/// least, so that the member's data starts at a multiple of 8, as Mach-O's linker wants.
fn name_field(at: usize, name: &str) -> usize {
    let mut len = name.len() + 1;
    while !(at + 60 + len).is_multiple_of(8) {
        len += 1;
    }
    len
}

/// Darwin's format: the table of symbols, `__.SYMDEF SORTED`, of each symbol's name and the
/// offset of the member that defines it, sorted by name, then the members, each name after its
/// header, as `#1/LENGTH` says.
fn darwin_archive(members: &[Member], symbols: &[Vec<Vec<u8>>]) -> Vec<u8> {
    const TABLE: &str = "__.SYMDEF SORTED";
    let mut entries: Vec<(&[u8], usize)> = Vec::new();
    let mut strings = Vec::new();
    let mut by_name: Vec<(&[u8], usize)> = symbols
        .iter()
        .enumerate()
        .flat_map(|(i, names)| names.iter().map(move |n| (n.as_slice(), i)))
        .collect();
    by_name.sort_by(|a, b| a.0.cmp(b.0).then(a.1.cmp(&b.1)));
    let mut string_at = Vec::with_capacity(by_name.len());
    for (name, member) in &by_name {
        string_at.push(strings.len());
        strings.extend_from_slice(name);
        strings.push(0);
        entries.push((name, *member));
    }
    while strings.len() % 8 != 0 {
        strings.push(0);
    }
    let table_name = name_field(8, TABLE);
    let table = table_name + 4 + 8 * entries.len() + 4 + strings.len();
    let mut at = 8 + 60 + table + table % 2;
    let mut placed = Vec::with_capacity(members.len());
    for m in members {
        let name = name_field(at, &m.name);
        placed.push((at, name));
        at += 60 + name + m.bytes.len();
        at += at % 2;
    }
    let word = |out: &mut Vec<u8>, n: usize| {
        out.extend_from_slice(&u32::try_from(n).unwrap_or(u32::MAX).to_le_bytes());
    };
    let mut out = b"!<arch>\n".to_vec();
    header(&mut out, &format!("#1/{table_name}"), table);
    out.extend_from_slice(TABLE.as_bytes());
    out.extend(std::iter::repeat_n(0, table_name - TABLE.len()));
    word(&mut out, 8 * entries.len());
    for (k, (_, member)) in entries.iter().enumerate() {
        word(&mut out, string_at[k]);
        word(&mut out, placed[*member].0);
    }
    word(&mut out, strings.len());
    out.extend_from_slice(&strings);
    pad(&mut out);
    for (m, &(_, name)) in members.iter().zip(&placed) {
        header(&mut out, &format!("#1/{name}"), name + m.bytes.len());
        out.extend_from_slice(m.name.as_bytes());
        out.extend(std::iter::repeat_n(0, name - m.name.len()));
        out.extend_from_slice(&m.bytes);
        pad(&mut out);
    }
    out
}
