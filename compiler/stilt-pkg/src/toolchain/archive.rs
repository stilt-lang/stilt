//! The archives of release toolchains: a POSIX tar of regular files, directories and symbolic
//! links, compressed by gzip (RFC 1952). Writing one is deterministic, its entries in the order
//! of their paths with no owner, no time and modes of 644 or 755, so that the same files give
//! the same bytes and so the same SHA-256 on every machine. Reading one refuses an entry that
//! would land outside its directory.

use std::fs;
use std::io::Write as _;
use std::path::{Component, Path, PathBuf};

/// A tar's block, which headers and contents fill.
const BLOCK: usize = 512;

/// The gzip header of a deflate stream with no name, no time and no flags.
const GZIP: [u8; 10] = [0x1f, 0x8b, 8, 0, 0, 0, 0, 0, 0, 0xff];

/// An entry of an archive, by its path inside it.
#[derive(Debug, PartialEq, Eq)]
enum Entry {
    File { bytes: Vec<u8>, executable: bool },
    Dir,
    Link(String),
}

/// The archive of the tree at `dir`, its symbolic links kept as links.
///
/// # Errors
///
/// Fails when the tree can't be read, or holds a path longer than a tar's 100 bytes.
pub fn pack(dir: &Path) -> Result<Vec<u8>, String> {
    let mut entries = Vec::new();
    walk(dir, Path::new(""), &mut entries)?;
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    let mut tar = Vec::new();
    for (path, entry) in &entries {
        header(&mut tar, path, entry)?;
        if let Entry::File { bytes, .. } = entry {
            tar.extend_from_slice(bytes);
            tar.resize(tar.len().next_multiple_of(BLOCK), 0);
        }
    }
    tar.resize(tar.len() + 2 * BLOCK, 0);
    let mut out = GZIP.to_vec();
    out.extend_from_slice(&miniz_oxide::deflate::compress_to_vec(&tar, 9));
    out.extend_from_slice(&crc32(&tar).to_le_bytes());
    // The length modulo 2^32, the low four bytes of the length, on a 32-bit target too.
    out.extend_from_slice(&tar.len().to_le_bytes()[..4]);
    Ok(out)
}

fn walk(root: &Path, at: &Path, out: &mut Vec<(String, Entry)>) -> Result<(), String> {
    let dir = root.join(at);
    let read = fs::read_dir(&dir).map_err(|e| format!("cannot read {}: {e}", dir.display()))?;
    for item in read {
        let item = item.map_err(|e| format!("cannot read {}: {e}", dir.display()))?;
        let rel = at.join(item.file_name());
        let path = root.join(&rel);
        let meta = fs::symlink_metadata(&path).map_err(|e| e.to_string())?;
        let name = rel.to_string_lossy().replace('\\', "/");
        if meta.file_type().is_symlink() {
            let to = fs::read_link(&path).map_err(|e| e.to_string())?;
            out.push((name, Entry::Link(to.to_string_lossy().into_owned())));
        } else if meta.is_dir() {
            out.push((format!("{name}/"), Entry::Dir));
            walk(root, &rel, out)?;
        } else {
            let bytes =
                fs::read(&path).map_err(|e| format!("cannot read {}: {e}", path.display()))?;
            out.push((
                name,
                Entry::File {
                    bytes,
                    executable: executable(&meta),
                },
            ));
        }
    }
    Ok(())
}

#[cfg(unix)]
fn executable(meta: &fs::Metadata) -> bool {
    use std::os::unix::fs::PermissionsExt as _;
    meta.permissions().mode() & 0o111 != 0
}

#[cfg(not(unix))]
fn executable(_: &fs::Metadata) -> bool {
    false
}

/// Writes the ustar header of an entry.
fn header(tar: &mut Vec<u8>, path: &str, entry: &Entry) -> Result<(), String> {
    if path.len() > 100 {
        return Err(format!("{path} is longer than an archive's 100 bytes"));
    }
    let mut h = [0u8; BLOCK];
    h[..path.len()].copy_from_slice(path.as_bytes());
    let (mode, size, kind, link) = match entry {
        Entry::File { bytes, executable } => {
            let mode = if *executable { 0o755 } else { 0o644 };
            (mode, bytes.len(), b'0', "")
        }
        Entry::Dir => (0o755, 0, b'5', ""),
        Entry::Link(to) => (0o777, 0, b'2', to.as_str()),
    };
    if link.len() > 100 {
        return Err(format!("{path} links to a path longer than 100 bytes"));
    }
    octal(&mut h[100..108], mode);
    octal(&mut h[108..116], 0);
    octal(&mut h[116..124], 0);
    octal(&mut h[124..136], size);
    octal(&mut h[136..148], 0);
    h[156] = kind;
    h[157..157 + link.len()].copy_from_slice(link.as_bytes());
    h[257..263].copy_from_slice(b"ustar\0");
    h[263..265].copy_from_slice(b"00");
    h[148..156].fill(b' ');
    let sum: usize = h.iter().map(|&b| usize::from(b)).sum();
    octal(&mut h[148..155], sum);
    tar.extend_from_slice(&h);
    Ok(())
}

/// Writes `value` in octal, zero-padded, ended by a NUL, into `field`.
fn octal(field: &mut [u8], value: usize) {
    let digits = field.len() - 1;
    let text = format!("{value:0digits$o}");
    field[..digits].copy_from_slice(&text.as_bytes()[text.len() - digits..]);
    field[digits] = 0;
}

/// Unpacks `archive` into the directory `dir`, which must not exist.
///
/// # Errors
///
/// Fails on bytes that aren't such an archive, on an entry whose path would leave `dir`, and
/// when the files can't be written.
pub fn unpack(archive: &[u8], dir: &Path) -> Result<(), String> {
    let tar = inflate(archive)?;
    fs::create_dir_all(dir).map_err(|e| format!("cannot write {}: {e}", dir.display()))?;
    let mut at = 0;
    while at + BLOCK <= tar.len() && tar[at..at + BLOCK].iter().any(|&b| b != 0) {
        let h = &tar[at..at + BLOCK];
        let name = text(&h[..100]);
        let prefix = text(&h[345..500]);
        let path = if prefix.is_empty() {
            name
        } else {
            format!("{prefix}/{name}")
        };
        let size = number(&h[124..136])?;
        let mode = number(&h[100..108])?;
        let to = inside(dir, &path)?;
        let start = at + BLOCK;
        let end = start
            .checked_add(size)
            .filter(|&e| e <= tar.len())
            .ok_or("a truncated archive")?;
        match h[156] {
            b'0' | 0 => write_file(&to, &tar[start..end], mode & 0o111 != 0)?,
            b'5' => fs::create_dir_all(&to)
                .map_err(|e| format!("cannot write {}: {e}", to.display()))?,
            b'2' => link(&to, &text(&h[157..257]), dir)?,
            other => return Err(format!("{path} is an entry of kind {}", char::from(other))),
        }
        at = start + size.next_multiple_of(BLOCK);
    }
    Ok(())
}

/// The tar inside the gzip stream `bytes`.
fn inflate(bytes: &[u8]) -> Result<Vec<u8>, String> {
    if bytes.len() < 18 || bytes[..3] != GZIP[..3] {
        return Err("it isn't a gzip stream".to_owned());
    }
    let flags = bytes[3];
    let mut at = 10;
    if flags & 4 != 0 {
        let extra = usize::from(u16::from_le_bytes([bytes[at], bytes[at + 1]]));
        at += 2 + extra;
    }
    for flag in [8, 16] {
        if flags & flag != 0 {
            at += 1 + bytes[at..]
                .iter()
                .position(|&b| b == 0)
                .ok_or("a malformed gzip header")?;
        }
    }
    if flags & 2 != 0 {
        at += 2;
    }
    let body = bytes
        .get(at..bytes.len() - 8)
        .ok_or("a malformed gzip stream")?;
    miniz_oxide::inflate::decompress_to_vec(body)
        .map_err(|e| format!("a malformed deflate stream: {e:?}"))
}

fn text(field: &[u8]) -> String {
    let end = field.iter().position(|&b| b == 0).unwrap_or(field.len());
    String::from_utf8_lossy(&field[..end]).into_owned()
}

fn number(field: &[u8]) -> Result<usize, String> {
    let digits = text(field);
    let digits = digits.trim_matches(|c: char| c == ' ' || c == '\0');
    if digits.is_empty() {
        return Ok(0);
    }
    usize::from_str_radix(digits, 8).map_err(|_| format!("a malformed number {digits:?}"))
}

/// The path of an entry under `dir`, which no `..` or root may leave.
fn inside(dir: &Path, path: &str) -> Result<PathBuf, String> {
    let rel = Path::new(path);
    if rel
        .components()
        .any(|c| !matches!(c, Component::Normal(_) | Component::CurDir))
    {
        return Err(format!("{path} would land outside the toolchain"));
    }
    Ok(dir.join(rel))
}

fn write_file(to: &Path, bytes: &[u8], executable: bool) -> Result<(), String> {
    if let Some(parent) = to.parent() {
        fs::create_dir_all(parent)
            .map_err(|e| format!("cannot write {}: {e}", parent.display()))?;
    }
    let mut file =
        fs::File::create(to).map_err(|e| format!("cannot write {}: {e}", to.display()))?;
    file.write_all(bytes)
        .map_err(|e| format!("cannot write {}: {e}", to.display()))?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        let mode = if executable { 0o755 } else { 0o644 };
        fs::set_permissions(to, fs::Permissions::from_mode(mode)).map_err(|e| e.to_string())?;
    }
    #[cfg(not(unix))]
    let _ = executable;
    Ok(())
}

/// Makes a symbolic link at `to`, whose target must stay within `dir`.
fn link(to: &Path, target: &str, dir: &Path) -> Result<(), String> {
    let base = to.parent().and_then(|p| p.strip_prefix(dir).ok());
    let mut depth = base.map_or(0, |p| p.components().count());
    for c in Path::new(target).components() {
        match c {
            Component::Normal(_) => depth += 1,
            Component::CurDir => {}
            Component::ParentDir if depth > 0 => depth -= 1,
            _ => return Err(format!("{} links outside the toolchain", to.display())),
        }
    }
    #[cfg(unix)]
    std::os::unix::fs::symlink(target, to)
        .map_err(|e| format!("cannot write {}: {e}", to.display()))?;
    Ok(())
}

/// The table of the CRC-32 of gzip (ISO 3309), one entry per byte.
const CRC: [u32; 256] = {
    let mut table = [0u32; 256];
    let mut i = 0;
    while i < 256 {
        #[expect(clippy::cast_possible_truncation, reason = "i is under 256")]
        let mut c = i as u32;
        let mut k = 0;
        while k < 8 {
            c = if c & 1 == 1 {
                c >> 1 ^ 0xedb8_8320
            } else {
                c >> 1
            };
            k += 1;
        }
        table[i] = c;
        i += 1;
    }
    table
};

/// The CRC-32 of `bytes`, which ends a gzip stream.
fn crc32(bytes: &[u8]) -> u32 {
    !bytes.iter().fold(!0u32, |crc, &b| {
        CRC[usize::from(crc.to_le_bytes()[0] ^ b)] ^ crc >> 8
    })
}
