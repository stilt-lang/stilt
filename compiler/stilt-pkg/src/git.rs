//! Reading a git repository (packages.dependencies): its tags, and the files of the tree each tag
//! names. A repository on the machine, as a `file://` source names it, has its objects read loose
//! or from packs; one that `HOST/PATH` names is reached over HTTPS ([`remote`]). All of it is
//! portable Rust, so that no `git` needs installing (goal one-tool).

mod pack;
pub(crate) mod remote;
mod stream;
mod tree;

use std::fs;
use std::path::{Path, PathBuf};

use crate::hash::Files;
use pack::{Found, Pack};

/// An object's id: its SHA-1, as git names it.
pub type Id = [u8; 20];

/// The largest object the reader inflates, and the largest answer it takes from a server: 1 GiB.
/// A size a pack or a server declares is never allocated past it.
pub(crate) const MAX_OBJECT: usize = 1 << 30;

/// The kinds of object a repository holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    Commit,
    Tree,
    Blob,
    Tag,
}

/// What finds a repository's objects by id.
pub(crate) trait Objects {
    /// The object `id`, with its kind.
    ///
    /// # Errors
    ///
    /// A message for people, when the object can't be had.
    fn object(&self, id: Id) -> Result<(Kind, Vec<u8>), String>;
}

/// A repository: its git directory, and its packs.
#[derive(Debug)]
pub struct Repo {
    git_dir: PathBuf,
    packs: Vec<Pack>,
}

impl Repo {
    /// The repository at `path`: a working tree holding `.git`, or a bare repository.
    ///
    /// # Errors
    ///
    /// A message for people, when `path` holds no repository.
    pub fn open(path: &Path) -> Result<Self, String> {
        let dot_git = path.join(".git");
        let git_dir = if dot_git.is_dir() {
            dot_git
        } else if let Ok(link) = fs::read_to_string(&dot_git) {
            let target = link
                .trim()
                .strip_prefix("gitdir: ")
                .unwrap_or("")
                .to_owned();
            path.join(target)
        } else if path.join("objects").is_dir() && path.join("refs").is_dir() {
            path.to_path_buf()
        } else {
            return Err(format!("{} holds no repository", path.display()));
        };
        let packs = Pack::all(&git_dir.join("objects/pack"))?;
        Ok(Self { git_dir, packs })
    }

    /// The repository's tags, each with the object it names.
    ///
    /// # Errors
    ///
    /// A message for people, when its refs can't be read.
    pub fn tags(&self) -> Result<Vec<(String, Id)>, String> {
        let mut tags = Vec::new();
        if let Ok(packed) = fs::read_to_string(self.git_dir.join("packed-refs")) {
            for line in packed.lines() {
                let Some((hex, name)) = line.split_once(' ') else {
                    continue;
                };
                if let (Some(id), Some(tag)) = (parse_id(hex), name.strip_prefix("refs/tags/")) {
                    tags.push((tag.to_owned(), id));
                }
            }
        }
        let dir = self.git_dir.join("refs/tags");
        if dir.is_dir() {
            loose_refs(&dir, "", &mut tags)
                .map_err(|e| format!("cannot read {}: {e}", dir.display()))?;
        }
        tags.sort();
        tags.dedup_by(|a, b| a.0 == b.0);
        Ok(tags)
    }

    /// The files that building the package at `id`, a tag or a commit, reads: its manifest and
    /// the `.lt` files under `src/`. `None` when the tree holds no `stilt.toml` at its root.
    ///
    /// # Errors
    ///
    /// A message for people, when an object can't be read.
    pub fn files_at(&self, id: Id) -> Result<Option<Files>, String> {
        files_at(self, id)
    }
}

/// The files that building the package at `id`, a tag or a commit of `objects`, reads, or
/// `None` when its tree holds no `stilt.toml` at its root.
pub(crate) fn files_at(objects: &dyn Objects, id: Id) -> Result<Option<Files>, String> {
    let files = tree::files(objects, tree_of(objects, id)?)?;
    if !files.iter().any(|(path, _)| path == "stilt.toml") {
        return Ok(None);
    }
    Ok(Some(files))
}

/// The tree that a tag or a commit names.
fn tree_of(objects: &dyn Objects, mut id: Id) -> Result<Id, String> {
    loop {
        let (kind, data) = objects.object(id)?;
        let field = |name: &str| {
            header_field(&data, name).ok_or_else(|| format!("a {kind:?} without `{name}`"))
        };
        match kind {
            Kind::Tag => id = field("object")?,
            Kind::Commit => return field("tree"),
            Kind::Tree => return Ok(id),
            Kind::Blob => return Err("a tag that names a file".to_owned()),
        }
    }
}

impl Objects for Repo {
    fn object(&self, id: Id) -> Result<(Kind, Vec<u8>), String> {
        read(self, id)
    }
}

/// The object `id` that `bases` finds, with its deltas applied.
fn read(bases: &dyn Bases, id: Id) -> Result<(Kind, Vec<u8>), String> {
    match bases.find(id)? {
        Found::Packed(pack, offset) => pack.read(offset, bases),
        Found::Whole(kind, data) => Ok((kind, data)),
    }
}

/// What finds an object by id, and the base of a delta.
trait Bases {
    /// Where the object `id` is.
    ///
    /// # Errors
    ///
    /// A message for people, when the object can't be had.
    fn find(&self, id: Id) -> Result<Found<'_>, String>;
}

impl Bases for Repo {
    fn find(&self, id: Id) -> Result<Found<'_>, String> {
        let hex = to_hex(&id);
        let loose = self.git_dir.join("objects").join(&hex[..2]).join(&hex[2..]);
        if let Ok(compressed) = fs::read(&loose) {
            let raw = inflate(&compressed)?;
            let nul = raw
                .iter()
                .position(|&b| b == 0)
                .ok_or("a malformed object")?;
            let kind = match raw[..nul].split(|&b| b == b' ').next() {
                Some(b"commit") => Kind::Commit,
                Some(b"tree") => Kind::Tree,
                Some(b"blob") => Kind::Blob,
                Some(b"tag") => Kind::Tag,
                _ => return Err(format!("object {hex} has an unknown kind")),
            };
            return Ok(Found::Whole(kind, raw[nul + 1..].to_vec()));
        }
        packed(&self.packs, id).ok_or_else(|| format!("the repository lacks object {hex}"))
    }
}

/// Where the first of `packs` that holds `id` holds it.
fn packed(packs: &[Pack], id: Id) -> Option<Found<'_>> {
    packs
        .iter()
        .find_map(|pack| Some(Found::Packed(pack, pack.find(&id)?)))
}

/// Packs with no repository around them, whose deltas' bases are in the packs themselves.
struct Packs(Vec<Pack>);

impl Bases for Packs {
    fn find(&self, id: Id) -> Result<Found<'_>, String> {
        packed(&self.0, id).ok_or_else(|| format!("no object {}", to_hex(&id)))
    }
}

/// Reads every object that `index` lists from the pack `data`, as a repository on the machine
/// reads its packs, and says how many there are: the reader's whole path through bytes that no
/// repository vouches for, which a fuzzer drives.
///
/// # Errors
///
/// A message for people, when the index or the pack is corrupt.
pub fn read_indexed(index: Vec<u8>, data: Vec<u8>) -> Result<usize, String> {
    let pack = Pack::new(index, data).ok_or("not a pack index of version 2")?;
    let count = pack.count().ok_or("a corrupt index")?;
    let ids: Vec<Id> = (0..count).map_while(|i| pack.id(i)).collect();
    let packs = Packs(vec![pack]);
    for id in ids {
        read(&packs, id)?;
    }
    Ok(count)
}

/// Reads every object of `pack`, as a remote sends one (packages.fetching), and says how many
/// there are, as [`read_indexed`] does for a pack on the machine.
///
/// # Errors
///
/// A message for people, when the pack is corrupt.
pub fn read_sent(pack: &[u8]) -> Result<usize, String> {
    stream::read(pack).map(|loaded| loaded.count())
}

/// The loose refs under `dir`, each named by its path from the refs' root.
fn loose_refs(dir: &Path, prefix: &str, tags: &mut Vec<(String, Id)>) -> std::io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let name = format!("{prefix}{}", entry.file_name().to_string_lossy());
        if entry.file_type()?.is_dir() {
            loose_refs(&entry.path(), &format!("{name}/"), tags)?;
        } else if let Some(id) = parse_id(fs::read_to_string(entry.path())?.trim()) {
            tags.retain(|(t, _)| *t != name);
            tags.push((name, id));
        }
    }
    Ok(())
}

/// The value of a header line `name VALUE` of a commit or a tag, as an id.
fn header_field(data: &[u8], name: &str) -> Option<Id> {
    let text = std::str::from_utf8(data).ok()?;
    let line = text
        .lines()
        .take_while(|l| !l.is_empty())
        .find_map(|l| l.strip_prefix(name).and_then(|rest| rest.strip_prefix(' ')))?;
    parse_id(line)
}

pub(crate) fn parse_id(hex: &str) -> Option<Id> {
    if hex.len() != 40 {
        return None;
    }
    let mut id = [0; 20];
    for (i, byte) in id.iter_mut().enumerate() {
        *byte = u8::from_str_radix(hex.get(2 * i..2 * i + 2)?, 16).ok()?;
    }
    Some(id)
}

pub(crate) fn to_hex(id: &Id) -> String {
    use std::fmt::Write as _;
    id.iter().fold(String::new(), |mut out, b| {
        let _ = write!(out, "{b:02x}");
        out
    })
}

pub(crate) fn inflate(compressed: &[u8]) -> Result<Vec<u8>, String> {
    miniz_oxide::inflate::decompress_to_vec_zlib_with_limit(compressed, MAX_OBJECT)
        .map_err(|e| format!("a corrupt object: {e:?}"))
}
