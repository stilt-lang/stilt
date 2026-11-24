//! The files of a tag's tree that building its package reads (packages.content-hash): the
//! manifest at the root and the files of the modules below `src/`, found as on disk
//! (program.module-names): through the tree's symbolic links, at the link's path, but for the
//! entries whose names start with `.` and the links that would make a cycle.

use super::{Id, Objects};
use crate::hash::{Files, is_built};

/// How many links a path may pass through before it names nothing, as on Linux.
const HOPS: usize = 40;

/// What an entry of a tree is.
#[derive(Clone, Copy)]
enum Node {
    Tree(Id),
    File(Id),
    Link(Id),
    /// A submodule, which a tree names but doesn't hold.
    Other,
}

struct Entry {
    name: String,
    node: Node,
}

/// A path from the root through trees alone, one name for each, and what it names.
type Real = (Node, Vec<String>);

struct Walk<'a> {
    objects: &'a dyn Objects,
    root: Id,
}

/// The files of the tree `root` that building its package reads.
pub(super) fn files(objects: &dyn Objects, root: Id) -> Result<Files, String> {
    let walk = Walk { objects, root };
    let mut files = Vec::new();
    for entry in walk.entries(root)? {
        if entry.name != "stilt.toml" && entry.name != "src" {
            continue;
        }
        match walk.follow(entry.node, &[], &entry.name, &mut HOPS.clone())? {
            Some((Node::File(id), _)) if entry.name == "stilt.toml" => {
                files.push((entry.name, objects.object(id)?.1));
            }
            Some((Node::Tree(id), real)) if entry.name == "src" => {
                walk.tree(id, "src", &mut vec![real], &mut files)?;
            }
            _ => {}
        }
    }
    Ok(files)
}

impl Walk<'_> {
    /// Adds the modules' files of `tree`, shown at `shown`, to `files`; `through` holds the real
    /// paths of the trees that the walk passes through to reach it, its own last.
    fn tree(
        &self,
        tree: Id,
        shown: &str,
        through: &mut Vec<Vec<String>>,
        files: &mut Files,
    ) -> Result<(), String> {
        let dir = through.last().cloned().unwrap_or_default();
        for entry in self.entries(tree)? {
            if entry.name.starts_with('.') {
                continue;
            }
            let path = format!("{shown}/{}", entry.name);
            let link = matches!(entry.node, Node::Link(_));
            let Some((node, real)) =
                self.follow(entry.node, &dir, &entry.name, &mut HOPS.clone())?
            else {
                continue;
            };
            match node {
                Node::Tree(id) => {
                    if link && through.iter().any(|d| d.starts_with(&real)) {
                        continue;
                    }
                    through.push(real);
                    self.tree(id, &path, through, files)?;
                    through.pop();
                }
                Node::File(id) if is_built(&path) => files.push((path, self.objects.object(id)?.1)),
                _ => {}
            }
        }
        Ok(())
    }

    /// What `node`, the entry `name` of the tree at `dir`, names once its links are followed, or
    /// `None` when it names nothing.
    fn follow(
        &self,
        node: Node,
        dir: &[String],
        name: &str,
        hops: &mut usize,
    ) -> Result<Option<Real>, String> {
        let mut real = dir.to_vec();
        real.push(name.to_owned());
        let Node::Link(id) = node else {
            return Ok(Some((node, real)));
        };
        if *hops == 0 {
            return Ok(None);
        }
        *hops -= 1;
        let target = String::from_utf8_lossy(&self.objects.object(id)?.1).into_owned();
        real.pop();
        self.resolve(real, &target, hops)
    }

    /// What the link target `target`, read from the tree at `real`, names, a name at a time; a
    /// target that leaves the tree names nothing.
    fn resolve(
        &self,
        mut real: Vec<String>,
        target: &str,
        hops: &mut usize,
    ) -> Result<Option<Real>, String> {
        if target.starts_with('/') {
            return Ok(None);
        }
        let mut node = Node::Tree(self.tree_at(&real)?);
        for part in target.split('/') {
            match (part, node) {
                ("" | ".", _) => {}
                ("..", Node::Tree(_)) => {
                    if real.pop().is_none() {
                        return Ok(None);
                    }
                    node = Node::Tree(self.tree_at(&real)?);
                }
                (_, Node::Tree(tree)) => {
                    let Some(entry) = self.entries(tree)?.into_iter().find(|e| e.name == part)
                    else {
                        return Ok(None);
                    };
                    let Some(found) = self.follow(entry.node, &real, part, hops)? else {
                        return Ok(None);
                    };
                    (node, real) = found;
                }
                _ => return Ok(None),
            }
        }
        Ok(Some((node, real)))
    }

    /// The tree at `real`, a path through trees alone.
    fn tree_at(&self, real: &[String]) -> Result<Id, String> {
        let mut tree = self.root;
        for part in real {
            let entry = self.entries(tree)?.into_iter().find(|e| e.name == *part);
            let Some(Entry {
                node: Node::Tree(id),
                ..
            }) = entry
            else {
                return Err("a tree that changed as it was read".to_owned());
            };
            tree = id;
        }
        Ok(tree)
    }

    /// The entries of the tree `tree`, in its order.
    fn entries(&self, tree: Id) -> Result<Vec<Entry>, String> {
        let (_, data) = self.objects.object(tree)?;
        let mut rest = &data[..];
        let mut entries = Vec::new();
        while !rest.is_empty() {
            let malformed = || "a malformed tree".to_owned();
            let space = rest.iter().position(|&b| b == b' ').ok_or_else(malformed)?;
            let nul = rest.iter().position(|&b| b == 0).ok_or_else(malformed)?;
            if nul + 21 > rest.len() || space > nul {
                return Err(malformed());
            }
            let mode = &rest[..space];
            let name = String::from_utf8_lossy(&rest[space + 1..nul]).into_owned();
            let mut id = [0; 20];
            id.copy_from_slice(&rest[nul + 1..nul + 21]);
            rest = &rest[nul + 21..];
            let node = match mode {
                b"40000" => Node::Tree(id),
                b"120000" => Node::Link(id),
                _ if mode.starts_with(b"100") => Node::File(id),
                _ => Node::Other,
            };
            entries.push(Entry { name, node });
        }
        Ok(entries)
    }
}

#[cfg(test)]
mod tests;
