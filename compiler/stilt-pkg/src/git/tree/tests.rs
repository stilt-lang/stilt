//! The files that a tag's tree gives its package, on trees built in memory with links, hidden
//! entries and cycles (program.module-names, packages.content-hash).

use std::collections::HashMap;

use super::super::{Id, Kind, Objects};
use super::files;

/// A repository's objects, made one at a time.
#[derive(Default)]
struct Store {
    objects: HashMap<Id, (Kind, Vec<u8>)>,
}

impl Objects for Store {
    fn object(&self, id: Id) -> Result<(Kind, Vec<u8>), String> {
        self.objects
            .get(&id)
            .cloned()
            .ok_or_else(|| "no such object".to_owned())
    }
}

impl Store {
    fn add(&mut self, kind: Kind, data: &[u8]) -> Id {
        let mut id = [0; 20];
        id[..8].copy_from_slice(&(self.objects.len() as u64 + 1).to_le_bytes());
        self.objects.insert(id, (kind, data.to_vec()));
        id
    }

    fn blob(&mut self, text: &str) -> (&'static str, Id) {
        ("100644", self.add(Kind::Blob, text.as_bytes()))
    }

    fn link(&mut self, target: &str) -> (&'static str, Id) {
        ("120000", self.add(Kind::Blob, target.as_bytes()))
    }

    fn tree(&mut self, entries: &[(&str, (&str, Id))]) -> (&'static str, Id) {
        let mut data = Vec::new();
        for (name, (mode, id)) in entries {
            data.extend(format!("{mode} {name}\0").as_bytes());
            data.extend(id);
        }
        ("40000", self.add(Kind::Tree, &data))
    }
}

fn paths(store: &Store, root: Id) -> Vec<String> {
    let mut paths: Vec<String> = files(store, root)
        .unwrap()
        .into_iter()
        .map(|(path, _)| path)
        .collect();
    paths.sort();
    paths
}

#[test]
fn hidden_entries_are_no_part_of_the_package() {
    let mut s = Store::default();
    let manifest = s.blob("[package]\nname = \"csv\"\n");
    let main = s.blob("pub fn f() -> i64 { 1 }\n");
    let cache = s.tree(&[("x.lt", main)]);
    let src = s.tree(&[(".cache", cache), (".notes.lt", main), ("main.lt", main)]);
    let (_, root) = s.tree(&[("stilt.toml", manifest), ("src", src)]);
    assert_eq!(paths(&s, root), ["src/main.lt", "stilt.toml"]);
}

#[test]
fn links_are_followed_at_their_paths_but_not_into_cycles() {
    let mut s = Store::default();
    let manifest = s.blob("[package]\nname = \"csv\"\n");
    let main = s.blob("pub fn f() -> i64 { 1 }\n");
    let (up, back, outside, absolute) = (
        s.link(".."),
        s.link("../a"),
        s.link("../../../x.lt"),
        s.link("/etc/x.lt"),
    );
    let a = s.tree(&[("one.lt", main), ("up", up)]);
    let b = s.tree(&[("back", back), ("lost.lt", outside), ("root.lt", absolute)]);
    let (to_shared, to_util, to_src, dangling) = (
        s.link("../shared"),
        s.link("../shared/util.lt"),
        s.link("src"),
        s.link("missing.lt"),
    );
    let shared = s.tree(&[("util.lt", main)]);
    let src = s.tree(&[
        ("a", a),
        ("b", b),
        ("lib", to_shared),
        ("main.lt", main),
        ("nothing.lt", dangling),
        ("tool.lt", to_util),
    ]);
    let (_, root) = s.tree(&[
        ("stilt.toml", manifest),
        ("shared", shared),
        ("source", to_src),
        ("src", src),
    ]);
    assert_eq!(
        paths(&s, root),
        [
            "src/a/one.lt",
            "src/b/back/one.lt",
            "src/lib/util.lt",
            "src/main.lt",
            "src/tool.lt",
            "stilt.toml"
        ]
    );
}

#[test]
fn a_linked_src_is_the_module_root() {
    let mut s = Store::default();
    let manifest = s.blob("[package]\nname = \"csv\"\n");
    let main = s.blob("pub fn f() -> i64 { 1 }\n");
    let code = s.tree(&[("main.lt", main)]);
    let to_code = s.link("code");
    let (_, root) = s.tree(&[("stilt.toml", manifest), ("code", code), ("src", to_code)]);
    assert_eq!(paths(&s, root), ["src/main.lt", "stilt.toml"]);
}
