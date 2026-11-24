//! A `use` whose path names no namespace (program.what-use-binds): read as a path in code is, it
//! may name an item of a module, which is E0230, and otherwise it names nothing, E0205.

use super::DefMap;
use super::paths::dotted;
use super::view::{Lookup, View};
use crate::hir::Name;
use crate::items::{DeclSummary, ItemSummary, ItemTree};

/// Whether a module whose items `tree` summarizes declares an item named `name`, in either
/// namespace: a function, a constant, a type or one of its variants, a trait, an effect or a
/// macro. A `use` declares no item of its module.
pub(crate) fn declares(tree: &ItemTree, name: &str) -> bool {
    tree.items.iter().any(|item| {
        let ItemSummary::Decl { kind, .. } = item else {
            return false;
        };
        match kind {
            DeclSummary::Fn(n)
            | DeclSummary::Const(n)
            | DeclSummary::Macro(n)
            | DeclSummary::Proc(n)
            | DeclSummary::Trait(n, _)
            | DeclSummary::Effect(n, _) => &**n == name,
            DeclSummary::Type {
                name: n, variants, ..
            } => &**n == name || variants.iter().any(|v| &**v == name),
            DeclSummary::Test(_) => false,
        }
    })
}

/// What a module of the program declares, as [`declares`] tells it, by the module's name in
/// the program and the item's name.
pub(crate) type ItemsOf<'a> = &'a dyn Fn(&str, &str) -> bool;

/// The number of names at the start of `path` that name the module whose item the path names:
/// the first start, from the shortest, that names a module which declares the name after it,
/// as a path in code reads `n.x` as the item `x` of `n`.
fn module_part(map: &DefMap, view: &View, path: &[Name], items_of: ItemsOf<'_>) -> Option<usize> {
    (1..path.len()).find(|&k| match view.lookup(map, &dotted(&path[..k])) {
        Lookup::Found(ns) => map.is_module(&ns) && items_of(&ns, &path[k]),
        Lookup::Unnamed | Lookup::Foreign(_) | Lookup::Missing => false,
    })
}

/// The message and fix of the E0230 of a `use`, or with `meta` a `meta use`, whose path names
/// an item of a module: the module to import, and the item as code names it through the
/// module.
pub(super) fn item_import(
    map: &DefMap,
    view: &View,
    path: &[Name],
    meta: bool,
    items_of: ItemsOf<'_>,
) -> Option<(String, (String, String))> {
    let k = module_part(map, view, path, items_of)?;
    let keyword = if meta { "meta use" } else { "use" };
    let module = dotted(&path[..k]);
    let named = dotted(&path[k - 1..]);
    let message = format!("`{keyword}` names a module: write `{keyword} {module}`, then `{named}`");
    Some((
        message,
        (format!("import `{module}`"), format!("{keyword} {module}")),
    ))
}
