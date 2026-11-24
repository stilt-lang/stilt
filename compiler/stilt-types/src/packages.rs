//! What packages do to the world, and the diagnostics of their manifests
//! (packages.dependencies-with-errors, packages.grants, packages.own-effects,
//! packages.ungranted-effects and packages.running-with-ungranted-effect; facts.capability-grants,
//! facts.own-capabilities and facts.ungranted-capabilities).
//!
//! A package's own code has a capability when one of its functions or methods, or a closure in
//! one, calls or names a function of another package that has it, and performs `io` without one
//! when it names a function of another package whose declared row holds `io` and that has no
//! capability. The items a body names are those that its implicit effects follow (facts.inference
//! and facts.calls-through-function-values), so a call through a function value names nothing, and
//! the effects that a caller's function brings are the caller's.

mod fetched;
mod grants;

pub(crate) use grants::ungranted_entries;
pub use grants::{diagnostics, ungranted};

use stilt_db::{Db, Program, SourceFile};
use stilt_diag::Diagnostic;
use stilt_hir::decls::{Lookup, QueriedOnce};
use stilt_hir::hir::{Capability, Item, Name};
use stilt_hir::{body_starts, def_map};
use stilt_syntax::TextSize;

use stilt_hir::hir::walk::{Visitor, walk_body, walk_expr};

use crate::analyses::implicit::{Effect, Effects, Key, code_sites};
use crate::owners::{BodyOwner, Place};
use crate::queries::{
    body_count, body_diagnostics, body_owner, implicit_effects, module_info, scope,
};

/// What a dependency's own code needs a grant for: a capability, or `io` without one
/// (facts.own-capabilities and facts.ungranted-capabilities), in the order of facts.capabilities
/// and then `io`, and then an `unsafe` block (c.granting-unsafe).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Need {
    /// A capability below `io`.
    Capability(Capability),
    /// `io` without a capability.
    Io,
    /// An `unsafe` block.
    Unsafe,
}

impl Need {
    /// Whether `grant` grants it: `io` grants everything, and a capability itself
    /// (facts.capability-grants).
    #[must_use]
    pub fn granted(self, grant: stilt_db::Grant) -> bool {
        match self {
            Need::Capability(c) => grant.io || grant.capabilities.has(c),
            Need::Io => grant.io,
            Need::Unsafe => grant.unsafe_code,
        }
    }

    /// The need as a grant writes it.
    #[must_use]
    pub fn text(self) -> &'static str {
        match self {
            Need::Capability(c) => c.text(),
            Need::Io => "io",
            Need::Unsafe => "unsafe",
        }
    }

    /// What code that has the need does, as messages say it.
    #[must_use]
    pub fn verb(self) -> String {
        match self {
            Need::Capability(c) => format!("uses `{}`", c.text()),
            Need::Io => "performs `io`".to_owned(),
            Need::Unsafe => "holds an `unsafe` block".to_owned(),
        }
    }
}

/// A function of a package whose own code has a capability, or performs `io` without one, and
/// the first operation that does.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IoCall {
    /// The file that declares the function.
    pub file: SourceFile,
    /// The function's body, by its index in its file, or `None` for a macro, whose templates
    /// name what it needs (macros.expansion-effects).
    pub body: Option<u32>,
    /// The function's address (edits.paths).
    pub function: String,
    /// The function it calls or names, as code writes it.
    pub callee: String,
    /// Where it does, in its file.
    pub at: TextSize,
    /// What it needs a grant for.
    pub need: Need,
}

/// The functions of the package `package` whose own code has a capability or performs `io`
/// (packages.own-effects; facts.own-capabilities), once for each need, in the order of their files'
/// paths and then of their source.
#[salsa::tracked(returns(ref))]
pub fn io_calls(db: &dyn Db, program: Program, package: u32) -> Vec<IoCall> {
    let Some(info) = program.packages(db).list.get(package as usize) else {
        return Vec::new();
    };
    let decls = QueriedOnce::new(db, program);
    let effects = implicit_effects(db, program);
    let mut found = Vec::new();
    for &file in &info.files {
        let module = module_info(db, program, file);
        let starts = body_starts(db, program, file);
        for index in 0..body_count(db, program, file) {
            let owner = body_owner(db, program, file, index);
            let (Some(key), BodyOwner::Fn { name, place, .. }) = (owner.key(module.name), owner)
            else {
                continue;
            };
            // A body with an error performs no effect of its own (packages.own-effects).
            if body_diagnostics(db, program, file, index)
                .iter()
                .any(Diagnostic::is_error)
            {
                continue;
            }
            let scope = scope(db, program, file, index, Some(&key));
            let Some(sites) = code_sites(&decls, &scope) else {
                continue;
            };
            // c.unsafe-in-api and c.granting-unsafe: its first `unsafe` block.
            let hir = stilt_hir::module_body(db, program, file, index);
            if let Some(first) = hir.unsafe_blocks.first() {
                found.push(IoCall {
                    file,
                    body: Some(index),
                    function: address(module.name, *name, place),
                    callee: String::new(),
                    at: first.at.start() + starts[index as usize],
                    need: Need::Unsafe,
                });
            }
            let outside = |k: &Key| outside_package(db, program, &decls, k, package);
            let in_code = sites
                .iter()
                .flat_map(|s| s.names().iter().map(move |k| (k, s.at().start())));
            let quoted = quoted_names(hir);
            let named = in_code.chain(quoted.iter().map(|(k, at)| (k, *at)));
            for (need, callee, at) in needs(&decls, effects, named, &outside) {
                found.push(IoCall {
                    file,
                    body: Some(index),
                    function: address(module.name, *name, place),
                    callee: self::callee(callee),
                    at: at + starts[index as usize],
                    need,
                });
            }
        }
        found.extend(macro_needs(db, program, file, &decls, &|k| {
            outside_package(db, program, &decls, k, package)
        }));
    }
    found
}

/// What the templates of a file's macros need a grant for: the capabilities, and `io`, of the
/// functions of other packages they name, which are their package's, as a call into it would
/// be (macros.expansion-effects).
fn macro_needs(
    db: &dyn Db,
    program: Program,
    file: SourceFile,
    decls: &dyn Lookup,
    outside: &dyn Fn(&Key) -> bool,
) -> Vec<IoCall> {
    let module = stilt_hir::module_hir(db, program, file);
    let effects = implicit_effects(db, program);
    let defs = stilt_hir::macros::macro_defs(db, file);
    let mut found = Vec::new();
    for item in &module.items {
        let stilt_hir::hir::ItemHir::Decl(decl) = item else {
            continue;
        };
        let stilt_hir::hir::DeclKind::Macro(m) = &decl.kind else {
            continue;
        };
        let keys: Vec<Key> = m.names.iter().cloned().map(Key::Function).collect();
        let mut needs: Vec<(Need, &Key)> = Vec::new();
        for key in keys.iter().filter(|k| outside(k)) {
            let has: Vec<Need> = Capability::ALL
                .into_iter()
                .filter(|&c| effects.has(Effect::Capability(c), key))
                .map(Need::Capability)
                .collect();
            let has = if has.is_empty() && performs_io(decls, key) {
                vec![Need::Io]
            } else {
                has
            };
            for need in has {
                if !needs.iter().any(|(n, _)| *n == need) {
                    needs.push((need, key));
                }
            }
        }
        needs.sort_by_key(|(need, _)| *need);
        for (need, key) in needs {
            let callee = self::callee(key);
            let first = callee.split('.').next().unwrap_or_default();
            let at = defs
                .get(&m.name)
                .and_then(|def| def.written(first))
                .map_or(TextSize::default(), stilt_syntax::TextRange::start);
            found.push(IoCall {
                file,
                body: None,
                function: format!("{}.{}!", module.name, m.name),
                callee,
                at,
                need,
            });
        }
    }
    found
}

/// The functions that the quotes of a body name, which an expansion of them names in its
/// package's name, each at its quote (macros.expansion-effects).
fn quoted_names(body: &stilt_hir::hir::Body) -> Vec<(Key, TextSize)> {
    struct Quotes(Vec<(Key, TextSize)>);
    impl Visitor for Quotes {
        fn expr(&mut self, e: &stilt_hir::hir::Expr) {
            if let stilt_hir::hir::ExprKind::Quote(q) = &e.kind {
                let at = e.at.start();
                self.0
                    .extend(q.names.iter().map(|item| (Key::Function(item.clone()), at)));
            }
            walk_expr(self, e);
        }
    }
    let mut quotes = Quotes(Vec::new());
    walk_body(&mut quotes, body);
    quotes.0
}

/// What the items a body names need a grant for, each with the first item of another package
/// that gives the need and where it is named: each capability of such an item, and `io` for one
/// whose declared row holds `io` and that has no capability (facts.own-capabilities).
fn needs<'s>(
    decls: &dyn Lookup,
    effects: &Effects,
    named: impl Iterator<Item = (&'s Key, TextSize)>,
    outside: &dyn Fn(&Key) -> bool,
) -> Vec<(Need, &'s Key, TextSize)> {
    let mut found: Vec<(Need, &Key, TextSize)> = Vec::new();
    let mut add = |need: Need, key, at| {
        if !found.iter().any(|(n, ..)| *n == need) {
            found.push((need, key, at));
        }
    };
    for (key, at) in named.filter(|(k, _)| outside(k)) {
        let mut any = false;
        for c in Capability::ALL {
            if effects.has(Effect::Capability(c), key) {
                any = true;
                add(Need::Capability(c), key, at);
            }
        }
        if !any && performs_io(decls, key) {
            add(Need::Io, key, at);
        }
    }
    found.sort_by_key(|(need, ..)| *need);
    found
}

/// Whether the item that `key` names declares `io` in its row.
fn performs_io(decls: &dyn Lookup, key: &Key) -> bool {
    let signature = match key {
        Key::Function(item) => decls.function(item),
        Key::Member(owner, name) => decls
            .inherent_members(owner)
            .iter()
            .find(|m| m.name == *name)
            .map(|m| &m.signature),
        Key::ImplMethod(trait_item, owner, name) => decls
            .trait_impl(trait_item, owner)
            .and_then(|i| i.members.iter().find(|m| m.name == *name))
            .map(|m| &m.signature),
        Key::DefaultMethod(trait_item, name) => decls
            .trait_info(trait_item)
            .and_then(|t| t.methods.iter().find(|m| m.name == *name))
            .map(|m| &m.signature),
        Key::BuiltIn(..) => None,
    };
    signature.is_some_and(|s| s.row.io)
}

/// Whether the item that `key` names is declared outside the package `package`.
fn outside_package(
    db: &dyn Db,
    program: Program,
    decls: &dyn Lookup,
    key: &Key,
    package: u32,
) -> bool {
    !in_package(db, program, decls, key, package)
}

/// Whether the item that `key` names is declared in the package `package`.
fn in_package(db: &dyn Db, program: Program, decls: &dyn Lookup, key: &Key, package: u32) -> bool {
    let home = match key {
        Key::Function(item) | Key::Member(item, _) | Key::DefaultMethod(item, _) => item.home,
        Key::ImplMethod(trait_item, owner, _) => match decls.trait_impl(trait_item, owner) {
            Some(i) => i.module,
            None => return false,
        },
        Key::BuiltIn(..) => return true,
    };
    module_package(db, program, &home) == Some(package)
}

/// The package of the module `name`, or `None` for the standard library's.
fn module_package(db: &dyn Db, program: Program, name: &str) -> Option<u32> {
    let module = def_map(db, program).module(name).filter(|m| !m.std)?;
    u32::try_from(stilt_db::package_of(db, program, module.file)).ok()
}

/// A function, as code calls it: `print`, `fs.read_lines`, `Point.norm`.
fn callee(key: &Key) -> String {
    let qualified = |item: &Item| match item.home.rsplit('.').next() {
        _ if &*item.home == "std.prelude" => item.name.to_string(),
        Some(last) => format!("{last}.{}", item.name),
        None => item.name.to_string(),
    };
    match key {
        Key::Function(item) => qualified(item),
        Key::Member(owner, name) => format!("{}.{name}", owner.name),
        Key::ImplMethod(trait_item, _, name)
        | Key::DefaultMethod(trait_item, name)
        | Key::BuiltIn(trait_item, name) => format!("{}.{name}", trait_item.name),
    }
}

/// A function's address, by its module and place (edits.paths).
fn address(module: Name, name: Name, place: &Place) -> String {
    match place {
        Place::Impl {
            trait_item: Some(t),
            owner: Some(o),
        } => format!("{module}.{}.{}.{name}", o.name, t.name),
        Place::Impl { owner: Some(o), .. } => format!("{module}.{}.{name}", o.name),
        Place::Module | Place::Impl { owner: None, .. } => format!("{module}.{name}"),
        Place::Trait(t) => format!("{module}.{}.{name}", t.name),
    }
}
