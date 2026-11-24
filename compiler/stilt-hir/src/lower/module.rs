//! A module: its header (program.module-header) and its items.

use std::sync::Arc;

use std::collections::BTreeSet;
use stilt_diag::{Diagnostic, Edit, Fix, codes};

use stilt_syntax::TextRange;
use stilt_syntax::ast::{self, AstNode};

use super::decls::declared_name;
use super::limits::implicit;
use super::{Anchors, ItemAnchors, ModuleResolution, Resolver, bare, dotted};
use crate::hir::{DeclId, Ident, Item, ItemHir, Limit, ModuleHir, Name, Ty};
use crate::scope::view::Lookup;

impl Resolver<'_> {
    /// The header (program.module-header): its path, which must be the module's name, and the
    /// limits of its `without`, each where it is written.
    pub(super) fn header(&mut self, header: Option<ast::Header>) -> Vec<(Limit, TextRange)> {
        let Some(header) = header else {
            return Vec::new();
        };
        let path = self.path(header.path());
        // A header writes the module's name in its package (packages.modules-of-dependencies).
        let local = &self.module.local;
        if self.module.valid
            && let Some(first) = path.first()
            && dotted(&path) != **local
        {
            let message = format!(
                "this file is module `{local}`, but its header says `{}`",
                dotted(&path)
            );
            let written = first.at.cover(path.last().map_or(first.at, |n| n.at));
            let name = Fix::new(
                format!("name the module `{local}`"),
                vec![Edit::replace(written, &**local)],
            );
            let d = Diagnostic::new(codes::E0201, first.at, message);
            self.diagnostics.push(d.with_fix(name));
        }
        self.header_limits(&header)
    }

    pub(super) fn module(mut self, tree: &ast::SourceFile) -> ModuleResolution {
        for item in tree.items() {
            if let ast::Item::TypeDecl(_) | ast::Item::Trait(_) = item
                && let Some(name) = declared_name(&item).and_then(|n| n.ident())
            {
                let start = self.at(item.syntax()).start();
                self.declared
                    .entry(Name::from(name.text()))
                    .or_insert(start);
            }
        }
        let header_limits = self.header(tree.header());
        let mut items = Items::default();
        for (index, item) in (0..).zip(tree.items()) {
            self.item(&mut items, index, &item);
        }
        // traits.inherent-names: a name is defined at most once across the inherent impl blocks of
        // a type. Only blocks in the type's home module count, since only they are allowed.
        for (_, names) in &items.inherent {
            self.check_unique("a member of this type", names);
        }
        self.references.sort_by_key(|&(_, at)| at.start());
        ModuleResolution {
            module: Arc::new(ModuleHir {
                name: self.module.name,
                std: self.module.std,
                limits: implicit(&header_limits),
                imports: items.imports.into_iter().collect(),
                items: items.resolved,
                poly_names: self.poly_names,
            }),
            bodies: self.bodies.into_iter().map(Arc::new).collect(),
            body_starts: self.body_starts,
            header_limits,
            diagnostics: self.diagnostics,
            references: self.references,
            anchors: items.anchors,
        }
    }

    /// Resolves the item at `index`, and records where its parts are.
    fn item(&mut self, items: &mut Items, index: u32, item: &ast::Item) {
        let id = DeclId {
            module: self.module.name,
            index,
        };
        let mut anchor = ItemAnchors {
            start: self.at(item.syntax()),
            name: None,
            variants: Vec::new(),
            impl_type: None,
            members: Vec::new(),
            wheres: Vec::new(),
        };
        let resolved = match item {
            ast::Item::Use(u) => {
                let written = dotted(&self.path(u.path()));
                let view = crate::scope::view::view_of(self.db, self.program, self.module.file);
                if let Lookup::Found(ns) = view.lookup(self.map, &written)
                    && self.map.is_module(&ns)
                {
                    // `meta use` is an import for cycles, and gives only procedural macros
                    // (macros.meta-use).
                    self.references.push((ns, anchor.start));
                    if !u.is_meta() {
                        items.imports.insert(ns);
                    }
                }
                ItemHir::Use
            }
            ast::Item::Impl(i) => {
                anchor.impl_type = i.self_ty().map(|t| self.at(bare(&t).syntax()));
                let (block, names, wheres) = self.impl_block(i, &id);
                anchor.members = names.iter().map(|n| n.at).collect();
                anchor.wheres = wheres;
                if block.trait_ref.is_none()
                    && let Ty::Con(owner, _) = &block.self_ty
                    && owner.home == self.module.name
                {
                    match items.inherent.iter_mut().find(|(o, _)| o == owner) {
                        Some((_, all)) => all.extend(names),
                        None => items.inherent.push((owner.clone(), names)),
                    }
                }
                ItemHir::Impl(block)
            }
            decl => {
                self.decl_anchors(decl, &mut anchor);
                ItemHir::Decl(self.decl(decl, &id))
            }
        };
        items.resolved.push(resolved);
        items.anchors.items.push(anchor);
    }

    /// Where a declaration's name is, and its variants' or methods' names.
    fn decl_anchors(&self, decl: &ast::Item, anchor: &mut ItemAnchors) {
        anchor.name = declared_name(decl).map(|n| self.name(Some(n), decl.syntax()).at);
        match decl {
            ast::Item::TypeDecl(t) => {
                if let Some(ast::TypeDef::VariantList(list)) = t.def() {
                    let names = list.variants().map(|v| self.name(v.name(), v.syntax()).at);
                    anchor.variants = names.collect();
                }
            }
            ast::Item::Trait(t) => {
                let names = t.members().map(|m| self.member_name(&m).at);
                anchor.members = names.collect();
            }
            _ => {}
        }
    }
}

/// A module's items as they are resolved.
#[derive(Default)]
struct Items {
    /// The modules that `use` declarations import.
    imports: BTreeSet<Name>,
    resolved: Vec<ItemHir>,
    anchors: Anchors,
    /// The names of the members of each of the module's types' inherent impl blocks.
    inherent: Vec<(Item, Vec<Ident>)>,
}
