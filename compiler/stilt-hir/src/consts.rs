//! Constants that refer to each other in a cycle (declarations.constant-cycles).

use std::collections::{BTreeSet, HashMap};

use stilt_db::{Db, Program, SourceFile};

use crate::Anchor;
use crate::decls::{MemberKindInfo, declarations};
use crate::hir::walk::{Visitor, walk_body, walk_expr, walk_pat};
use crate::hir::{
    DeclKind, Expr, ExprKind, Fallback, Item, ItemHir, MemberKind, MemberOwner, Name, Pat, PatKind,
    Ty, TypeRef,
};
use crate::lower::resolve_module;
use crate::scope::def_map;

/// A constant: one of a module, or one of a type, which its inherent impl blocks declare.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Constant {
    Global(Item),
    Assoc(Item, Name),
}

/// A constant that has a value, with the constants its value names.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Valued {
    key: Constant,
    /// Where its name is: the item, and the member of an impl block.
    item: u32,
    member: Option<u32>,
    named: Vec<Constant>,
}

impl Valued {
    fn anchor(&self) -> Anchor {
        match self.member {
            None => Anchor::Name(self.item),
            Some(j) => Anchor::Member(self.item, j),
        }
    }
}

/// The constants of a file's module that have values, in source order, with the constants
/// each one's value names, as type checking finds them.
#[salsa::tracked(returns(ref))]
pub(crate) fn valued_constants(db: &dyn Db, program: Program, file: SourceFile) -> Vec<Valued> {
    let resolution = resolve_module(db, program, file);
    let decls = declarations(db, program);
    let module = &resolution.module;
    let named = |index: crate::hir::BodyIndex| {
        let mut found = Names {
            decls,
            found: Vec::new(),
        };
        walk_body(&mut found, &resolution.bodies[index.0 as usize]);
        found.found
    };
    let mut valued = Vec::new();
    for (i, item) in (0..).zip(&module.items) {
        match item {
            ItemHir::Decl(decl) => {
                if let DeclKind::Const(c) = &decl.kind {
                    let key = Constant::Global(Item {
                        home: module.name,
                        name: c.name,
                    });
                    valued.push(Valued {
                        key,
                        item: i,
                        member: None,
                        named: named(c.value),
                    });
                }
            }
            ItemHir::Impl(block) => {
                let Ty::Con(owner, _) = &block.self_ty else {
                    continue;
                };
                for (j, member) in (0..).zip(&block.members) {
                    if let MemberKind::Const(c) = &member.kind {
                        valued.push(Valued {
                            key: Constant::Assoc(owner.clone(), c.name),
                            item: i,
                            member: Some(j),
                            named: named(c.value),
                        });
                    }
                }
            }
            ItemHir::Use => {}
        }
    }
    valued
}

/// The constants that a body names.
struct Names<'a> {
    decls: &'a crate::decls::Declarations,
    found: Vec<Constant>,
}

impl Names<'_> {
    /// A constant of a type, named as `Type.NAME`: one of its inherent impls
    /// (declarations.impl-constants), or one of a trait impl, which its trait's constant names
    /// (traits.trait-constants), so that a constant the trait doesn't declare, E0306, is no member.
    fn member(&mut self, ty: &TypeRef, name: Name) {
        let Ty::Con(item, _) = &ty.ty else { return };
        let constant = |members: &[crate::decls::MemberInfo]| {
            members
                .iter()
                .any(|m| m.name == name && m.kind == MemberKindInfo::Constant)
        };
        let declared = |t: &crate::hir::Item| {
            self.decls
                .traits
                .get(t)
                .is_some_and(|info| info.methods.iter().any(|m| m.name == name))
        };
        let of_trait = self
            .decls
            .trait_impls
            .iter()
            .any(|((t, owner), imp)| owner == item && constant(&imp.members) && declared(t));
        if constant(self.decls.inherent_members(item)) || of_trait {
            self.found.push(Constant::Assoc(item.clone(), name));
        }
    }
}

impl Visitor for Names<'_> {
    fn expr(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Const(item) => self.found.push(Constant::Global(item.clone())),
            ExprKind::Member(MemberOwner::Type(ty), name) => self.member(ty, name.name),
            _ => walk_expr(self, e),
        }
    }

    fn pat(&mut self, p: &Pat) {
        match &p.kind {
            PatKind::Const(item) => self.found.push(Constant::Global(item.clone())),
            PatKind::AssocConst(ty, name) => self.member(ty, name.name),
            // A constant's value holds a pattern only in an error
            // (declarations.constant-expressions), so the name is read as it is in scope.
            PatKind::Bare(_, _, fallback) => {
                if let Fallback::Const(item) = &**fallback {
                    self.found.push(Constant::Global(item.clone()));
                }
                walk_pat(self, p);
            }
            _ => walk_pat(self, p),
        }
    }
}

/// A group of constants in a cycle, reported at the name of its last constant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ConstCycle {
    pub(crate) file: SourceFile,
    pub(crate) at: Anchor,
}

/// declarations.constant-cycles: constants that refer to each other in a cycle. Each cycle is
/// reported once, at the name of its last constant (errors.primary-spans).
#[salsa::tracked(returns(ref))]
pub(crate) fn constant_cycles(db: &dyn Db, program: Program) -> Vec<ConstCycle> {
    let map = def_map(db, program);
    let mut modules: Vec<_> = map.modules.iter().filter(|m| !m.std).collect();
    modules.sort_by_key(|a| a.name);
    // Of two constants with the same name, only the first is the one names refer to.
    let mut constants: Vec<(SourceFile, &str, &Valued)> = Vec::new();
    for m in modules {
        for v in valued_constants(db, program, m.file) {
            if !constants.iter().any(|(_, _, c)| c.key == v.key) {
                constants.push((m.file, m.file.path(db), v));
            }
        }
    }
    let refers: HashMap<&Constant, &[Constant]> = constants
        .iter()
        .map(|(_, _, c)| (&c.key, c.named.as_slice()))
        .collect();
    let reach = |key: &Constant| {
        let mut seen = BTreeSet::new();
        let mut pending: Vec<&Constant> =
            refers.get(key).into_iter().flat_map(|n| n.iter()).collect();
        while let Some(k) = pending.pop() {
            if seen.insert(k.clone()) {
                pending.extend(refers.get(k).into_iter().flat_map(|n| n.iter()));
            }
        }
        seen
    };
    let reaches: HashMap<&Constant, BTreeSet<Constant>> = constants
        .iter()
        .map(|(_, _, c)| (&c.key, reach(&c.key)))
        .collect();
    let mut cyclic: Vec<_> = constants
        .iter()
        .filter(|(_, _, c)| reaches[&c.key].contains(&c.key))
        .collect();
    let mut cycles = Vec::new();
    while let Some(&&(_, _, first)) = cyclic.first() {
        let together = |c: &Valued| {
            reaches[&first.key].contains(&c.key) && reaches[&c.key].contains(&first.key)
        };
        let (group, others): (Vec<_>, Vec<_>) = cyclic
            .into_iter()
            .partition(|(_, _, c)| c.key == first.key || together(c));
        cyclic = others;
        if let Some((file, _, last)) = group
            .into_iter()
            .max_by(|(_, a, x), (_, b, y)| (a, x.item, x.member).cmp(&(b, y.item, y.member)))
        {
            cycles.push(ConstCycle {
                file: *file,
                at: last.anchor(),
            });
        }
    }
    cycles
}
