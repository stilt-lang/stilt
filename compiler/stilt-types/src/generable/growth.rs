//! Whether a type holds infinitely many types (tests.growth-test), decided without expanding any
//! of them. The nodes are the type parameters of the declarations that the type holds; an edge
//! from `D.p` to `E.j` says that a field or payload of `D` holds `E` with an argument `j` in
//! which `p` occurs, and it grows when `p` occurs strictly inside that argument. The type holds
//! infinitely many types exactly when a cycle has a growing edge. The reference interpreter's
//! `Prop_types` makes the same test.

use std::collections::{HashMap, HashSet};

use stilt_hir::decls::{Lookup, TypeDefInfo};
use stilt_hir::hir::{GenericId, Item};

use crate::ty::Ty;

/// A type parameter of a declaration, by the declaration and the parameter's place.
type Node = (Item, usize);

/// An edge, and whether it grows.
type Edge = (Node, Node, bool);

/// Whether the types that `roots` hold are infinitely many.
pub(super) fn infinite(decls: &dyn Lookup, roots: &[Ty]) -> bool {
    let mut walk = Walk {
        decls,
        seen: HashSet::new(),
        queue: Vec::new(),
        edges: Vec::new(),
    };
    for root in roots {
        walk.holds(root, None);
    }
    while let Some(item) = walk.queue.pop() {
        walk.declaration(&item);
    }
    grows_in_a_cycle(&walk.edges)
}

struct Walk<'a> {
    decls: &'a dyn Lookup,
    seen: HashSet<Item>,
    queue: Vec<Item>,
    edges: Vec<Edge>,
}

impl Walk<'_> {
    /// The edges of a declaration's fields and payloads, in terms of its parameters.
    fn declaration(&mut self, item: &Item) {
        let Some(info) = self.decls.type_info(item) else {
            return;
        };
        let held: Vec<_> = match &info.def {
            TypeDefInfo::Record(fields) => fields.iter().map(|(_, t)| t).collect(),
            TypeDefInfo::Variants(vs) => vs.iter().flat_map(|(_, p)| p.iter()).collect(),
            TypeDefInfo::Builtin => return,
        };
        let owner = (item.clone(), info.params.as_slice());
        for t in held {
            self.holds(&Ty::from_hir(t, None), Some(&owner));
        }
    }

    /// The edges that `ty` gives when it is held by `owner`, a declaration with its parameters.
    fn holds(&mut self, ty: &Ty, owner: Option<&(Item, &[GenericId])>) {
        match ty {
            Ty::Tuple(ts) => {
                for t in ts {
                    self.holds(t, owner);
                }
            }
            Ty::Con(item, args) => {
                if self.is_declared(item) {
                    if let Some((from, params)) = owner {
                        for (j, a) in args.iter().enumerate() {
                            for (i, p) in params.iter().enumerate() {
                                if occurs(a, p) {
                                    let grows = *a != Ty::Param(p.clone());
                                    self.edges
                                        .push(((from.clone(), i), (item.clone(), j), grows));
                                }
                            }
                        }
                    }
                    if self.seen.insert(item.clone()) {
                        self.queue.push(item.clone());
                    }
                }
                for t in args {
                    self.holds(t, owner);
                }
            }
            _ => {}
        }
    }

    fn is_declared(&self, item: &Item) -> bool {
        self.decls
            .type_info(item)
            .is_some_and(|i| !matches!(i.def, TypeDefInfo::Builtin))
    }
}

fn occurs(ty: &Ty, p: &GenericId) -> bool {
    match ty {
        Ty::Param(q) => q == p,
        Ty::Con(_, ts) | Ty::Tuple(ts) => ts.iter().any(|t| occurs(t, p)),
        Ty::Fn(f) => f.params.iter().any(|(_, t)| occurs(t, p)) || occurs(&f.ret, p),
        Ty::Spread(s) => occurs(&s.pack, p) || occurs(&s.elem, p),
        Ty::Handler(_) | Ty::SelfTy | Ty::App(..) | Ty::Var(_) | Ty::Value(_) | Ty::Error => false,
    }
}

/// Whether some growing edge lies on a cycle: its target reaches its source.
fn grows_in_a_cycle(edges: &[Edge]) -> bool {
    let mut next: HashMap<&Node, Vec<&Node>> = HashMap::new();
    for (from, to, _) in edges {
        next.entry(from).or_default().push(to);
    }
    edges.iter().any(|(from, to, grows)| {
        if !grows {
            return false;
        }
        let mut seen = HashSet::new();
        let mut stack = vec![to];
        while let Some(n) = stack.pop() {
            if n == from {
                return true;
            }
            if seen.insert(n) {
                stack.extend(next.get(n).into_iter().flatten());
            }
        }
        false
    })
}
