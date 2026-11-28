//! What a type holds (cycles.can-form-cycle): itself, the types of its fields and variants, of
//! its elements and of its type arguments, with a declared type's arguments put where its
//! declaration places them. The thread axes read it (modes.mode-crossing): a type is contended
//! when it holds a `Shared<T>` and fixed when it holds a view, through a record's field as
//! through a type argument.

use std::collections::HashSet;

use stilt_hir::decls::{Lookup, TypeDefInfo};
use stilt_hir::hir::Item;

use crate::ty::{Ty, instantiate};

/// The types that a type constructor applied to `args` holds directly: a declared type's fields'
/// and payloads' types at `args`, and the arguments of any other.
pub(crate) fn declared(decls: &dyn Lookup, item: &Item, args: &[Ty]) -> Vec<Ty> {
    let Some(info) = decls.type_info(item) else {
        return args.to_vec();
    };
    let at = |t| instantiate(t, &info.params, args);
    match &info.def {
        TypeDefInfo::Record(fields) => fields.iter().map(|(_, t)| at(t)).collect(),
        TypeDefInfo::Variants(vs) => vs.iter().flat_map(|(_, ts)| ts.iter().map(at)).collect(),
        TypeDefInfo::Builtin => args.to_vec(),
    }
}

/// Whether a type holds a type that `p` accepts, at any depth. It also reads the parameters and
/// the result of a function type. A declared type met again inside itself adds only what its
/// arguments hold, so the walk of a recursive type ends, as the interpreter's does.
pub(crate) fn holds(decls: &dyn Lookup, ty: &Ty, p: &dyn Fn(&Ty) -> bool) -> bool {
    let mut walk = Walk {
        decls,
        p,
        none: HashSet::new(),
    };
    walk.holds(ty, &mut Vec::new())
}

struct Walk<'a> {
    decls: &'a dyn Lookup,
    p: &'a dyn Fn(&Ty) -> bool,
    /// The types found to hold nothing that `p` accepts, each with the declared types it was met
    /// inside, on which its answer depends.
    none: HashSet<(Ty, Vec<Item>)>,
}

impl Walk<'_> {
    fn holds(&mut self, ty: &Ty, inside: &mut Vec<Item>) -> bool {
        if (self.p)(ty) {
            return true;
        }
        let key = (ty.clone(), inside.clone());
        if self.none.contains(&key) {
            return false;
        }
        let found = match ty {
            Ty::Con(item, args) if inside.contains(item) => self.any(args, inside),
            Ty::Con(item, args) => {
                inside.push(item.clone());
                let found = self.any(&declared(self.decls, item, args), inside);
                inside.pop();
                found
            }
            Ty::Tuple(ts) => self.any(ts, inside),
            Ty::App(head, ts) => self.holds(head, inside) || self.any(ts, inside),
            Ty::Spread(s) => self.holds(&s.elem, inside),
            Ty::Fn(f) => {
                f.params.iter().any(|(_, t)| self.holds(t, inside)) || self.holds(&f.ret, inside)
            }
            Ty::Param(_) | Ty::SelfTy | Ty::Handler(_) | Ty::Var(_) | Ty::Value(_) | Ty::Error => {
                false
            }
        };
        if !found {
            self.none.insert(key);
        }
        found
    }

    fn any(&mut self, types: &[Ty], inside: &mut Vec<Item>) -> bool {
        types.iter().any(|t| self.holds(t, inside))
    }
}
