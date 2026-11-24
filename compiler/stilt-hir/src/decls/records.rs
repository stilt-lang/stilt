//! What an anonymous record type declares, which no module writes (records.anonymous-types): a
//! record of its fields, in alphabetical order, each of the type parameter at its place, which its
//! arguments give. Each is made once, the first time it is looked up, and kept for the life of the
//! process, as a declaration of the standard library is.

use std::collections::HashMap;
use std::sync::{LazyLock, Mutex};

use super::{FnSig, TypeDefInfo, TypeInfo};
use crate::hir::{DeclId, GenericId, Item, Name, Owner, RECORD_HOME, Ty};

static MADE: LazyLock<Mutex<HashMap<Name, &'static TypeInfo>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

/// The owner of the type parameters of every anonymous record type.
#[must_use]
pub fn record_owner() -> Owner {
    Owner {
        decl: DeclId {
            module: Name::from(RECORD_HOME),
            index: 0,
        },
        member: None,
    }
}

/// What the anonymous record type `item` declares, if it is one.
pub(super) fn record_info(item: &Item) -> Option<&'static TypeInfo> {
    if !item.is_record() {
        return None;
    }
    let mut made = MADE
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if let Some(&info) = made.get(&item.name) {
        return Some(info);
    }
    let names = item.record_fields();
    let params: Vec<GenericId> = (0..)
        .zip(&names)
        .map(|(index, _)| GenericId {
            owner: record_owner(),
            index,
        })
        .collect();
    let fields = names
        .into_iter()
        .zip(&params)
        .map(|(n, p)| (n, Ty::Param(p.clone())))
        .collect();
    let info: &'static TypeInfo = Box::leak(Box::new(TypeInfo {
        params,
        values: Vec::new(),
        def: TypeDefInfo::Record(fields),
        is_pub: true,
        pack: false,
    }));
    made.insert(item.name, info);
    Some(info)
}

impl FnSig {
    /// The packs among its type parameters: those its parameters' types and its result spread
    /// (variadics.packs), in order and each once.
    #[must_use]
    pub fn packs(&self) -> Vec<GenericId> {
        fn of_ty(acc: &mut Vec<GenericId>, t: &Ty) {
            match t {
                Ty::Spread(p, t) => {
                    if !acc.contains(p) {
                        acc.push(p.clone());
                    }
                    of_ty(acc, t);
                }
                Ty::Fn(f) => {
                    f.params.iter().for_each(|(_, t)| of_ty(acc, t));
                    f.ret.iter().for_each(|t| of_ty(acc, t));
                }
                Ty::Handler(h) => {
                    h.effect.args.iter().for_each(|t| of_ty(acc, t));
                    h.answer.iter().for_each(|t| of_ty(acc, t));
                }
                Ty::Con(_, ts) | Ty::Tuple(ts) | Ty::App(_, ts) => {
                    for t in ts {
                        of_ty(acc, t);
                    }
                }
                Ty::Param(_) | Ty::SelfTy | Ty::Value(_) | Ty::Error => {}
            }
        }
        let mut acc = Vec::new();
        for (_, t) in &self.params {
            of_ty(&mut acc, t);
        }
        of_ty(&mut acc, &self.ret);
        acc
    }
}
