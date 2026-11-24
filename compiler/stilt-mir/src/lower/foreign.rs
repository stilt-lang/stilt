//! Calls of foreign functions, which C gives (c.calls): a call of one calls the
//! function its name gives, with its C types, which the back ends pass and take as C does, and
//! a use of one as a value makes code that calls it so.

use stilt_hir::decls::Lookup;
use stilt_hir::hir::{Item, Ty};

use super::Lower;
use crate::CType;
use crate::items::Foreign;

/// The C type of a foreign function's parameter or result of type `t`: a number or `bool` as
/// itself, and a `c.Ptr` or a `c.Str` as an address. A program whose foreign function has
/// another type has an error, and never runs.
fn c_type(t: &Ty) -> Option<CType> {
    let Ty::Con(item, _) = t else { return None };
    match (&*item.home, &*item.name) {
        ("std.prelude", name) => CType::of(name),
        ("std.c", "Ptr" | "Str") => Some(CType::Ptr),
        _ => None,
    }
}

impl Lower<'_> {
    /// The foreign function `item`, if it is one.
    pub(crate) fn foreign(&self, item: &Item) -> Option<Foreign> {
        let decls = self.decls();
        let sig = decls.function(item).filter(|s| s.foreign)?;
        Some(Foreign {
            name: item.name.to_string(),
            params: sig.params.iter().filter_map(|(_, t)| c_type(t)).collect(),
            result: c_type(&sig.ret),
        })
    }
}
