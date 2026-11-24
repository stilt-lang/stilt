//! Unsafe code and what C holds, while a body is checked (c.unsafe-operations, c.element-types and
//! c.lending-buffer): E0436 at an unsafe operation outside every `unsafe` block of the body, and
//! E0353 at a call that reads, writes or lends values of a type C doesn't hold as Stilt does,
//! decided once the body's types are known.

use stilt_diag::codes;
use stilt_hir::hir::Item;
use stilt_syntax::TextRange;

use super::State;
use crate::tast::Callee;
use crate::ty::Ty;

/// Whether `item` is the type `name` of `std.c`.
fn is_c(item: &Item, name: &str) -> bool {
    &*item.home == "std.c" && &*item.name == name
}

/// The calls whose first type argument C must hold (c.element-types and c.lending-buffer): reading,
/// writing and moving through an address, and lending a list.
fn reads_c_memory(callee: &Callee) -> bool {
    match callee {
        Callee::Member(owner, name) if is_c(owner, "Ptr") => {
            matches!(&**name, "read" | "write" | "read_list" | "offset")
        }
        Callee::Member(owner, name) => {
            crate::ty::is_prelude(owner, "List") && matches!(&**name, "with_ptr" | "with_mut_ptr")
        }
        _ => false,
    }
}

impl State<'_> {
    /// Whether a use of `callee` is unsafe (c.unsafe-operations): a foreign function, the reads and
    /// writes of a `c.Ptr`, and `to_str` on a `c.Str`.
    fn is_unsafe(&self, callee: &Callee) -> bool {
        match callee {
            Callee::Function(item) => self.env.decls.function(item).is_some_and(|s| s.foreign),
            Callee::Member(owner, name) if is_c(owner, "Ptr") => {
                matches!(&**name, "read" | "write" | "read_list")
            }
            Callee::Member(owner, name) => is_c(owner, "Str") && &**name == "to_str",
            Callee::TraitMethod(..) | Callee::Operation(..) => false,
        }
    }

    /// A call of `callee`, or a use of it as a value, at `at`, with its type arguments: E0436
    /// when it is unsafe and no `unsafe` block of the body holds it, and the type that C must
    /// hold, which [`State::c_elements`] checks once the body's types are known.
    pub(super) fn c_use(&mut self, callee: &Callee, targs: &[Ty], at: TextRange) {
        if self.is_unsafe(callee) && !self.unsafe_blocks.iter().any(|b| b.contains_range(at)) {
            let message = "this is an unsafe operation, which only an `unsafe because \"…\" { … }` \
                           block may hold";
            self.error(codes::E0436, at, message.to_owned());
        }
        if let Some(t) = targs.first().filter(|_| reads_c_memory(callee)) {
            self.c_elements.push((t.clone(), at));
        }
    }

    /// Whether C holds a value of type `t` as Stilt does (c.element-types): a number, `bool`, or a
    /// `c.Ptr` to one of these or to `()`; `None` while it is unknown.
    fn c_holds(&self, t: &Ty) -> Option<bool> {
        match self.table.shape(t) {
            Ty::Var(_) | Ty::Error => None,
            Ty::Con(item, args) if is_c(&item, "Ptr") && args.len() == 1 => {
                if matches!(self.table.shape(&args[0]), Ty::Tuple(ts) if ts.is_empty()) {
                    return Some(true);
                }
                self.c_holds(&args[0])
            }
            t => Some(t.numeric_name().is_some() || t == Ty::bool()),
        }
    }

    /// c.element-types and c.lending-buffer: E0353 at each call whose type C must hold and doesn't.
    pub(super) fn c_elements(&mut self) {
        for (t, at) in std::mem::take(&mut self.c_elements) {
            if self.c_holds(&t) == Some(false) {
                let message = format!(
                    "C doesn't hold a `{}` as Stilt does: use an integer, a float, `bool` or a \
                     `c.Ptr`",
                    self.show(&t)
                );
                self.error(codes::E0353, at, message);
            }
        }
    }
}
