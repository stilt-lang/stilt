//! The renames of a package's edition, which a method call on a type of `std` follows: `std`
//! declares each method by its name in the first edition, and a package of a later edition
//! writes the name its edition gives it (editions.renames).

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_hir::hir::{Ident, Name};
use stilt_pkg::edition::{Named, resolve};

use super::State;
use crate::ty::Ty;

impl State<'_> {
    /// The method's name as `std` declares it, for a call of `name` on a receiver of type `ty`.
    /// A name that the package's edition took away is E0314, whose fix writes its new name.
    pub(super) fn edition_name(&mut self, ty: &Ty, name: &Ident) -> Ident {
        if self.env.renames.is_empty() {
            return name.clone();
        }
        let Ty::Con(item, _) = self.table.shape(ty) else {
            return name.clone();
        };
        if !item.home.starts_with("std") {
            return name.clone();
        }
        let declared = match resolve(self.env.renames, &item.name, &name.name) {
            Named::Declared(declared) => Name::from(declared),
            Named::Renamed {
                declared,
                newest,
                edition,
            } => {
                let message = format!(
                    "the edition {edition} renames `{}` to `{newest}`",
                    name.name
                );
                let fix = Fix::new(
                    format!("write `{newest}`"),
                    vec![Edit::replace(name.at, newest)],
                );
                let d = Diagnostic::new(codes::E0314, name.at, message).with_fix(fix);
                self.errors.push(d);
                self.renamed.push((name.at, newest));
                Name::from(declared)
            }
        };
        Ident {
            name: declared,
            at: name.at,
        }
    }
}
