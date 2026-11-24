//! Quotes and their splices (macros.quote and macros.splices): a quote has the type of its form's
//! code, and each splice's value is inferred where it is written, then checked, once the body's
//! types are known, against what may stand where it does: E0311 at the splice otherwise.

use stilt_diag::codes;
use stilt_hir::hir::{self, Item, Name, Place};
use stilt_syntax::TextRange;

use super::{Cx, State, node};
use crate::tast;
use crate::ty::{FLOAT_TYPES, INTEGER_TYPES, Ty};

/// The type `name` of `std.meta`.
pub(crate) fn meta_ty(name: &str) -> Ty {
    Ty::Con(
        Item {
            home: Name::from("std.meta"),
            name: Name::from(name),
        },
        Vec::new(),
    )
}

impl State<'_> {
    /// A quote, whose module is in the meta tier (macros.meta-tier).
    pub(super) fn quote_expr(&mut self, cx: &mut Cx, at: TextRange, q: &hir::Quote) -> tast::Expr {
        let splices = q
            .splices
            .iter()
            .map(|s| {
                let value = self.infer(cx, None, &s.value);
                self.splices.push((value.ty.clone(), s.place, s.at));
                tast::Splice {
                    place: s.place,
                    spread: s.spread,
                    at: s.at,
                    value,
                }
            })
            .collect();
        let quote = tast::Quote {
            home: q.home,
            form: q.form,
            tokens: q.tokens.clone(),
            splices,
            written: q.written.clone(),
        };
        node(
            tast::ExprKind::Quote(Box::new(quote)),
            meta_ty(q.form.type_name()),
            at,
        )
    }

    /// E0311 at each splice whose value can't stand where it does (macros.splices).
    pub(super) fn fit_splices(&mut self) {
        for (ty, place, at) in std::mem::take(&mut self.splices) {
            if !self.splice_fits(place, &ty) {
                let shown = self.show(&ty);
                let message = format!("a value of type `{shown}` can't be spliced here");
                self.error(codes::E0311, at, message);
            }
        }
    }

    /// Whether a value of type `ty` may stand at `place`: a type still open, or with an error,
    /// does, which inference or another diagnostic decides.
    fn splice_fits(&self, place: Place, ty: &Ty) -> bool {
        let unknown = |t: &Ty| self.table.unsolved(t).is_some() || self.table.mentions_error(t);
        if unknown(ty) {
            return true;
        }
        let ty = self.table.resolve(ty);
        match (place, ty) {
            (Place::Elements, Ty::Con(item, args)) if is_list(item) && args.len() == 1 => {
                unknown(&args[0]) || one(Place::Expr, self.table.resolve(&args[0]))
            }
            (Place::Fields, Ty::Con(item, args)) if is_list(item) && args.len() == 1 => {
                unknown(&args[0]) || *self.table.resolve(&args[0]) == meta_ty("FieldInit")
            }
            _ => one(place, ty),
        }
    }
}

fn is_list(item: &Item) -> bool {
    &*item.home == "std.prelude" && &*item.name == "List"
}

/// What a value of a type writes where a splice stands: code, a name, or a literal, a float
/// only as an expression.
fn one(place: Place, ty: &Ty) -> bool {
    let meta = |name: &str| *ty == meta_ty(name);
    let literal = |float: bool| match ty {
        Ty::Con(item, args) if args.is_empty() && &*item.home == "std.prelude" => {
            let n = &*item.name;
            n == "str"
                || n == "bool"
                || INTEGER_TYPES.contains(&n)
                || (float && FLOAT_TYPES.contains(&n))
        }
        _ => false,
    };
    match place {
        Place::Expr => meta("Expr") || meta("Name") || literal(true),
        Place::Pattern => meta("Pattern") || meta("Name") || literal(false),
        Place::Type => meta("Type"),
        Place::Name => meta("Name"),
        Place::Elements | Place::Fields => false,
    }
}
