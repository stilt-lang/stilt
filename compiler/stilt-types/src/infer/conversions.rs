//! The fix of a mismatch between two numeric types (numbers.no-implicit-conversions): the
//! conversion `.to_T()` of one value, where it gives a `T` and not an `Option`
//! (numbers.conversions).

use stilt_diag::{Edit, Fix, codes};
use stilt_hir::hir::{self, ExprKind};
use stilt_syntax::TextRange;

use super::State;
use crate::ty::Ty;

impl State<'_> {
    /// Gives the E0311 last reported, if it is at `at` and has no fix, the fix that converts
    /// `e` from `from` to `to`, when that conversion gives a `to`. A mismatch of an operator's
    /// right operand converts the left one when the right one has no such conversion.
    pub(super) fn offer_conversion(
        &mut self,
        at: TextRange,
        e: &hir::Expr,
        (from, to): (&Ty, &Ty),
    ) {
        let Some(fix) = self.conversion(e, from, to) else {
            return;
        };
        if let Some(d) = self.errors.last_mut()
            && d.code == codes::E0311
            && d.range == at
            && d.fixes.is_empty()
        {
            d.fixes.push(fix);
        }
    }

    fn conversion(&self, e: &hir::Expr, from: &Ty, to: &Ty) -> Option<Fix> {
        let (from, to) = (self.table.shape(from), self.table.shape(to));
        let (from, to) = (from.numeric_name()?, to.numeric_name()?);
        if from == to || !total(from, to) {
            return None;
        }
        let call = format!(".to_{to}()");
        let edits = if postfix(e) {
            vec![Edit::insert(e.at.end(), call.clone())]
        } else {
            vec![
                Edit::insert(e.at.start(), "("),
                Edit::insert(e.at.end(), format!("){call}")),
            ]
        };
        Some(Fix::new(format!("convert it with `{call}`"), edits))
    }
}

/// Whether the conversion from the numeric type `from` to `to` gives a `to`, not an `Option`
/// (numbers.conversions): an integer into an integer type that holds every value of its own,
/// an integer into a float, and a float into a float.
fn total(from: &str, to: &str) -> bool {
    let float = |t: &str| t.starts_with('f');
    let bits = |t: &str| t[1..].parse::<u32>().ok();
    if float(to) {
        return true;
    }
    if float(from) {
        return false;
    }
    let (Some(m), Some(n)) = (bits(from), bits(to)) else {
        return false;
    };
    match (from.starts_with('u'), to.starts_with('u')) {
        (false, false) | (true, true) => n >= m,
        (true, false) => n > m,
        (false, true) => false,
    }
}

/// Whether a method call can follow `e` as it is written, without parentheses around it.
fn postfix(e: &hir::Expr) -> bool {
    matches!(
        e.kind,
        ExprKind::Local(_)
            | ExprKind::Const(_)
            | ExprKind::ValueParam(..)
            | ExprKind::Field(..)
            | ExprKind::Call(..)
            | ExprKind::Index(..)
    )
}

#[cfg(test)]
mod tests {
    use super::total;

    #[test]
    fn a_conversion_is_total_when_every_value_has_an_image() {
        assert!(total("i32", "i64"));
        assert!(total("u8", "i16"));
        assert!(total("i64", "f64"));
        assert!(total("f64", "f32"));
        assert!(!total("i64", "i32"));
        assert!(!total("u64", "i64"));
        assert!(!total("i8", "u64"));
        assert!(!total("f64", "i64"));
    }
}
