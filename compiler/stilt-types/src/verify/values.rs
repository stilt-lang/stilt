//! The values of integer expressions (facts.linear-forms and facts.intervals): a linear form, a
//! term plus a number, or a new term, and the interval of each, computed from its parts.

use super::dbm::Term;

/// The least and greatest values an expression may have, none where nothing bounds it.
pub(crate) type Interval = (Option<i128>, Option<i128>);

/// What evaluating an integer expression gives: its value, `term` plus `d`, which is a linear
/// form when `linear` holds and a new term otherwise, and its interval.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Value {
    pub(crate) term: Term,
    pub(crate) d: i128,
    pub(crate) linear: bool,
    pub(crate) lo: Option<i128>,
    pub(crate) hi: Option<i128>,
}

impl Value {
    pub(crate) fn interval(&self) -> Interval {
        (self.lo, self.hi)
    }

    /// The linear form, if the value is one.
    pub(crate) fn form(&self) -> Option<(Term, i128)> {
        self.linear.then_some((self.term, self.d))
    }
}

/// The bounds of the integer type named `name`.
pub(crate) fn type_bounds(name: &str) -> Option<(i128, i128)> {
    stilt_hir::values::int_range(name)
}

/// The width in bits of the integer type named `name`.
pub(crate) fn width(name: &str) -> Option<i128> {
    let digits: String = name.chars().filter(char::is_ascii_digit).collect();
    digits.parse().ok()
}

fn lift(a: Option<i128>, b: Option<i128>, f: impl Fn(i128, i128) -> i128) -> Option<i128> {
    Some(f(a?, b?))
}

/// `a + b`, exactly.
pub(crate) fn add(a: Interval, b: Interval) -> Interval {
    (
        lift(a.0, b.0, i128::saturating_add),
        lift(a.1, b.1, i128::saturating_add),
    )
}

/// `a - b`, exactly.
pub(crate) fn sub(a: Interval, b: Interval) -> Interval {
    (
        lift(a.0, b.1, i128::saturating_sub),
        lift(a.1, b.0, i128::saturating_sub),
    )
}

/// `a * b`, exactly: unbounded unless both are bounded.
pub(crate) fn mul(a: Interval, b: Interval) -> Interval {
    let (Some(al), Some(ah), Some(bl), Some(bh)) = (a.0, a.1, b.0, b.1) else {
        return (None, None);
    };
    let corners = [
        al.saturating_mul(bl),
        al.saturating_mul(bh),
        ah.saturating_mul(bl),
        ah.saturating_mul(bh),
    ];
    (corners.iter().min().copied(), corners.iter().max().copied())
}

/// `-a`, exactly.
pub(crate) fn neg(a: Interval) -> Interval {
    (a.1.map(i128::saturating_neg), a.0.map(i128::saturating_neg))
}

/// `a / b` for a divisor at least 1, truncating toward zero (numbers.division-and-remainder).
pub(crate) fn quotient(a: Interval, least: i128, most: Option<i128>) -> Interval {
    // A dividend over an unbounded divisor gives 0 at that end.
    let by_most = |x: Option<i128>| x.map(|x| most.map_or(0, |most| x / most));
    let by_least = |x: Option<i128>| x.map(|x| x / least);
    match a.0 {
        Some(al) if al >= 0 => (by_most(a.0), by_least(a.1)),
        _ => {
            let hi = match a.1 {
                Some(ah) if ah >= 0 => by_least(a.1),
                _ => by_most(a.1),
            };
            (by_least(a.0), hi)
        }
    }
}

/// `a % b` for a divisor at least 1: between `max(al, 1 − bh)` and `min(ah, bh − 1)`, the least
/// 0 when `al ≥ 0` and the greatest 0 when `ah ≤ 0`.
pub(crate) fn remainder(a: Interval, bh: Option<i128>) -> Interval {
    let lo = match a.0 {
        Some(al) if al >= 0 => Some(0),
        al => match (al, bh) {
            (Some(al), Some(bh)) => Some(al.max(1 - bh)),
            (None, Some(bh)) => Some(1 - bh),
            (al, None) => al,
        },
    };
    let hi = match a.1 {
        Some(ah) if ah <= 0 => Some(0),
        ah => match (ah, bh) {
            (Some(ah), Some(bh)) => Some(ah.min(bh - 1)),
            (None, Some(bh)) => Some(bh - 1),
            (ah, None) => ah,
        },
    };
    (lo, hi)
}

/// The interval cut to the bounds `(lo, hi)` of a type.
pub(crate) fn cut(a: Interval, (lo, hi): (i128, i128)) -> (i128, i128) {
    (
        a.0.map_or(lo, |x| x.clamp(lo, hi)),
        a.1.map_or(hi, |x| x.clamp(lo, hi)),
    )
}

/// Whether the interval lies within `(lo, hi)`.
pub(crate) fn within(a: Interval, (lo, hi): (i128, i128)) -> bool {
    a.0.is_some_and(|x| x >= lo) && a.1.is_some_and(|x| x <= hi)
}

/// Whether the interval leaves out `x`.
pub(crate) fn leaves_out(a: Interval, x: i128) -> bool {
    a.0.is_some_and(|l| l > x) || a.1.is_some_and(|h| h < x)
}
