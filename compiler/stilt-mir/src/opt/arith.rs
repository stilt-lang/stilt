//! The facts of integer arithmetic: when an addition, a subtraction or a multiplication can't
//! overflow, and what the result of one that holds exactly is known to be. Besides the relations
//! between terms, each term may be known to lie between two constants ([`Facts::upper`] and
//! [`Facts::lower`]), from the branches that tested it, as a size that a program checks, and an
//! operation whose operands' bounds keep its result in `i64` can't overflow.

use crate::mir::{Const, Operand};
use crate::opt::facts::{Fact, Facts, Rel, Term};

/// The least and the largest values `t` is known to have.
fn range(facts: &Facts, t: Term) -> (Option<i128>, Option<i128>) {
    (
        facts.lower(t).map(i128::from),
        facts.upper(t).map(i128::from),
    )
}

/// Whether `n`, if known, is a value of `i64`.
fn in_i64(n: Option<i128>) -> bool {
    n.is_some_and(|n| i64::try_from(n).is_ok())
}

/// The least and the largest results of an operation on two ranges, through `f` on their ends,
/// when all four ends are known.
fn corners(
    (la, ua): (Option<i128>, Option<i128>),
    (lb, ub): (Option<i128>, Option<i128>),
    f: impl Fn(i128, i128) -> i128,
) -> Option<(i128, i128)> {
    let (la, ua, lb, ub) = (la?, ua?, lb?, ub?);
    let ends = [f(la, lb), f(la, ub), f(ua, lb), f(ua, ub)];
    Some((*ends.iter().min()?, *ends.iter().max()?))
}

/// Whether `a + b` can't overflow: adding 1 to a term below another, which is at most the
/// maximum, adding 0, adding a negative constant to a term at least 0, and adding two terms whose
/// bounds keep their sum in `i64`.
pub(crate) fn add_fits(facts: &Facts, a: Term, b: Term) -> bool {
    let one_side = |x: Term, c: Term| match c {
        Term::Const(1) => facts.below_another(x),
        Term::Const(c) => c == 0 || (c < 0 && facts.nonneg(x)),
        Term::Local(_) => false,
    };
    one_side(a, b) || one_side(b, a) || bounded(facts, a, b, |x, y| x + y)
}

/// Whether `a - b` can't overflow: both at least 0, so that the result lies between minus the
/// maximum and the maximum, or both bounded so that it lies in `i64`.
pub(crate) fn sub_fits(facts: &Facts, a: Term, b: Term) -> bool {
    (facts.nonneg(a) && facts.nonneg(b)) || bounded(facts, a, b, |x, y| x - y)
}

/// Whether `a * b` can't overflow: both bounded so that the product lies in `i64`.
pub(crate) fn mul_fits(facts: &Facts, a: Term, b: Term) -> bool {
    bounded(facts, a, b, |x, y| x * y)
}

/// Whether the bounds of `a` and `b` keep `f(a, b)` in `i64`, of operands not both known
/// exactly. An operation of two known values is folded by the back end, check included, and a
/// debug build keeps its line only while its check is there, as a function inlined with constant
/// arguments does.
fn bounded(facts: &Facts, a: Term, b: Term, f: impl Fn(i128, i128) -> i128) -> bool {
    let (ra, rb) = (range(facts, a), range(facts, b));
    let exact = |(low, high): (Option<i128>, Option<i128>)| low.is_some() && low == high;
    !(exact(ra) && exact(rb))
        && corners(ra, rb, f).is_some_and(|(low, high)| in_i64(Some(low)) && in_i64(Some(high)))
}

/// The bounds of `result = f(lhs, rhs)`, which holds exactly, from those of its operands: as
/// facts of the result against constants.
pub(crate) fn bounds(
    facts: &Facts,
    (result, lhs, rhs): (Term, Term, Term),
    f: impl Fn(i128, i128) -> i128,
    out: &mut Vec<Fact>,
) {
    let (lower, upper) = (range(facts, lhs), range(facts, rhs));
    let Some((low, high)) = corners(lower, upper, f) else {
        return;
    };
    for (bound, below) in [(low, false), (high, true)] {
        if let Ok(c) = i64::try_from(bound) {
            let c = Term::Const(c);
            out.push(Fact::Rel(if below {
                Rel::Le(result, c)
            } else {
                Rel::Le(c, result)
            }));
        }
    }
}

/// The facts of `result = lhs + rhs`, which holds exactly, either because the addition is
/// checked and didn't panic or because it can't overflow: at least 0 of two terms at least 0,
/// and above 0 when one of them is.
pub(crate) fn sum(facts: &Facts, result: Term, lhs: Term, rhs: Term, out: &mut Vec<Fact>) {
    let zero = Term::Const(0);
    if facts.nonneg(lhs) && facts.nonneg(rhs) {
        out.push(Fact::Rel(Rel::Le(zero, result)));
        if facts.lt(zero, lhs) || facts.lt(zero, rhs) {
            out.push(Fact::Rel(Rel::Lt(zero, result)));
        }
    }
    for (term, other) in [(lhs, rhs), (rhs, lhs)] {
        if other == Term::Const(1) {
            out.extend(facts.iter().filter_map(|f| match f {
                Fact::Rel(Rel::Lt(low, high)) if low == term => {
                    Some(Fact::Rel(Rel::Le(result, high)))
                }
                _ => None,
            }));
        }
    }
}

/// The facts of `result = lhs - rhs`, which holds exactly: with `rhs` at least 0, the result
/// is at most `lhs`, and 1 less than a term above 0 is at least 0.
pub(crate) fn difference(facts: &Facts, result: Term, lhs: Term, rhs: Term, out: &mut Vec<Fact>) {
    if !facts.nonneg(rhs) {
        return;
    }
    if rhs == Term::Const(1) && facts.lt(Term::Const(0), lhs) {
        out.push(Fact::Rel(Rel::Le(Term::Const(0), result)));
    }
    out.extend(facts.iter().filter_map(|f| match f {
        Fact::Rel(Rel::Lt(low, high)) if low == lhs => Some(Fact::Rel(Rel::Lt(result, high))),
        Fact::Rel(Rel::Le(low, high)) if low == lhs => Some(Fact::Rel(Rel::Le(result, high))),
        _ => None,
    }));
}

/// Whether an element of the constant shape `elem` is read as a narrow scalar that its read
/// doesn't extend the sign of, a `bool`, a `u8` or a `u16`, which is at least 0.
pub(crate) fn zero_extended(elem: &Operand) -> bool {
    let Operand::Const(Const::Word(shape)) = *elem else {
        return false;
    };
    matches!(crate::shape::size(shape), 1 | 2) && !crate::shape::signed(shape)
}
