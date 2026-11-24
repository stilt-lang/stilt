//! Divisions and keys (facts.divisors and facts.keys): a divisor that tests show non-zero, and a
//! key that a test or a store shows present, with nothing between that undoes it.

use super::Need;
use super::code::{Atom, Cmp, Term};
use super::indexes::{Rules, first};
use super::walked::Pending;
use crate::tast::Expr;

impl Rules<'_, '_> {
    /// facts.divisors: whether the divisor `d` is proved non-zero, or what the divisor needs.
    pub(super) fn divisor(&self, p: &Pending<'_>, d: &Expr) -> Result<(), Need> {
        let reader = self.signs.reader();
        let Some(v) = reader.name(d) else {
            return match reader.number(d) {
                Some(n) if n != 0 => Ok(()),
                _ => Err(Need::DivisorForm),
            };
        };
        if self.signs.positive(d, p.body) {
            return Ok(());
        }
        let (name, zero) = (Term::Name(v), Term::Num(0));
        let nonzero = |a: &Atom| {
            [Cmp::Ne, Cmp::Gt, Cmp::Lt]
                .into_iter()
                .any(|op| a.compares(&name, op, &zero))
        };
        let frame = self
            .walked
            .frame(p, &nonzero)
            .ok_or(Need::DivisorTest(d.at))?;
        match first(self.walked.between(frame, p).into_iter(), &|w| w.root == v) {
            Some(at) => Err(Need::DivisorWrites(d.at, at)),
            None => Ok(()),
        }
    }

    /// facts.keys: whether the key `k` of the map `m` is proved present, or what the key needs.
    pub(super) fn key(&self, p: &Pending<'_>, m: &Expr, k: &Expr) -> Result<(), Need> {
        let reader = self.signs.reader();
        let key = reader.key(k).ok_or(Need::KeyForm)?;
        if !super::super::verify::keyable(self.cx.decls, &k.ty) {
            return Err(Need::KeyType);
        }
        let test = Need::KeyTest(m.at, k.at);
        let place = reader.place(m).ok_or(test.clone())?;
        let frame = self
            .walked
            .frame(p, &|a| *a == Atom::Contains(place.clone(), key.clone()))
            .ok_or(test)?;
        let between = self.walked.between(frame, p);
        if let super::code::KeyTerm::Name(v) = key
            && let Some(at) = first(between.iter().copied(), &|w| w.root == v)
        {
            return Err(Need::KeyWrites(k.at, at));
        }
        match first(between.into_iter(), &|w| w.unstores(&place)) {
            Some(at) => Err(Need::KeyChanges(m.at, at)),
            None => Ok(()),
        }
    }
}
