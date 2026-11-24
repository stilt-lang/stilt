//! Indexes of lists and arrays (facts.range-loops and facts.guards): the range loop around an
//! index, and the guards before it, and what the closest of the two needs when neither proves it
//! (facts.closest-rule).

use stilt_hir::hir::{BinaryOp, LocalId};
use stilt_syntax::TextSize;

use super::code::{Atom, Cmp, Place, Term, is_sequence};
use super::signs::Signs;
use super::walked::{Op, Pending, Range, Walked, Write};
use super::{Context, Need, Rule, Verdict};
use crate::tast::{Expr, ExprKind};
use crate::ty::Ty;
use crate::verify::Check;

/// What the rules read once the walk is done.
pub(super) struct Rules<'r, 'a> {
    pub(super) cx: &'r Context<'r>,
    pub(super) walked: &'r Walked<'a>,
    pub(super) signs: &'r Signs<'r, 'a>,
}

impl Rules<'_, '_> {
    /// The verdict of each index, division and key.
    pub(super) fn checks(&self) -> Vec<(stilt_syntax::TextRange, Check, Verdict)> {
        let mut out = Vec::new();
        for p in &self.walked.pending {
            let (Some(check), verdict) = (p.check, self.verdict(p)) else {
                continue;
            };
            if let Some(v) = verdict {
                out.push((p.at, check, v));
            }
        }
        out
    }

    fn verdict(&self, p: &Pending<'_>) -> Option<Verdict> {
        Some(match p.op {
            Op::Index(base, key) if p.check == Some(Check::MissingKey) => {
                done(Rule::Key, self.key(p, base, key))
            }
            Op::Index(base, key) => self.index(p, base, key),
            Op::Division(d) => done(Rule::Divisor, self.divisor(p, d)),
            Op::SelfCall(_) => return None,
        })
    }

    /// An index of a list or an array: by a range loop or a guard, or what the closest needs.
    fn index(&self, p: &Pending<'_>, base: &Expr, key: &Expr) -> Verdict {
        if self.below_size(base, key) {
            return Verdict::Proved(Rule::RangeLoop);
        }
        let ranges = || p.ranges.iter().rev().map(|&r| &self.walked.ranges[r]);
        if ranges().any(|r| self.range(p, r, base, key).is_ok()) {
            return Verdict::Proved(Rule::RangeLoop);
        }
        let guard = self.guard(p, base, key);
        let Err(need) = guard else {
            return Verdict::Proved(Rule::Guard);
        };
        match ranges().find(|r| names(key, r.var)) {
            Some(r) => Verdict::Lacks(self.range(p, r, base, key).err().unwrap_or(need)),
            None => Verdict::Lacks(need),
        }
    }

    /// An array's element at a literal or a constant at least 0 and below its size
    /// (facts.range-loops).
    fn below_size(&self, base: &Expr, key: &Expr) -> bool {
        let reader = self.signs.reader();
        match (size(&base.ty), reader.number(key)) {
            (Some(Size::Number(n)), Some(k)) => 0 <= k && k < n,
            _ => false,
        }
    }

    /// facts.range-loops: whether the range loop `r` proves `base[key]`, or what it needs.
    fn range(&self, p: &Pending<'_>, r: &Range<'_>, base: &Expr, key: &Expr) -> Result<(), Need> {
        let reader = self.signs.reader();
        if r.body != p.body {
            return Err(Need::OutsideClosures);
        }
        let Some((k, plus)) = self.offset(key, r.var) else {
            return Err(Need::IndexForm(r.var));
        };
        let kn = k.map_or(0, |k| reader.number(k).unwrap_or(0));
        if plus && !self.signs.nonneg(r.start, r.body) {
            return Err(Need::StartNonNegative);
        }
        // For `i - k`, the start is a number at least `k`.
        if !(plus || reader.number(r.start).is_some_and(|a| a >= kn)) {
            return Err(Need::StartAtLeast(k.map_or(key.at, |k| k.at)));
        }
        let place = reader.place(base).filter(|_| is_sequence(&base.ty));
        let ends = place
            .as_ref()
            .is_some_and(|pl| self.ends(r, pl, base, plus.then_some(kn)));
        if r.inclusive || !ends {
            let shown = k.filter(|_| plus && kn > 0).map(|k| k.at);
            return Err(Need::EndAt(base.at, shown, r.end.at, r.inclusive));
        }
        // An array's length never changes (facts.rules-of-acceptance).
        let list = place.filter(|_| base.ty.is_prelude("List"));
        let changed =
            list.and_then(|pl| first(self.walked.in_span(r.body, r.span), &|w| w.changes(&pl)));
        match changed {
            Some(at) => Err(Need::KeepsLength(base.at, at)),
            None => Ok(()),
        }
    }

    /// The `k` of an index `i`, `i + k` or `i - k` of the variable `var`, none for `i`, and
    /// whether it adds.
    fn offset<'e>(&self, key: &'e Expr, var: LocalId) -> Option<(Option<&'e Expr>, bool)> {
        let reader = self.signs.reader();
        let is_var = |e: &Expr| matches!(e.kind, ExprKind::Local(v) if v == var);
        match &key.kind {
            _ if is_var(key) => Some((None, true)),
            ExprKind::Binary(op @ (BinaryOp::Add | BinaryOp::Sub), a, k)
                if is_var(a) && reader.number(k).is_some_and(|n| n >= 0) =>
            {
                Some((Some(&**k), *op == BinaryOp::Add))
            }
            _ => None,
        }
    }

    /// Whether the range loop ends at `P.len()`, where the index adds nothing, or at
    /// `P.len() - c` with `c` at least `k` where it adds `k`, `n` standing for `P.len()` for an
    /// array of size `n`.
    fn ends(&self, r: &Range<'_>, place: &Place, base: &Expr, k: Option<i128>) -> bool {
        let reader = self.signs.reader();
        let is_len =
            |e: &Expr| reader.len_of(e).as_ref() == Some(place) || self.is_size(e, &base.ty);
        match &r.end.kind {
            _ if is_len(r.end) => k.is_none_or(|k| k == 0),
            ExprKind::Binary(BinaryOp::Sub, len, c) => {
                is_len(len) && k.is_some_and(|k| reader.number(c).is_some_and(|c| c >= k))
            }
            _ => false,
        }
    }

    /// Whether an expression is the size `n` of the array type `ty`.
    fn is_size(&self, e: &Expr, ty: &Ty) -> bool {
        match (size(ty), &e.kind) {
            (Some(Size::Param(id)), ExprKind::ValueParam(v)) => *v == id,
            (Some(Size::Number(n)), _) => self.signs.reader().number(e) == Some(n),
            _ => false,
        }
    }

    /// facts.guards: whether guards prove `base[key]`, or what they need.
    fn guard(&self, p: &Pending<'_>, base: &Expr, key: &Expr) -> Result<(), Need> {
        let reader = self.signs.reader();
        let term = match (reader.name(key), reader.number(key)) {
            (Some(v), _) => Term::Name(v),
            (None, Some(n)) if n >= 0 => Term::Num(n),
            _ => return Err(Need::GuardForm),
        };
        let lower = if self.signs.nonneg(key, p.body) {
            None
        } else {
            let zero = Term::Num(0);
            let f = self.walked.frame(p, &|a| a.compares(&term, Cmp::Ge, &zero));
            Some(f.ok_or(Need::LowerTest(key.at))?)
        };
        let place = reader.place(base).filter(|_| is_sequence(&base.ty));
        let upper = place.as_ref().and_then(|pl| {
            let len = Term::Len(pl.clone());
            self.walked.frame(p, &|a| {
                a.compares(&term, Cmp::Lt, &len)
                    || (term == Term::Num(0) && *a == Atom::NonEmpty(pl.clone()))
            })
        });
        let (Some(upper), Some(place)) = (upper, place) else {
            return Err(Need::UpperTest(key.at, base.at));
        };
        let frames: Vec<usize> = lower.into_iter().chain([upper]).collect();
        let between = |f: &dyn Fn(&Write<'_>) -> bool| {
            frames
                .iter()
                .filter_map(|&fr| first(self.walked.between(fr, p).into_iter(), f))
                .min()
        };
        if let Term::Name(v) = term
            && let Some(at) = between(&|w| w.root == v)
        {
            return Err(Need::GuardWrites(key.at, at));
        }
        let list = base.ty.is_prelude("List");
        match between(&|w| list && w.changes(&place)) {
            Some(at) => Err(Need::GuardLength(base.at, at)),
            None => Ok(()),
        }
    }
}

/// A proof by `rule`, or what it needs.
fn done(rule: Rule, found: Result<(), Need>) -> Verdict {
    match found {
        Ok(()) => Verdict::Proved(rule),
        Err(need) => Verdict::Lacks(need),
    }
}

/// Where the first of the writes that `f` accepts is.
pub(super) fn first<'w, 'a: 'w>(
    writes: impl Iterator<Item = &'w Write<'a>>,
    f: &dyn Fn(&Write<'_>) -> bool,
) -> Option<TextSize> {
    writes.filter(|w| f(w)).map(|w| w.at).min()
}

/// Whether an expression names the binding `v`.
fn names(e: &Expr, v: LocalId) -> bool {
    crate::tast::walk::exists(e, &|x| matches!(x.kind, ExprKind::Local(w) if w == v))
}

/// An array's size.
enum Size {
    Number(i128),
    Param(stilt_hir::hir::GenericId),
}

fn size(ty: &Ty) -> Option<Size> {
    match ty.arrayed()?.1 {
        Ty::Value(stilt_hir::hir::Value::Int(n)) => Some(Size::Number(*n)),
        Ty::Param(id) => Some(Size::Param(id.clone())),
        _ => None,
    }
}
