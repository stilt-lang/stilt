//! The sets of difference facts themselves (facts.difference-facts, facts.joins, facts.widening
//! and facts.large-bodies): closure, non-zero terms, contradictions, the bounds of a large body,
//! joins, widenings and the terms a set keeps.

use super::super::dbm::{Facts, INF, Key, ZERO, plus};

const A: u32 = 1;
const B: u32 = 2;
const C: u32 = 3;

/// A set over zero, `A`, `B` and `C`, with no facts.
fn set(capped: bool) -> Facts {
    Facts::over(vec![ZERO, A, B, C], capped)
}

#[test]
fn sums_of_facts_stay_exact_and_none_absorbs() {
    assert_eq!(plus(2, -5), -3);
    assert_eq!(plus(INF, -5), INF);
    assert_eq!(plus(-5, INF), INF);
    assert_eq!(plus(INF - 1, 1), INF - 1, "a finite sum never becomes none");
}

#[test]
fn a_set_is_closed_by_every_path() {
    let mut f = set(false);
    f.assume(A, B, 1);
    f.assume(B, C, 2);
    assert!(f.gives(A, C, 3));
    assert!(!f.gives(A, C, 2));
    // Of two facts on one pair, the smaller holds.
    f.assume(A, C, 0);
    assert!(f.gives(A, C, 0));
    f.assume(A, C, 7);
    assert!(!f.gives(A, C, -1));
    assert_eq!(f.get(A, C), 0);
    assert!(!f.gives(C, A, 100), "no fact bounds the other way");
}

#[test]
fn bounds_come_from_the_facts_against_zero() {
    let mut f = set(false);
    assert_eq!(f.bounds(A), (None, None));
    f.assume(A, ZERO, 5);
    assert_eq!(f.bounds(A), (None, Some(5)));
    f.assume(ZERO, A, 2);
    assert_eq!(f.bounds(A), (Some(-2), Some(5)));
    // B within 1 of A has bounds from A's.
    f.assume(B, A, 1);
    f.assume(A, B, 1);
    assert_eq!(f.bounds(B), (Some(-3), Some(6)));
}

#[test]
fn a_contradiction_is_never_reached_and_gives_every_fact() {
    let mut f = set(false);
    f.assume(A, B, -1);
    assert!(!f.is_bottom());
    f.assume(B, A, 0);
    assert!(f.is_bottom());
    assert!(f.gives(C, A, -100));
    assert!(f.is_nonzero(C));
    let mut g = set(false);
    g.assume(A, A, -1);
    assert!(g.is_bottom(), "t − t ≤ c with c < 0");
    let mut h = set(false);
    h.assume(A, A, 0);
    assert!(!h.is_bottom());
    assert!(h.gives(A, A, 0));
    assert!(!h.gives(A, A, -1));
}

#[test]
fn a_fact_on_a_term_the_set_lacks_changes_nothing() {
    let mut f = set(false);
    f.assume(A, 9, -5);
    assert_eq!(f, set(false));
    assert!(!f.has(9));
    assert!(f.has(C));
    f.mark_nonzero(9);
    assert!(!f.is_nonzero(9));
}

#[test]
fn a_nonzero_term_steps_past_zero_until_nothing_changes() {
    let mut f = set(false);
    f.mark_nonzero(A);
    f.assume(ZERO, B, 0);
    f.mark_nonzero(B);
    assert_eq!(f.bounds(B), (Some(1), None), "bounded below by 0, so by 1");
    let mut g = set(false);
    g.mark_nonzero(C);
    g.assume(C, ZERO, 0);
    assert_eq!(
        g.bounds(C),
        (None, Some(-1)),
        "bounded above by 0, so by −1"
    );
    // A ≥ B − 1 and B ≥ 0 give A ≥ 0 only once B ≥ 1, so the closure repeats: A, the smaller
    // term, is met first.
    let mut h = set(false);
    h.mark_nonzero(A);
    h.mark_nonzero(B);
    h.assume(B, A, 1);
    h.assume(ZERO, B, 0);
    assert_eq!(h.bounds(B), (Some(1), None));
    assert_eq!(h.bounds(A), (Some(1), None));
}

#[test]
fn a_large_body_keeps_only_bounds() {
    // Each time facts are added, the set is closed, then the facts between two terms neither
    // of which is zero are dropped: A − B ≤ 0 gives A its bound from B's, then goes, so a later
    // bound of B gives A nothing.
    let mut f = set(true);
    f.assume(B, ZERO, 4);
    f.assume(A, B, 0);
    assert!(!f.gives(A, B, 0), "the fact between two terms is dropped");
    assert!(f.gives(A, ZERO, 4), "the bound it gave is kept");
    f.assume(B, ZERO, 1);
    assert!(!f.gives(A, ZERO, 1));
    assert!(f.gives(B, ZERO, 4));
    assert!(f.gives(A, A, 0));
    let mut g = set(false);
    g.assume(A, B, 0);
    assert!(g.gives(A, B, 0));
}

#[test]
fn a_join_keeps_what_every_path_keeps() {
    let mut p = set(false);
    p.assume(A, ZERO, 3);
    p.assume(ZERO, A, 0);
    p.mark_nonzero(B);
    p.mark_nonzero(C);
    p.assume(C, ZERO, 2);
    let mut q = set(false);
    q.assume(A, ZERO, 5);
    q.mark_nonzero(B);
    q.assume(C, ZERO, 1);
    let same: &dyn Fn(u32) -> u32 = &|t| t;
    let joined = Facts::merge(vec![ZERO, A, B, C], &[(&p, same), (&q, same)]);
    assert_eq!(
        joined.bounds(A),
        (None, Some(5)),
        "the greatest c of the paths'"
    );
    assert_eq!(joined.bounds(C), (None, Some(2)));
    assert!(joined.is_nonzero(B));
    assert!(!joined.is_nonzero(C), "only one path's");
    // A path's own term is read as the new one.
    let renamed: &dyn Fn(u32) -> u32 = &|t| if t == C { A } else { t };
    let joined = Facts::merge(vec![ZERO, C], &[(&p, renamed), (&q, renamed)]);
    assert_eq!(joined.bounds(C), (None, Some(5)));
}

#[test]
fn a_widened_pair_goes_to_the_least_threshold_at_least_as_large() {
    let mut last = set(false);
    last.assume(A, ZERO, 1);
    last.assume(B, ZERO, 1);
    last.assume(C, ZERO, 1);
    last.mark_nonzero(A);
    last.mark_nonzero(B);
    last.present.insert((A, Key::Text("1".to_owned())));
    last.present.insert((B, Key::Text("2".to_owned())));
    let mut joined = set(false);
    joined.assume(A, ZERO, 1);
    joined.assume(B, ZERO, 7);
    joined.assume(C, ZERO, 20);
    joined.mark_nonzero(A);
    joined.present.insert((A, Key::Text("1".to_owned())));
    let w = last.widen(&joined, &[0, 7, 10]);
    assert_eq!(w.get(A, ZERO), 1, "a pair that didn't grow");
    assert_eq!(w.get(B, ZERO), 7, "a threshold equal to the join's");
    assert_eq!(w.get(C, ZERO), INF, "no threshold is as large");
    assert!(w.is_nonzero(A));
    assert!(!w.is_nonzero(B));
    assert_eq!(w.present.len(), 1);
    assert!(w.same(&w.clone()));
    assert!(!w.same(&last));
    let mut other = w.clone();
    other.mark_nonzero(C);
    assert!(!w.same(&other), "the non-zero terms differ");
    let mut keys = w.clone();
    keys.present.clear();
    assert!(!w.same(&keys), "the present keys differ");
}

#[test]
fn a_widened_set_is_closed_again() {
    // The last set had A − C ≤ −5, tighter than its path through B; the join's A − C ≤ 0 grows
    // it, and with no threshold it is dropped, while A − B and B − C stay: closing gives it back.
    let mut last = set(false);
    last.assume(A, B, 0);
    last.assume(B, C, 0);
    last.assume(A, C, -5);
    let mut joined = set(false);
    joined.assume(A, B, 0);
    joined.assume(B, C, 0);
    let mut w = last.widen(&joined, &[]);
    assert!(!w.gives(A, C, 0));
    w.close();
    assert!(w.gives(A, C, 0));
    assert!(!w.gives(A, C, -1));
}

#[test]
fn closing_applies_the_nonzero_terms() {
    // A ≥ 2, then A ≥ 1, widened to the threshold 0: A ≥ 0, and A is non-zero on both.
    let mut last = set(false);
    last.mark_nonzero(A);
    last.assume(ZERO, A, -2);
    let mut joined = set(false);
    joined.mark_nonzero(A);
    joined.assume(ZERO, A, -1);
    let mut w = last.widen(&joined, &[0]);
    assert_eq!(w.bounds(A), (Some(0), None));
    w.close();
    assert_eq!(w.bounds(A), (Some(1), None));
}

#[test]
fn a_set_keeps_zero_and_the_terms_it_is_told_to() {
    let mut f = set(false);
    f.assume(A, B, 1);
    f.assume(B, C, 2);
    f.mark_nonzero(B);
    f.mark_nonzero(C);
    f.keep(&|t| t != B);
    assert!(f.has(ZERO));
    assert!(f.has(A));
    assert!(!f.has(B));
    assert!(f.gives(A, C, 3), "the fact through B is already there");
    assert!(!f.gives(A, C, 2));
    assert!(f.is_nonzero(C));
    assert!(!f.is_nonzero(B));
    assert_eq!(f.terms(), [ZERO, A, C]);
    let mut all = set(false);
    all.assume(A, B, 1);
    let before = all.clone();
    all.keep(&|_| true);
    assert_eq!(all, before);
}
