import Stilt.Analysis.Frames

/-!
# Intervals and relative bounds

A term's interval, the least and greatest values its facts allow (facts.intervals), the exact
interval of a sum, a difference, a product and a negation, and the facts that relate the value
an expression gives to a term (facts.relative-bounds). A bound that the facts don't give is
left out, and an interval with no bound on a side has none on that side.
-/

namespace Stilt

/-- An interval: a least and a greatest value, each when one is known. -/
abbrev Interval := Option Int × Option Int

/-- An integer lies within an interval. -/
def Interval.Has (i : Interval) (x : Int) : Prop := (∀ l, i.1 = some l → l ≤ x) ∧ ∀ h, i.2 = some h → x ≤ h

/-- Both of two options, combined. -/
def Option.both {α : Type} (f : α → α → α) : Option α → Option α → Option α
  | some a, some b => some (f a b)
  | _, _ => none

namespace Interval

/-- The exact interval of a sum. -/
def add (a b : Interval) : Interval := (Option.both (· + ·) a.1 b.1, Option.both (· + ·) a.2 b.2)

/-- The exact interval of a difference. -/
def sub (a b : Interval) : Interval := (Option.both (· - ·) a.1 b.2, Option.both (· - ·) a.2 b.1)

/-- The exact interval of a negation. -/
def neg (a : Interval) : Interval := (a.2.map (- ·), a.1.map (- ·))

/-- The exact interval of a product: the least and greatest of the products of the bounds,
when all four are known. -/
def mul (a b : Interval) : Interval :=
  match a, b with
  | (some al, some ah), (some bl, some bh) =>
    let ps := [al * bh, ah * bl, ah * bh]
    (some (ps.foldl min (al * bl)), some (ps.foldl max (al * bl)))
  | _, _ => (none, none)

/-- Whether an interval lies within `lo` to `hi`. -/
def within (i : Interval) (lo hi : Int) : Bool :=
  (i.1.any fun l => decide (lo ≤ l)) && i.2.any fun h => decide (h ≤ hi)

variable {a b : Interval} {x y : Int}

theorem Has.add (ha : a.Has x) (hb : b.Has y) : (a.add b).Has (x + y) := by
  constructor
  · intro l hl
    simp only [Interval.add] at hl
    cases h1 : a.1 <;> cases h2 : b.1 <;> simp only [h1, h2, Option.both, reduceCtorEq,
      Option.some.injEq] at hl
    subst hl; have := ha.1 _ h1; have := hb.1 _ h2; omega
  · intro h hh
    simp only [Interval.add] at hh
    cases h1 : a.2 <;> cases h2 : b.2 <;> simp only [h1, h2, Option.both, reduceCtorEq,
      Option.some.injEq] at hh
    subst hh; have := ha.2 _ h1; have := hb.2 _ h2; omega

theorem Has.sub (ha : a.Has x) (hb : b.Has y) : (a.sub b).Has (x - y) := by
  constructor
  · intro l hl
    simp only [Interval.sub] at hl
    cases h1 : a.1 <;> cases h2 : b.2 <;> simp only [h1, h2, Option.both, reduceCtorEq,
      Option.some.injEq] at hl
    subst hl; have := ha.1 _ h1; have := hb.2 _ h2; omega
  · intro h hh
    simp only [Interval.sub] at hh
    cases h1 : a.2 <;> cases h2 : b.1 <;> simp only [h1, h2, Option.both, reduceCtorEq,
      Option.some.injEq] at hh
    subst hh; have := ha.2 _ h1; have := hb.1 _ h2; omega

theorem Has.neg (ha : a.Has x) : a.neg.Has (-x) := by
  constructor
  · intro l hl
    simp only [Interval.neg] at hl
    cases h1 : a.2 <;> simp only [h1, Option.map_none, Option.map_some, reduceCtorEq,
      Option.some.injEq] at hl
    subst hl; have := ha.2 _ h1; omega
  · intro h hh
    simp only [Interval.neg] at hh
    cases h1 : a.1 <;> simp only [h1, Option.map_none, Option.map_some, reduceCtorEq,
      Option.some.injEq] at hh
    subst hh; have := ha.1 _ h1; omega

/-- A product of two integers within intervals lies between the products of their bounds. -/
theorem mul_between {al ah bl bh x y : Int} (hx : al ≤ x ∧ x ≤ ah) (hy : bl ≤ y ∧ y ≤ bh) :
    (min (min (min (al * bl) (al * bh)) (ah * bl)) (ah * bh) ≤ x * y) ∧
      x * y ≤ max (max (max (al * bl) (al * bh)) (ah * bl)) (ah * bh) := by
  have row : ∀ {c : Int}, min (al * c) (ah * c) ≤ x * c ∧ x * c ≤ max (al * c) (ah * c) := by
    intro c
    rcases Int.le_total 0 c with hc | hc
    · have h1 := Int.mul_le_mul_of_nonneg_right hx.1 hc
      have h2 := Int.mul_le_mul_of_nonneg_right hx.2 hc
      constructor <;> omega
    · have h1 := Int.mul_le_mul_of_nonpos_right hx.1 hc
      have h2 := Int.mul_le_mul_of_nonpos_right hx.2 hc
      constructor <;> omega
  have col : x * bl ≤ x * y ∧ x * y ≤ x * bh ∨ x * bh ≤ x * y ∧ x * y ≤ x * bl := by
    rcases Int.le_total 0 x with hx0 | hx0
    · exact .inl ⟨Int.mul_le_mul_of_nonneg_left hy.1 hx0, Int.mul_le_mul_of_nonneg_left hy.2 hx0⟩
    · exact .inr ⟨Int.mul_le_mul_of_nonpos_left hx0 hy.2, Int.mul_le_mul_of_nonpos_left hx0 hy.1⟩
  have r1 := @row bl
  have r2 := @row bh
  rcases col with c | c <;> constructor <;> omega

theorem Has.mul (ha : a.Has x) (hb : b.Has y) : (a.mul b).Has (x * y) := by
  unfold Interval.mul
  split
  · rename_i al ah bl bh
    have hx : al ≤ x ∧ x ≤ ah := ⟨ha.1 _ rfl, ha.2 _ rfl⟩
    have hy : bl ≤ y ∧ y ≤ bh := ⟨hb.1 _ rfl, hb.2 _ rfl⟩
    obtain ⟨h1, h2⟩ := mul_between hx hy
    refine ⟨fun l hl => ?_, fun h hh => ?_⟩
    · simp only [Option.some.injEq, List.foldl_cons, List.foldl_nil] at hl
      subst hl; omega
    · simp only [Option.some.injEq, List.foldl_cons, List.foldl_nil] at hh
      subst hh; omega
  · exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩

theorem Has.within {i : Interval} {lo hi : Int} (h : i.Has x) (hw : i.within lo hi = true) :
    lo ≤ x ∧ x ≤ hi := by
  simp only [Interval.within, Bool.and_eq_true, Option.any_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨l, hl, hll⟩, ⟨u, hu, huu⟩⟩ := hw
  exact ⟨Int.le_trans hll (h.1 l hl), Int.le_trans (h.2 u hu) huu⟩

end Interval

namespace Facts

variable {F : Facts} {ν : Valuation}

/-- A term's interval: the bounds its facts give it against zero (facts.intervals). -/
def interval (F : Facts) (t : Term) : Interval := ((F.bound .zero t).map (- ·), F.bound t .zero)

theorem Holds.interval (h : F.Holds ν) (hz : ν .zero = 0) (t : Term) : (F.interval t).Has (ν t) := by
  constructor
  · intro l hl
    simp only [Facts.interval] at hl
    cases hb : F.bound .zero t <;> simp only [hb, Option.map_none, Option.map_some,
      reduceCtorEq, Option.some.injEq] at hl
    have := h.bound hb; rw [hz] at this; omega
  · intro u hu
    simp only [Facts.interval] at hu
    have := h.bound hu; rw [hz] at this; omega

/-- The facts that `res − t` lies between `c + l` and `c + h`, for the bounds of `i`
(facts.relative-bounds); with `t` zero and `c` zero, that `res` lies within `i`. -/
def relate (F : Facts) (t : Term) (c : Int) (i : Interval) : Facts :=
  let F := match i.2 with
    | some h => F.insert ⟨.res, t, c + h⟩
    | none => F
  match i.1 with
  | some l => F.insert ⟨t, .res, -(c + l)⟩
  | none => F

theorem Holds.relate (h : F.Holds ν) {t : Term} {c : Int} {i : Interval}
    (hi : i.Has (ν .res - ν t - c)) : (F.relate t c i).Holds ν := by
  unfold Facts.relate
  have h' : (match i.2 with
      | some h => F.insert ⟨.res, t, c + h⟩
      | none => F).Holds ν := by
    cases hu : i.2 with
    | none => exact h
    | some u => exact h.insert (by have := hi.2 u hu; simp only [Diff.Holds]; omega)
  cases hl : i.1 with
  | none => exact h'
  | some l => exact h'.insert (by have := hi.1 l hl; simp only [Diff.Holds]; omega)

/-- `res` equal to `t + c`. -/
def equate (F : Facts) (t : Term) (c : Int) : Facts := F.relate t c (some 0, some 0)

theorem Holds.equate (h : F.Holds ν) {t : Term} {c : Int} (he : ν .res = ν t + c) :
    (F.equate t c).Holds ν :=
  h.relate ⟨fun _ hl => by cases hl; omega, fun _ hh => by cases hh; omega⟩

/-- The linear form `t + c` of the value pushed `i`th, when the facts still give it: the value
is `t + c` and `t` is current (facts.linear-forms). -/
def linAt (F : Facts) (i : Nat) : Option (Term × Int) → Option (Term × Int)
  | some (t, c) =>
    if (F.bound (.opnd i) t).any (· ≤ c) && (F.bound t (.opnd i)).any (· ≤ -c) then some (t, c)
    else none
  | none => none

theorem Holds.linAt (h : F.Holds ν) {i : Nat} {l : Option (Term × Int)} {t : Term} {c : Int}
    (hl : F.linAt i l = some (t, c)) : ν (.opnd i) = ν t + c := by
  cases l with
  | none => cases hl
  | some p =>
    obtain ⟨t', c'⟩ := p
    simp only [Facts.linAt] at hl
    split at hl
    · rename_i hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp only [Bool.and_eq_true, Option.any_eq_true, decide_eq_true_eq] at hb
      obtain ⟨⟨a, ha, hac⟩, ⟨b, hb, hbc⟩⟩ := hb
      have := h.bound ha; have := h.bound hb; omega
    · cases hl

/-- The value an expression gave, pushed as the `d`th value read and not yet used: `res`
renamed to it, and what an earlier push there said dropped (facts.analysis-order). -/
def push (F : Facts) (d : Nat) : Facts :=
  (F.restrict fun t => t != .opnd d && t != .opndLen d).map fun t =>
    match t with
    | .res => .opnd d
    | .reslen => .opndLen d
    | t => t

theorem Holds.push {fr : Copy.Frame} {st : List Value} {v u : Value} (h : F.Holds (fr.nu st v)) :
    (F.push st.length).Holds (fr.nu (st ++ [v]) u) := by
  unfold Facts.push
  rw [holds_map]
  refine h.restrict fun t ht => ?_
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at ht
  cases t with
  | res => exact Copy.Frame.nu_push_opnd
  | reslen => exact Copy.Frame.nu_push_opndLen
  | opnd i =>
    have : i ≠ st.length := fun e => ht.1 (by rw [e])
    simp only [Function.comp, Copy.Frame.nu, List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_gt_of_ne this with hi | hi
    · rw [List.getElem?_append_left hi]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
  | opndLen i =>
    have : i ≠ st.length := fun e => ht.2 (by rw [e])
    simp only [Function.comp, Copy.Frame.nu, List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_gt_of_ne this with hi | hi
    · rw [List.getElem?_append_left hi]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
  | zero | val _ | len _ => rfl

end Facts

end Stilt
