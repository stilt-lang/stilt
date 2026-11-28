import Stilt.Ops

/-!
# Clamping

`clamp(self, lo, hi)` is written in Stilt as `self.max(lo).min(hi)` (std.clamp-and-sum), on the
natives `max` and `min` of the numeric types. What those natives compute gives the paragraph's
consequences: on an integer type, `hi` wins when `lo > hi` and a value between `lo` and `hi` is
kept; on a float type, a NaN anywhere gives NaN, so a NaN stays NaN. Lean's floats have no
theory of their order, so that `hi` wins on floats is left out.
-/

namespace Stilt

/-- `x.max(lo).min(hi)` on an integer type, as the natives compute it. -/
def IntTy.clamp (k : IntTy) (x lo hi : Int) : Except Fault Int :=
  k.method .max x lo >>= fun m => k.method .min m hi

theorem IntTy.clamp_eq (k : IntTy) {x lo hi : Int} (hx : k.Contains x) (hlo : k.Contains lo)
    (hhi : k.Contains hi) :
    k.clamp x lo hi = .ok (if (if x ≥ lo then x else lo) ≤ hi then (if x ≥ lo then x else lo)
      else hi) := by
  generalize hmd : (if x ≥ lo then x else lo) = m
  have hm : k.Contains m := by rw [← hmd]; split <;> assumption
  have hr : k.Contains (if m ≤ hi then m else hi) := by
    by_cases h1 : m ≤ hi
    · simp only [h1, ↓reduceIte]; exact hm
    · simp only [h1, ↓reduceIte]; exact hhi
  simp only [IntTy.clamp, IntTy.method, IntTy.within, IntTy.check, hx, hlo, and_self,
    ↓reduceIte, hmd, bind, Except.bind, hm, hhi, hr]

/-- std.clamp-and-sum: on an integer type, `hi` wins when `lo > hi`. -/
theorem IntTy.clamp_hi (k : IntTy) {x lo hi : Int} (hx : k.Contains x) (hlo : k.Contains lo)
    (hhi : k.Contains hi) (h : hi < lo) : k.clamp x lo hi = .ok hi := by
  rw [k.clamp_eq hx hlo hhi]
  have : ¬ (if x ≥ lo then x else lo) ≤ hi := by split <;> omega
  simp only [this, ↓reduceIte]

/-- std.clamp-and-sum: on an integer type with `lo ≤ hi`, the result is between `lo` and `hi`,
and is the value itself when that is between them. -/
theorem IntTy.clamp_between (k : IntTy) {x lo hi : Int} (hx : k.Contains x) (hlo : k.Contains lo)
    (hhi : k.Contains hi) (h : lo ≤ hi) : ∃ r, k.clamp x lo hi = .ok r ∧ lo ≤ r ∧ r ≤ hi ∧
      (lo ≤ x → x ≤ hi → r = x) := by
  rw [k.clamp_eq hx hlo hhi]
  refine ⟨_, rfl, ?_⟩
  by_cases h1 : x ≥ lo
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
    by_cases h2 : x ≤ hi
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]; omega
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]; omega
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h)]; omega

/-- `x.max(lo).min(hi)` on a float type, as the natives compute it. -/
def FloatVal.clamp (x lo hi : FloatVal) : Option FloatVal :=
  (FloatVal.extremum false x lo).bind fun m => FloatVal.extremum true m hi

/-- `min` and `max` on floats give one of their operands: the first when it is NaN, and the
second when only it is. -/
theorem FloatVal.extremum_cases {least : Bool} {x y z : FloatVal}
    (h : FloatVal.extremum least x y = some z) :
    (z = x ∨ z = y) ∧ (x.isNaN = true → z = x) ∧ (x.isNaN = false → y.isNaN = true → z = y) := by
  unfold FloatVal.extremum at h
  split at h
  · cases h
  · split at h
    · cases h; exact ⟨.inl rfl, fun _ => rfl, fun h' => by simp_all⟩
    · rename_i hx
      split at h
      · cases h; exact ⟨.inr rfl, fun h' => by simp_all, fun _ _ => rfl⟩
      · rename_i hy
        refine ⟨?_, fun h' => by simp_all, fun _ h' => by simp_all⟩
        split at h <;> (try split at h) <;> cases h <;> (try split) <;> simp

/-- Floats of one type have a clamp. -/
theorem FloatVal.clamp_some {x lo hi : FloatVal} (hlo : lo.type = x.type) (hhi : hi.type = x.type) :
    ∃ z, x.clamp lo hi = some z := by
  obtain ⟨m, hm, hmt⟩ := FloatVal.extremum_some false hlo
  obtain ⟨z, hz, -⟩ := FloatVal.extremum_some true (y := hi) (x := m) (by rw [hmt, hhi])
  exact ⟨z, by simp [FloatVal.clamp, hm, hz]⟩

/-- std.clamp-and-sum: on a float type, a NaN, whether `self`, `lo` or `hi`, gives NaN, and a
NaN `self` stays itself. -/
theorem FloatVal.clamp_nan {x lo hi z : FloatVal} (h : x.clamp lo hi = some z)
    (hn : x.isNaN = true ∨ lo.isNaN = true ∨ hi.isNaN = true) :
    z.isNaN = true ∧ (x.isNaN = true → z = x) := by
  simp only [FloatVal.clamp, Option.bind_eq_some_iff] at h
  obtain ⟨m, hm, hz⟩ := h
  have cm := FloatVal.extremum_cases hm
  have cz := FloatVal.extremum_cases hz
  by_cases hx : x.isNaN = true
  · have := cm.2.1 hx; subst this
    exact ⟨by rw [cz.2.1 hx]; exact hx, fun _ => cz.2.1 hx⟩
  · have hx' : x.isNaN = false := by simpa using hx
    refine ⟨?_, fun h' => absurd h' hx⟩
    by_cases hl : lo.isNaN = true
    · have := cm.2.2 hx' hl; subst this; rw [cz.2.1 hl]; exact hl
    · have hl' : lo.isNaN = false := by simpa using hl
      have hh : hi.isNaN = true := by simp_all
      have hm' : m.isNaN = false := by rcases cm.1 with rfl | rfl <;> assumption
      rw [cz.2.2 hm' hh]; exact hh

end Stilt
