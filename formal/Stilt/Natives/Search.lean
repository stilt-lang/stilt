import Stilt.StrNatives

/-!
# Finding a substring

What the native `find` gives (std.str-search): the byte offset of the first occurrence, where the
bytes of the substring start, with no occurrence before it; and none when there is none.
-/

namespace Stilt

namespace Str

/-- The offset `firstAt` gives is where `sub` starts, and it starts nowhere before. -/
theorem firstAt_first (sub : List UInt8) : ∀ (bs : List UInt8) (i n : Nat),
    Str.firstAt sub bs i = some n → i ≤ n ∧ sub.isPrefixOf (bs.drop (n - i)) = true ∧
      ∀ j < n - i, sub.isPrefixOf (bs.drop j) = false
  | [], i, n, h => by
    unfold Str.firstAt at h
    split at h
    · cases h
      rename_i hs
      cases sub with
      | nil => simp [List.isPrefixOf]
      | cons => simp at hs
    · cases h
  | b :: bs, i, n, h => by
    unfold Str.firstAt at h
    split at h
    · cases h; rename_i hp; simpa using hp
    · rename_i hp
      obtain ⟨hi, hpre, hnone⟩ := firstAt_first sub bs (i + 1) n h
      refine ⟨by omega, ?_, ?_⟩
      · have : n - i = (n - (i + 1)) + 1 := by omega
        rw [this, List.drop_succ_cons]; exact hpre
      · intro j hj
        cases j with
        | zero => rw [List.drop_zero]; exact Bool.eq_false_iff.mpr hp
        | succ j => rw [List.drop_succ_cons]; exact hnone j (by omega)

/-- `firstAt` finds nothing only where `sub` starts nowhere. -/
theorem firstAt_none (sub : List UInt8) : ∀ (bs : List UInt8) (i : Nat),
    Str.firstAt sub bs i = none → ∀ j ≤ bs.length, sub.isPrefixOf (bs.drop j) = false
  | [], i, h, j, hj => by
    unfold Str.firstAt at h
    split at h
    · cases h
    · rename_i hs
      have : j = 0 := by simpa using hj
      subst this
      cases sub with
      | nil => simp at hs
      | cons => rfl
  | b :: bs, i, h, j, hj => by
    unfold Str.firstAt at h
    split at h
    · cases h
    · rename_i hp
      cases j with
      | zero => rw [List.drop_zero]; exact Bool.eq_false_iff.mpr hp
      | succ j =>
        rw [List.drop_succ_cons]
        exact firstAt_none sub bs (i + 1) h j (by simp only [List.length_cons] at hj; omega)

/-- std.str-search: `find(sub)` gives the byte offset of the first occurrence of `sub`: its bytes
start there, and nowhere before; and `None` when they start nowhere. -/
theorem find_first (s sub : String) :
    (∀ n, Str.find false s sub = some n →
      sub.toUTF8.toList.isPrefixOf (s.toUTF8.toList.drop n) = true ∧
      ∀ j < n, sub.toUTF8.toList.isPrefixOf (s.toUTF8.toList.drop j) = false) ∧
    (Str.find false s sub = none →
      ∀ j ≤ s.toUTF8.toList.length, sub.toUTF8.toList.isPrefixOf (s.toUTF8.toList.drop j) = false) := by
  simp only [Str.find, Bool.false_eq_true, ↓reduceIte]
  refine ⟨fun n h => ?_, fun h => firstAt_none _ _ 0 h⟩
  have := firstAt_first _ _ 0 n h
  simpa using this.2

end Str

end Stilt
