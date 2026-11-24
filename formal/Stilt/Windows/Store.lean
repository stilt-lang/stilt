import Stilt.Windows.Relation
import Stilt.Windows.Through

/-!
# Stores that keep windows

How the changes of a store keep the windows that hold: a window reads its region, the part of
its location at its path, and a change that leaves the region as it was in both stores keeps
the window holding and every value whose windows it is read alike (`Holds.region`,
`VRel.region`). New locations, freed ones other than a window's own and writes at disjoint
paths leave regions as they were; so binding a variable keeps two states that agree, and so
does ending a binding whose location no window reads.
-/

namespace Stilt

namespace Windows

/-- The ranges of a window, sliced in turn. -/
def slices (ranges : List (Int × Int)) (v : Value) : Except Fault Value :=
  ranges.foldlM (fun v r => Op.view.apply [v, .int r.1, .int r.2]) v

theorem part_eq_region (sw : List (Option Value)) (w : Window) :
    part sw w.1 w.2.1 w.2.2 = regionW sw w >>= slices w.2.2 := by
  simp only [part, regionW]
  cases cell sw w.1 <;> rfl

theorem partIn_eq_region (si : List Value) (w : Window) :
    partIn si w.1 w.2.1 w.2.2 = regionI si w >>= slices w.2.2 := by
  simp only [partIn, regionI, cellIn]
  cases si[w.1]? <;> rfl

variable {sw sw' : List (Option Value)} {si si' : List Value} {w : Window}

theorem Holds.readAlike (h : Holds sw si w) : ReadAlike sw si w := by
  obtain ⟨d, hw', hi', hd, -⟩ := h
  refine ⟨by rw [part_eq_region, partIn_eq_region, hw', hi'], fun u hu => ?_⟩
  rw [partIn_eq_region, hi'] at hu
  exact free_slices hd w.2.2 hu

theorem Holds.region (h : Holds sw si w) (hw : regionW sw' w = regionW sw w)
    (hi : regionI si' w = regionI si w) : Holds sw' si' w := by
  obtain ⟨d, h₁, h₂, h₃⟩ := h
  exact ⟨d, hw.trans h₁, hi.trans h₂, h₃⟩

theorem regionW_lt {sw : List (Option Value)} {w : Window} {d : Value}
    (h : regionW sw w = .ok d) : w.1 < sw.length := by
  unfold regionW cell at h
  split at h
  · rename_i v hv
    exact (List.getElem?_eq_some_iff.1 hv).1
  · cases h

theorem regionI_lt {si : List Value} {w : Window} {d : Value}
    (h : regionI si w = .ok d) : w.1 < si.length := by
  unfold regionI cellIn at h
  split at h
  · rename_i v hv
    exact (List.getElem?_eq_some_iff.1 hv).1
  · cases h

theorem Holds.lt (h : Holds sw si w) : w.1 < sw.length := by
  obtain ⟨d, h₁, -⟩ := h
  exact regionW_lt h₁

theorem Holds.ltI (h : Holds sw si w) : w.1 < si.length := by
  obtain ⟨d, -, h₂, -⟩ := h
  exact regionI_lt h₂

/-- Reading a value against two in-place stores alike when they hold its windows' regions
alike. -/
theorem resolveIn_congr {x : Value} (h : ∀ w ∈ windowsOf x, regionI si' w = regionI si w) :
    resolveIn si' x = resolveIn si x :=
  mapWindows_congr x fun w hw => by rw [partIn_eq_region, partIn_eq_region, h w hw]

theorem VRel.region {x v : Value} (h : VRel si sw x v)
    (hw : ∀ w ∈ windowsOf x, regionW sw' w = regionW sw w)
    (hi : ∀ w ∈ windowsOf x, regionI si' w = regionI si w) : VRel si' sw' x v :=
  ⟨(resolveIn_congr hi).trans h.1, fun w hm => (h.2 w hm).region (hw w hm) (hi w hm)⟩

theorem VRel.free {v : Value} (hv : Free v) : VRel si sw v v :=
  ⟨resolveIn_free si hv, fun w hw => by simp [Free] at hv; rw [hv] at hw; cases hw⟩

theorem VRel.readAlike {x v : Value} (h : VRel si sw x v) : ∀ w ∈ windowsOf x, ReadAlike sw si w :=
  fun w hw => (h.2 w hw).readAlike

/-- What a value of windows reads, through any store that reads its windows alike. -/
theorem VRel.resolve {x v : Value} (h : VRel si sw x v) : resolve sw x = .ok v :=
  (resolve_eq_resolveIn h.readAlike).trans h.1

/-! ## Regions that changes keep -/

theorem regionW_append (extra : List (Option Value)) (h : w.1 < sw.length) :
    regionW (sw ++ extra) w = regionW sw w := by
  simp [regionW, cell, List.getElem?_append_left h]

theorem regionI_append (extra : List Value) (h : w.1 < si.length) :
    regionI (si ++ extra) w = regionI si w := by
  simp [regionI, cellIn, List.getElem?_append_left h]

theorem regionW_set_ne {ℓ : Nat} (c : Option Value) (h : ℓ ≠ w.1) :
    regionW (sw.set ℓ c) w = regionW sw w := by
  simp [regionW, cell, List.getElem?_set_ne h]

theorem regionI_set_ne {ℓ : Nat} (c : Value) (h : ℓ ≠ w.1) :
    regionI (si.set ℓ c) w = regionI si w := by
  simp [regionI, cellIn, List.getElem?_set_ne h]

/-- The store with each location from `n` on freed. -/
def freeStore (n : Nat) (st : List (Option Value)) : List (Option Value) :=
  st.take n ++ (st.drop n).map fun _ => none

theorem freeStore_length (n : Nat) (st : List (Option Value)) :
    (freeStore n st).length = st.length := by
  simp only [freeStore, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem freeStore_getElem?_lt {n ℓ : Nat} (st : List (Option Value)) (h : ℓ < n) :
    (freeStore n st)[ℓ]? = st[ℓ]? := by
  by_cases hl : ℓ < st.length
  · rw [freeStore, List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt h]
  · rw [List.getElem?_eq_none (by rw [freeStore_length]; omega), List.getElem?_eq_none (by omega)]

theorem freeStore_getElem?_ge {n ℓ : Nat} (st : List (Option Value)) (h : n ≤ ℓ) {x : Value} :
    (freeStore n st)[ℓ]? ≠ some (some x) := by
  intro hx
  by_cases hl : ℓ < st.length
  · unfold freeStore at hx
    rw [List.getElem?_append_right (by simp; omega)] at hx
    simp only [List.getElem?_map] at hx
    cases (st.drop n)[ℓ - (st.take n).length]? <;> simp at hx
  · rw [List.getElem?_eq_none (by rw [freeStore_length]; omega)] at hx
    cases hx

theorem freeFrom_store (n : Nat) (s : State × World) :
    (freeFrom n s).1.store = freeStore n s.1.store := rfl

theorem regionW_freeStore {n : Nat} (h : w.1 < n) : regionW (freeStore n sw) w = regionW sw w := by
  simp [regionW, cell, freeStore_getElem?_lt sw h]

end Windows

end Stilt
