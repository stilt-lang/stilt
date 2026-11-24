import Stilt.InPlace.Writes
import Stilt.Views.Places
import Stilt.Writes.Semantics

/-!
# Parts of lists, written back

The laws of `splice` and `restore`: writing back the part a view copied
changes nothing, a window into what a write-back gave reads the part written
back, and a write through the window is a write to the part (projections.places-through-views).
-/

namespace Stilt.Writes

open Stilt.Views (Store bounded slice cell source)

theorem bounded_iff {n : Nat} {a b : Int} : bounded n a b = true ↔ 0 ≤ a ∧ a ≤ b ∧ b ≤ n := by
  simp [bounded]

/-! ## Splicing -/

theorem splice_slice {vs : List Value} {a b : Int} (h : bounded vs.length a b = true) :
    splice vs a b (slice vs a b) = vs := by
  rw [bounded_iff] at h
  have hb : b.toNat = a.toNat + (b - a).toNat := by omega
  simp only [splice, slice]
  rw [hb, ← List.drop_drop, List.take_append_drop, List.take_append_drop]

theorem splice_length {vs part : List Value} {a b : Int} (h : bounded vs.length a b = true)
    (hp : part.length = (b - a).toNat) : (splice vs a b part).length = vs.length := by
  rw [bounded_iff] at h
  simp only [splice, List.length_append, List.length_take, List.length_drop, hp]
  omega

theorem take_length {vs : List Value} {a b : Int} (h : bounded vs.length a b = true) :
    (vs.take a.toNat).length = a.toNat := by
  rw [bounded_iff] at h
  simp only [List.length_take]
  omega

theorem slice_splice {vs part : List Value} {a b : Int} (h : bounded vs.length a b = true)
    (hp : part.length = (b - a).toNat) : slice (splice vs a b part) a b = part := by
  simp only [slice, splice, List.drop_left' (take_length h), List.take_left' hp]

theorem splice_set {vs part : List Value} {a b k : Int} (h : bounded vs.length a b = true)
    (hk : 0 ≤ k) (hk' : k < part.length) (w : Value) :
    (splice vs a b part).set (a + k).toNat w = splice vs a b (part.set k.toNat w) := by
  have ht := take_length h
  rw [bounded_iff] at h
  simp only [splice]
  rw [List.set_append_right _ _ (by omega), List.set_append_left _ _ (by omega)]
  congr 3
  omega

/-! ## Writing back -/

theorem restore_ok {c c' : Value} {π : Path} {a b : Int} {part : List Value}
    (h : restore c π a b part = .ok c') :
    ∃ vs, c.get π = .ok (.list vs) ∧ bounded vs.length a b = true ∧
      part.length = (b - a).toNat ∧ c.set π (.list (splice vs a b part)) = .ok c' := by
  unfold restore at h
  split at h
  · rename_i vs hvs
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨vs, hvs, hc.1, hc.2, h⟩
    · cases h
  · cases h

/-- Writing back the part a view copied changes nothing. -/
theorem restore_slice {c : Value} {π : Path} {vs : List Value} {a b : Int}
    (hc : c.get π = .ok (.list vs)) (hb : bounded vs.length a b = true) :
    restore c π a b (slice vs a b) = .ok c := by
  simp [restore, hc, hb, Views.slice_length hb, splice_slice hb, Value.set_of_get hc]

/-- A window into what a write-back gave reads the part written back. -/
theorem restore_part {store : Store} {ℓ : Nat} {c c' : Value} {π : Path} {a b : Int}
    {part : List Value} (h : restore c π a b part = .ok c') (hc : cell store ℓ = .ok c') :
    (WVal.window ℓ π a b).part store = .ok part := by
  obtain ⟨vs, -, hb, hp, hset⟩ := restore_ok h
  have hb' : bounded (splice vs a b part).length a b = true := by
    rw [splice_length hb hp]
    exact hb
  simp [WVal.part, source, hc, Value.get_of_set hset, hb', slice_splice hb hp]

/-- A write through a window into what a write-back gave is the write-back of
the part with the element written. -/
theorem restore_put {c c' : Value} {π : Path} {a b k : Int} {part : List Value} (w : Value)
    (h : restore c π a b part = .ok c') (hk : 0 ≤ k) (hk' : k < b - a) :
    c'.set (π ++ [.index (a + k)]) w = restore c π a b (part.set k.toNat w) := by
  obtain ⟨vs, hvs, hb, hp, hset⟩ := restore_ok h
  have hlen := splice_length hb hp
  have hb' := hb
  rw [bounded_iff] at hb'
  have hel : elemAt? (splice vs a b part) (a + k) =
      some ((splice vs a b part)[(a + k).toNat]'(by omega)) := by
    simp only [elemAt?, show 0 ≤ a + k by omega, ite_true]
    exact List.getElem?_eq_getElem _
  have hpk : k < part.length := by omega
  rw [Value.set_append, Value.get_of_set hset]
  simp only [Except.bind, Value.set, hel, Functor.map, Except.map]
  rw [Value.set_set_self hset, splice_set hb hk hpk]
  simp [restore, hvs, hb, hp]

end Stilt.Writes
