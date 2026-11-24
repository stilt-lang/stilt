import Stilt.Sharing.Bind
import Stilt.Sharing.Unshare

/-!
# Frames that read alike

Facts on the bindings of a state of sharing that the steps changing them need: a frame whose
bindings, position by position, read what another's read agrees with the same frame of copies;
homes that don't overlap are distinct; and `evacuate` gives each binding it settles a new
location of its own, so the homes still don't overlap.
-/

namespace Stilt.Sharing

open InPlace (Ref)

/-- Two frames of the same names whose bindings, position by position, read alike in two
stores. -/
def ReadsAlike (st st' : Array Value) : List (Name × Entry) → List (Name × Entry) → Prop
  | [], [] => True
  | a :: env, b :: env' =>
    (a.1 = b.1 ∧ deref ⟨[], st'⟩ b.2.ref [] = deref ⟨[], st⟩ a.2.ref []) ∧ ReadsAlike st st' env env'
  | _, _ => False

theorem Holds.alike {st st' : Array Value} :
    ∀ {fr : Copy.Frame} {env env' : List (Name × Entry)}, Holds st fr env →
      ReadsAlike st st' env env' → Holds st' fr env'
  | [], [], [], _, _ => trivial
  | (_, _) :: _, (_, _) :: _, (_, _) :: _, ⟨h₁, h₂, h₃⟩, ⟨⟨hn, hd⟩, hr⟩ =>
    ⟨h₁.trans hn, hd.trans h₂, Holds.alike h₃ hr⟩
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim
  | [], [], _ :: _, _, h => h.elim
  | _ :: _, _ :: _, [], _, h => h.elim

theorem overlaps_self (r : Ref) : overlaps r r = true := by
  simp [overlaps, List.isPrefixOf_iff_prefix]

theorem overlaps_comm (a b : Ref) : overlaps a b = overlaps b a := by
  simp only [overlaps, Bool.beq_comm, Bool.or_comm]

/-- A part that overlaps nothing of `a` overlaps nothing below it. -/
theorem overlaps_at {a b : Ref} (h : overlaps a b = false) (p : Path) : overlaps (a.at p) b = false := by
  simp only [overlaps, InPlace.Ref.at, Bool.and_eq_false_iff, Bool.or_eq_false_iff] at h ⊢
  rcases h with h | ⟨h₁, h₂⟩
  · exact .inl h
  · refine .inr ⟨?_, ?_⟩
    · cases hp : (a.path ++ p).isPrefixOf b.path
      · rfl
      · exact absurd (List.isPrefixOf_iff_prefix.2 ((List.prefix_append _ _).trans
          (List.isPrefixOf_iff_prefix.1 hp))) (by simp [h₁])
    · cases hp : b.path.isPrefixOf (a.path ++ p)
      · rfl
      · have hp' := List.isPrefixOf_iff_prefix.1 hp
        rcases List.prefix_or_prefix_of_prefix hp' (List.prefix_append a.path p) with h' | h'
        · exact absurd (List.isPrefixOf_iff_prefix.2 h') (by simp [h₂])
        · exact absurd (List.isPrefixOf_iff_prefix.2 h') (by simp [h₁])

/-- A part with a location past every location the store has overlaps none of its parts. -/
theorem overlaps_fresh {a b : Ref} (h : b.loc < a.loc) : overlaps a b = false := by
  simp only [overlaps, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
  exact .inl (by omega)

/-- Entries whose homes don't overlap are distinct. -/
theorem ne_of_homes {a b : Entry} (h : overlaps a.home b.home = false) : a ≠ b := by
  rintro rfl
  rw [overlaps_self] at h
  cases h

end Stilt.Sharing
