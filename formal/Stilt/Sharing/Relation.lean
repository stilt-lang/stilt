import Stilt.Sharing.Store
import Stilt.Moves.Mask
import Stilt.InPlace.Safe

/-!
# The relation of sharing to copies

`Agrees m fr s`: a frame of copy-in, copy-out and a state of sharing agree on the bindings that
the mask `m` keeps live, as `Stilt.Moves.Relation` reads a mask: each live binding holds in the
copy frame the value its binding of sharing reads where it refers. A binding that is no longer
live may read anything: a `unique` write may have changed the storage it shares
(modes.shared-writes), which nothing reads after.

Every binding's home and the part it refers to are in the store, and the homes of a frame's
bindings don't overlap: a new home is a new location, and an `inout` parameter's home is its
argument's place, which no other argument's overlaps (modes.overlapping-inout). So a write
where a binding refers changes only what the bindings that refer into the same storage read.
-/

namespace Stilt

namespace Sharing

open InPlace (Ref)
open Moving (keep LiveAt)

/-- Each variable of a copy frame holds the value that its binding of sharing reads in the
store `st`, name by name. -/
def Holds (st : Array Value) : Copy.Frame → List (Name × Entry) → Prop
  | [], [] => True
  | (x, v) :: fr, (y, e) :: env => x = y ∧ deref ⟨[], st⟩ e.ref [] = .ok v ∧ Holds st fr env
  | _, _ => False

/-- A copy frame and a state of sharing agree on the bindings the mask `m` keeps live: each
holds the same value in both. Every binding's home and the part it refers to are in the store,
the homes of the frame's bindings don't overlap, and the copy frame's values are safe. -/
structure Agrees (m : List Bool) (fr : Copy.Frame) (s : State) : Prop where
  len : m.length = fr.length
  align : fr.map Prod.fst = s.env.map Prod.fst
  holds : Holds s.store (keep m fr) (keep m s.env)
  has : ∀ ye ∈ s.env, s.Has ye.2.home ∧ s.Has ye.2.ref
  homes : s.env.Pairwise fun a b => overlaps a.2.home b.2.home = false
  safe : ∀ xv ∈ fr, xv.2.Safe

namespace Holds

/-- A variable is in the frame exactly when it is in the state, and holds the value its binding
reads. -/
theorem lookup {st : Array Value} (x : Name) :
    ∀ {fr : Copy.Frame} {env : List (Name × Entry)}, Holds st fr env →
      (fr.lookup x = none ∧ env.lookup x = none) ∨
        ∃ v e, fr.lookup x = some v ∧ env.lookup x = some e ∧ deref ⟨[], st⟩ e.ref [] = .ok v
  | [], [], _ => .inl ⟨rfl, rfl⟩
  | (z, v) :: fr, (_, e) :: env, ⟨rfl, hd, h⟩ => by
    by_cases hx : x = z
    · subst hx
      exact .inr ⟨v, e, List.lookup_cons_self, List.lookup_cons_self, hd⟩
    · rw [lookup_cons_ne hx, lookup_cons_ne hx]
      exact lookup x h
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- Both models read a variable of agreeing frames alike. -/
theorem read {st : Array Value} {fr : Copy.Frame} {env : List (Name × Entry)} (h : Holds st fr env)
    (x : Name) (p : Path) : Copy.read fr x p = Sharing.read ⟨env, st⟩ x p := by
  rcases h.lookup x with ⟨h₁, h₂⟩ | ⟨v, e, h₁, h₂, hd⟩
  · simp [Copy.read, Sharing.read, h₁, h₂]
  · simp only [Copy.read, Sharing.read, h₁, h₂]
    have hd' : deref ⟨env, st⟩ e.ref [] = .ok v := hd
    rw [← List.nil_append p, deref_append, hd']
    rfl

end Holds

namespace Agrees

variable {m : List Bool} {fr : Copy.Frame} {s : State}

theorem len_env (h : Agrees m fr s) : m.length = s.env.length := by
  rw [h.len, ← List.length_map (f := Prod.fst), h.align, List.length_map]

/-- Both models read a live variable alike. -/
theorem read (h : Agrees m fr s) {x : Name} (hx : LiveAt x m (fr.map Prod.fst)) (p : Path) :
    Copy.read fr x p = Sharing.read s x p := by
  have h₁ : Copy.read fr x p = Copy.read (keep m fr) x p := by
    simp only [Copy.read, Moving.lookup_keep h.len hx]
  have h₂ : Sharing.read s x p = Sharing.read ⟨keep m s.env, s.store⟩ x p := by
    simp only [Sharing.read, Moving.lookup_keep h.len_env (by rw [← h.align]; exact hx)]
    rfl
  rw [h₁, h₂, h.holds.read]

end Agrees

end Sharing

end Stilt
