import Stilt.Cells
import Stilt.Moves.Mask
import Stilt.Moves.Justified
import Stilt.Moves.Memory
import Stilt.InPlace.Evolves

/-!
# The relation

`MAgrees m fr s`: a copy frame `fr` and a `Moving` state `s` agree on the
bindings that the mask `m` keeps live. Those agree as `InPlace.Agrees` asks:
each holds the value its reference reaches, and their references reach
disjoint parts of the store. An ended binding may hold anything, and its
reference may reach storage that a live binding now owns.

Each operation of the evaluator keeps the relation, reading and writing live
bindings only, and a last use ends its binding as it hands its storage over.
-/

namespace Stilt

open InPlace

namespace InPlace

/-! ## Agreement without a binding -/

theorem Holds.dropName {st : List Value} (x : Name) :
    ∀ {fr : Copy.Frame} {env : List (Name × Ref)}, Holds st fr env →
      Holds st (Moving.dropName x fr) (Moving.dropName x env)
  | [], [], _ => trivial
  | (z, _) :: fr, (_, _) :: env, ⟨rfl, hd, h⟩ => by
    by_cases hz : z = x
    · simpa [Moving.dropName, hz] using h
    · simp only [Moving.dropName, hz, ↓reduceIte]
      exact ⟨rfl, hd, Holds.dropName x h⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem disjoint_dropName {x : Name} {r : Ref} :
    ∀ {env : List (Name × Ref)}, env.Pairwise (fun a b => a.2.Disjoint b.2) →
      env.lookup x = some r → ∀ e ∈ Moving.dropName x env, e.2.Disjoint r
  | [], _, h => by simp at h
  | (z, rz) :: env, hp, hl => by
    rw [List.pairwise_cons] at hp
    by_cases hz : z = x
    · subst hz
      simp only [List.lookup_cons_self, Option.some.injEq] at hl
      subst hl
      simp only [Moving.dropName, ↓reduceIte]
      exact fun e he => (hp.1 e he).symm
    · rw [lookup_cons_ne (Ne.symm hz)] at hl
      simp only [Moving.dropName, hz, ↓reduceIte]
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hp.1 _ (mem_of_lookup hl)
      · exact disjoint_dropName hp.2 hl e he

/-- Leaving out a binding keeps the agreement of the others. -/
theorem Agrees.drop {fr : Copy.Frame} {s : State} (h : Agrees fr s) (x : Name) :
    Agrees (Moving.dropName x fr) ⟨Moving.dropName x s.env, s.store⟩ :=
  ⟨h.holds.dropName x, h.disjoint.sublist (Moving.sublist_dropName x _),
    fun xv hxv => h.safe xv ((Moving.sublist_dropName x _).subset hxv)⟩

/-- A new binding that takes over the reference of `x`, which ends, agrees
with the value of `x`. -/
theorem Agrees.rebind {fr : Copy.Frame} {s : State} (h : Agrees fr s) {x y : Name} {v : Value}
    {r : Ref} (hv : fr.lookup x = some v) (hr : s.env.lookup x = some r) :
    Agrees ((y, v) :: Moving.dropName x fr) ⟨(y, r) :: Moving.dropName x s.env, s.store⟩ := by
  have hd : deref ⟨[], s.store⟩ r [] = .ok v := by
    rcases h.holds.lookup x with ⟨h₁, -⟩ | ⟨v', r', h₁, h₂, hd⟩
    · rw [h₁] at hv
      cases hv
    · rw [h₁] at hv
      rw [h₂] at hr
      cases hv
      cases hr
      exact hd
  refine ⟨⟨rfl, hd, h.holds.dropName x⟩, .cons ?_ (h.drop x).disjoint, fun xv hxv => ?_⟩
  · exact fun e he => (disjoint_dropName h.disjoint hr e he).symm
  · rcases List.mem_cons.1 hxv with rfl | hxv
    · exact h.safe (x, v) (mem_of_lookup hv)
    · exact (h.drop x).safe xv hxv

/-- Writes below the references of some bindings are writes below the
references of any list that holds them. -/
theorem Evolves.of_sub {e e' : List (Name × Ref)} {st st' : List Value} (hsub : ∀ a ∈ e, a ∈ e')
    (h : Evolves ⟨e, st⟩ ⟨e, st'⟩) : Evolves ⟨e', st⟩ ⟨e', st'⟩ := by
  obtain ⟨-, W, st₁, extra, hs, hW, hseq⟩ := h
  refine ⟨rfl, W, st₁, extra, hs, fun pw hpw => ?_, hseq⟩
  obtain ⟨P, hP, q, hq⟩ := hW pw hpw
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hP
  exact ⟨a.2.toPath, List.mem_map.2 ⟨a, hsub a ha, rfl⟩, q, hq⟩

end InPlace

namespace Moving

/-- A copy frame and a `Moving` state agree on the bindings that `m` keeps
live: each holds the value its reference reaches, their references reach
disjoint parts of the store, and their values are safe and justified. Every
reference reaches a location of the store. -/
structure MAgrees (m : List Bool) (fr : Copy.Frame) (s : State) : Prop where
  len : m.length = fr.length
  align : fr.map Prod.fst = s.env.map Prod.fst
  agrees : Agrees (keep m fr) ⟨keep m s.env, s.store⟩
  valid : Valid s
  just : ∀ xv ∈ keep m fr, xv.2.Justified

/-- The names of a frame's bindings, the newest first. -/
abbrev names (fr : Copy.Frame) : List Name := fr.map Prod.fst

namespace MAgrees

variable {m : List Bool} {fr : Copy.Frame} {s : State}

theorem len_env (h : MAgrees m fr s) : m.length = s.env.length := by
  rw [h.len, ← List.length_map (f := Prod.fst), h.align, List.length_map]

theorem lookup_frame (h : MAgrees m fr s) {x : Name} (hx : LiveAt x m (names fr)) :
    (keep m fr).lookup x = fr.lookup x :=
  lookup_keep h.len hx

theorem lookup_env (h : MAgrees m fr s) {x : Name} (hx : LiveAt x m (names fr)) :
    (keep m s.env).lookup x = s.env.lookup x :=
  lookup_keep h.len_env (by rw [← h.align]; exact hx)

/-- Both models read a live binding alike. -/
theorem read (h : MAgrees m fr s) {x : Name} (hx : LiveAt x m (names fr)) (p : Path) :
    Copy.read fr x p = InPlace.read s x p := by
  have h₁ : Copy.read fr x p = Copy.read (keep m fr) x p := by
    simp only [Copy.read, h.lookup_frame hx]
  have h₂ : InPlace.read s x p = InPlace.read ⟨keep m s.env, s.store⟩ x p := by
    simp only [InPlace.read, h.lookup_env hx]
    rfl
  rw [h₁, h₂, h.agrees.read]

theorem read_ok (h : MAgrees m fr s) {x : Name} (hx : LiveAt x m (names fr)) {p : Path}
    {v : Value} (hv : Copy.read fr x p = .ok v) : v.Safe ∧ v.Justified := by
  have h₁ : Copy.read (keep m fr) x p = .ok v := by
    simpa only [Copy.read, h.lookup_frame hx] using hv
  refine ⟨h.agrees.read_safe h₁, ?_⟩
  unfold Copy.read at h₁
  split at h₁
  · rename_i w hw
    exact Value.Justified.get (h.just (x, w) (mem_of_lookup hw)) h₁
  · cases h₁

end MAgrees

/-- A state of copy-in, copy-out and a `Moving` state agree under the mask
`m`: their frames agree under it, in one world, whose cells hold safe and justified values. -/
def MAgreesIn (m : List Bool) (fr : Copy.State) (s : State × World) : Prop :=
  MAgrees m fr.1 s.1 ∧ fr.2 = s.2 ∧ fr.2.All fun v => v.Safe ∧ v.Justified

end Moving

end Stilt
