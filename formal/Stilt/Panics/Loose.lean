import Stilt.Panics.Runs
import Stilt.Panics.Sites

/-!
# Code that may panic but not overflow

Code limited by `without overflow` alone may panic, but not with `overflow`
(effects.without-overflow): where `lim.panics` allows panics, an index, a store at an index
and an operation that panics are allowed, and only an operation that overflows at its
types, or names a function that may, is a site. Reading and writing a value at a path
panics only with `bounds` or stuck, and keeps values panic-free, so each step that may
panic ends as `lim` allows (`Limited.Allowed`).
-/

namespace Stilt

variable {lim : Limited} {α : Type}

/-- A result whose panics `lim` allows. -/
def Limited.Allowed (lim : Limited) (x : Except Fault α) : Prop :=
  ∀ k, x = .error (.panic k) → lim.Allows k

/-- Where `lim` allows panics, a result that doesn't overflow, or where `lim` allows overflow
too, is one whose panics it allows. -/
theorem Limited.allowed_of {x : Except Fault α} (hp : lim.panics = true)
    (h : lim.overflows = true ∨ NoOverflow x) : lim.Allowed x := fun k hk => by
  by_cases hk' : k = .overflow
  · rcases h with h | h
    · exact .inl ⟨hk', h⟩
    · exact absurd hk' (h k hk)
  · exact .inr (.inr ⟨hk', hp⟩)

theorem Value.get_noOverflow (v : Value) (p : Path) : NoOverflow (v.get p) := by
  induction p generalizing v with
  | nil => exact NoOverflow.ok _
  | cons s p ih =>
    cases v <;> cases s <;> simp only [Value.get] <;> first
      | exact NoOverflow.stuck
      | (split
         · exact ih _
         · first | exact NoOverflow.stuck | exact NoOverflow.panic (by decide))

theorem Value.set_noOverflow (v : Value) (p : Path) (w : Value) : NoOverflow (v.set p w) := by
  induction p generalizing v with
  | nil => exact NoOverflow.ok _
  | cons s p ih =>
    cases v <;> cases s <;> simp only [Value.set] <;> first
      | exact NoOverflow.stuck
      | (split
         · exact NoOverflow.map _ (ih _)
         · first | exact NoOverflow.stuck | exact NoOverflow.panic (by decide))

namespace Value.PanicFree

/-- A part of a panic-free value is panic-free, at any path. -/
theorem get_ok {v : Value} {p : Path} {u : Value} (hv : v.PanicFree lim) (h : v.get p = .ok u) :
    u.PanicFree lim := by
  induction p generalizing v with
  | nil => cases h; exact hv
  | cons s p ih =>
    cases v <;> cases s <;> simp only [Value.get] at h <;> try cases h
    · split at h
      · rename_i x hx
        cases hv with
        | record hfs => exact ih (hfs (_, x) (mem_of_lookup hx)) h
      · cases h
    · split at h
      · rename_i x hx
        cases hv with
        | list hvs =>
          unfold elemAt? at hx
          split at hx
          · exact ih (hvs x (List.mem_of_getElem? hx)) h
          · cases hx
      · cases h

/-- Writing a panic-free value into a panic-free one, at any path, gives a panic-free value. -/
theorem set_ok {v w u : Value} {p : Path} (hv : v.PanicFree lim) (hw : w.PanicFree lim)
    (h : v.set p w = .ok u) : u.PanicFree lim := by
  induction p generalizing v u with
  | nil => cases h; exact hw
  | cons s p ih =>
    cases v <;> cases s <;> simp only [Value.set] at h <;> try cases h
    · split at h
      · rename_i x hx
        cases hv with
        | record hfs =>
          cases hs : x.set p w with
          | error => rw [hs] at h; cases h
          | ok x' =>
            rw [hs] at h; cases h
            have hx' := ih (hfs (_, x) (mem_of_lookup hx)) hs
            refine .record fun fv hfv => ?_
            rcases mem_assocSet hfv with hfv | hfv
            · exact hfs fv hfv
            · exact hfv ▸ hx'
      · cases h
    · split at h
      · rename_i x hx
        cases hv with
        | list hvs =>
          unfold elemAt? at hx
          split at hx
          · cases hs : x.set p w with
            | error => rw [hs] at h; cases h
            | ok x' =>
              rw [hs] at h; cases h
              have hx' := ih (hvs x (List.mem_of_getElem? hx)) hs
              refine .list fun y hy => ?_
              rcases List.mem_or_eq_of_mem_set hy with hy | rfl
              · exact hvs y hy
              · exact hx'
          · cases hx
      · cases h

end Value.PanicFree

/-- Writing a panic-free value into a panic-free frame, at any path, doesn't overflow and
keeps the frame panic-free. -/
theorem Frame.PanicFree.write_any {fr : Copy.Frame} (hfr : Frame.PanicFree lim fr) (x : Name)
    (p : Path) {w : Value} (hw : w.PanicFree lim) :
    NoOverflow (Copy.write fr x p w) ∧ ∀ fr', Copy.write fr x p w = .ok fr' → Frame.PanicFree lim fr' := by
  unfold Copy.write
  split
  · rename_i v hv
    refine ⟨NoOverflow.map _ (Value.set_noOverflow v p w), fun fr' h => ?_⟩
    cases hs : v.set p w with
    | error => rw [hs] at h; cases h
    | ok v' =>
      rw [hs] at h; cases h
      have hv' := Value.PanicFree.set_ok (hfr (x, v) (mem_of_lookup hv)) hw hs
      intro xv hxv
      rcases mem_assocSet hxv with hxv | hxv
      · exact hfr xv hxv
      · exact hxv ▸ hv'
  · exact ⟨NoOverflow.stuck, fun _ h => by cases h⟩

namespace Eval.PanicFree

variable {G : List Known} {P : α → Prop}

theorem faultA {γ : Type} {f : Fault} (hf : lim.Allowed (Except.error f : Except Fault γ))
    {s : Copy.State} (hs : State.PanicFree lim s) : Outcome.PanicFree lim P (Outcome.fault f s) := by
  cases f with
  | panic k => exact ⟨hf k rfl, hs⟩
  | stuck => trivial

theorem ofExceptA {x : Except Fault α} (h : lim.Allowed x) (hP : ∀ a, x = .ok a → P a) :
    Eval.PanicFree lim G P (Eval.ofExcept x) := by
  intro s hs _
  cases x with
  | ok a => exact ⟨hP a rfl, hs⟩
  | error f => exact faultA h hs

theorem updateA {f : Copy.State → Except Fault Copy.State}
    (h : ∀ s, State.PanicFree lim s → lim.Allowed (f s) ∧ ∀ s', f s = .ok s' → State.PanicFree lim s') :
    Eval.PanicFree lim G (fun _ => True) (Eval.update f) := by
  intro s hs _
  obtain ⟨h1, h2⟩ := h s hs
  unfold Eval.update
  cases hf : f s with
  | ok s' => exact ⟨trivial, h2 s' hf⟩
  | error e => rw [hf] at h1; exact faultA h1 hs

theorem asIntA {v : Value} : Eval.PanicFree lim G (fun _ => True) (Eval.asInt v) := by
  cases v <;> first | exact pure trivial | exact stuck

/-- An operation in the world whose panics `lim` allows. -/
theorem runA (w : WriteBack) {R : Value → Prop} {o : Op} {vs : List Value}
    (hc : lim.Allowed (o.apply vs)) (hvs : ∀ v ∈ vs, v.PanicFree lim)
    (hP : ∀ x v x', o.run vs x = .ok (v, x') → R v) :
    Eval.PanicFree lim G R (Eval.world (Copy.memoryWith w) (o.run vs)) := by
  rintro ⟨fr, x⟩ hs _
  cases hf : o.run vs x with
  | ok p =>
    rw [show Eval.world (Copy.memoryWith w) (o.run vs) (fr, x) = .done p.1 (fr, p.2) from
      Eval.world_ok hf]
    exact ⟨hP x p.1 p.2 hf, hs.1, hs.2.run hvs hf⟩
  | error e =>
    rw [show Eval.world (Copy.memoryWith w) (o.run vs) (fr, x) = .fault e (fr, x) from
      Eval.world_error hf]
    refine faultA (γ := Value) (fun k hk => ?_) hs
    rcases Op.run_error hf with rfl | ha
    · cases hk
    · exact hc k (ha.trans (by rw [hk]))

section Runs

variable {run : Expr → Eval Copy.State Value} (h : PanicFreeRun lim run) (hk : KeepsRun run)
include h hk

/-- The indexes of a place's path, which may be out of bounds where `lim` allows panics. -/
theorem pathA : ∀ {G : List Known} (ps : List Projection), pathPanicFree lim G ps = true →
    Eval.PanicFree lim G (fun _ => True) (Eval.path run ps)
  | _, [], _ => pure trivial
  | G, .field _ :: ps, hps => by
    simp only [pathPanicFree] at hps
    exact bind (pathA ps hps) (Eval.Keeps.path hk ps (List.Subset.refl _) (List.Subset.refl _))
      fun _ _ => pure trivial
  | G, .index i :: ps, hps => by
    simp only [pathPanicFree, Bool.and_eq_true] at hps
    exact bind (bind (h G i hps.1) (hk i _ _ (List.Subset.refl _) (List.Subset.refl _))
        fun _ _ => asIntA)
      (Eval.Keeps.bind (hk i _ _ (List.Subset.refl _) (List.Subset.refl _)) fun v _ =>
        Eval.Keeps.asInt v) fun _ _ =>
      bind (pathA ps hps.2) (Eval.Keeps.path hk ps (List.Subset.refl _) (List.Subset.refl _))
        fun _ _ => pure trivial

/-- An index of a value, where `lim` allows it to be out of bounds. -/
theorem indexA (hp : lim.panics = true) {e i : Expr} (he : e.panicFreeIn lim G = true)
    (hi : i.panicFreeIn lim (withoutNames G e.writes) = true) :
    Eval.PanicFree lim G (Value.PanicFree lim) (do
      let v ← run e
      let k ← run i >>= Eval.asInt
      Eval.ofExcept (v.get [.index k])) :=
  bind (h G e he) (hk e _ _ (List.Subset.refl _) (List.Subset.refl _)) fun v hv =>
    bind (bind (h _ i hi) (hk i _ _ (List.Subset.refl _) (List.Subset.refl _)) fun _ _ => asIntA)
      (Eval.Keeps.bind (hk i _ _ (List.Subset.refl _) (List.Subset.refl _)) fun u _ =>
        Eval.Keeps.asInt u) fun _ _ =>
      ofExceptA (lim.allowed_of hp (.inr (Value.get_noOverflow v _))) fun _ hu =>
        Value.PanicFree.get_ok hv hu

/-- An assignment to a place whose indexes `lim` allows to be out of bounds. -/
theorem assignA (w : WriteBack) (hp : lim.panics = true) (x : Name) {ps : List Projection}
    {value : Expr} (hps : pathPanicFree lim G ps = true)
    (hv : value.panicFreeIn lim (withoutNames G (pathWrites ps)) = true) :
    Eval.PanicFree lim G (Value.PanicFree lim) (Eval.assign (Copy.memoryWith w) run x ps value) :=
  bind (pathA h hk ps hps) (Eval.Keeps.path hk ps (List.Subset.refl _) (List.Subset.refl _))
    fun p _ =>
    bind (h _ value hv) (hk value _ _ (List.Subset.refl _) (List.Subset.refl _)) fun u hu =>
      bind (updateA fun s hs => by
          rw [Eval.Keeps.memoryWith_write]
          obtain ⟨hn, hf⟩ := hs.1.write_any x p hu
          refine ⟨lim.allowed_of hp (.inr (NoOverflow.map _ hn)), fun s' h' => ?_⟩
          cases hw : Copy.write s.1 x p u with
          | error => rw [hw] at h'; cases h'
          | ok fr' => rw [hw] at h'; cases h'; exact ⟨hf fr' hw, hs.2⟩)
        (Eval.Keeps.update (L := [x]) w x _ _ (List.mem_singleton_self x)
          fun _ => List.mem_singleton_self x) fun _ _ => pure .unit

end Runs

end Eval.PanicFree

end Stilt
