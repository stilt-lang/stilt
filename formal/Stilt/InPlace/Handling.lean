import Stilt.InPlace.Call
import Stilt.Handling.Related

/-!
# Performances and handlers in place

A performance ends alike in both models, and a `with` handles alike what its
block ends with: its clauses are calls of the same safe closures on the same
safe values, and what a clause or the rest of the block ends with relates the
frame and the state it ends with, wherever the other runs left off
(handlers.performing-operation and handlers.with).
-/

namespace Stilt.InPlace

/-- A handler's clause, a field of a safe record, is safe. -/
theorem Value.Safe.clause {hv c : Value} {n : Name} (hhv : hv.Safe) (h : hv.clause? n = some c) :
    c.Safe := by
  cases hv <;> simp only [Value.clause?, reduceCtorEq] at h
  cases hhv with
  | record hf => exact hf _ (Stilt.mem_of_lookup h)

namespace Sim

/-- A performance of a safe value (handlers.performing-operation). -/
theorem perform {op : Operation} {v : Value} (hv : v.Safe) :
    Sim Value.Safe (Eval.perform Copy.memory op v) (Eval.perform InPlace.memory op v) :=
  fun _ s hs => ⟨⟨rfl, rfl, hv, hs, Evolves.refl s.1⟩, fun _ _ _ _ ⟨hw, hws, hx⟩ =>
    ⟨hw, hws, ⟨hs.1, hx⟩, Evolves.refl s.1⟩⟩

/-- What the two runs relate from `s` they relate at the frames of a state of
each model that agree and evolved from `s`, in the worlds they relate. -/
theorem lifts {s : State} {fr : Copy.State} {s₁ : State × World} (hag : AgreesIn fr s₁)
    (hev : Evolves s s₁.1) : (Corr.relation Value.Safe s).Lifts Copy.memory InPlace.memory fr s₁ :=
  ⟨fun _ _ _ _ h => ⟨h.1, h.2.1, ⟨hag.1, h.2.2.1.2⟩, hev⟩,
    fun _ _ _ _ h => ⟨h.1, h.2.1, ⟨hag.1, h.2.2.1.2⟩, hev⟩,
    fun _ _ _ _ h => ⟨h.1, h.2.1, ⟨hag.1, h.2.2.1.2⟩, hev⟩,
    fun _ _ _ _ h => ⟨h.1, ⟨hag.1, h.2.1.2⟩, hev⟩,
    fun _ _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1, ⟨hag.1, h.2.2.2.1.2⟩, hev⟩⟩

/-- A `with` of a safe handler keeps the simulation (handlers.with). -/
theorem handleWith {D : Decls} (hD : DeclsSafe D) {run : Expr → Eval Copy.State Value}
    {run' : Expr → Eval (State × World) Value} (h : SimRun run run') (E : Name) (c : Bool)
    {hv : Value} (hhv : hv.Safe) {m : Eval Copy.State Value} {m' : Eval (State × World) Value}
    (hm : Sim Value.Safe m m') :
    Sim Value.Safe
      (Eval.handleWith Copy.memory E c hv (fun f v => Eval.callAs D Copy.memory run c f [.value v]) m)
      (Eval.handleWith InPlace.memory E c hv
        (fun f v => Eval.callAs D InPlace.memory run' c f [.value v]) m') := by
  intro fr s hs
  refine Outcome.Rel.handleWith (R := Corr.relation Value.Safe s.1)
    (C := fun c c' => c = c' ∧ c.Safe)
    (fun _ _ _ _ _ _ h => h.1.symm) (fun n => ?_) ?_ (fun _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1.2⟩)
    (fun _ _ _ _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2.1.2⟩) (fun _ _ _ _ h => lifts h.2.2.1 h.2.2.2)
    (hm fr s hs)
  · unfold ClauseRel
    cases hcl : hv.clause? n
    · trivial
    · exact ⟨rfl, Value.Safe.clause hhv hcl⟩
  · rintro f _ op v fr₁ _ s₁ ⟨rfl, hf⟩ ⟨-, rfl, hvs, hag, hev⟩
    have hp : PassedSafe [.value v] := by
      intro q hq w hw
      simp only [List.mem_singleton] at hq
      subst hq
      cases hw
      exact hvs
    exact (callAs hD h c hf hp (List.pairwise_singleton _ _) fr₁ s₁ hag).evolve hs.1.valid hev

end Sim

end Stilt.InPlace
