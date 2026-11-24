import Stilt.Sharing.Steps
import Stilt.Handling.Related
import Stilt.InPlace.Handling

/-!
# Performances and handlers with sharing

A performance ends alike with copies and with sharing, and a `with` handles alike what its block
ends with: its clauses are calls of the same safe values on the same safe values, and what a
clause or the rest of the block ends with relates the frame and the state it ends with, wherever
the other runs left off (handlers.performing-operation and handlers.with). A call of a clause
passes one value and no place, so no root stops sharing when it starts.
-/

namespace Stilt.Sharing

namespace Sim

/-- A performance of a safe value (handlers.performing-operation). -/
theorem perform (shared : Name → Bool) {op : Operation} {v : Value} (hv : v.Safe) :
    Sim Value.Safe (Eval.perform Copy.memory op v) (Eval.perform (memory shared) op v) :=
  fun _ s hs => ⟨⟨rfl, rfl, hv, hs, Follows.refl s.1⟩, fun _ _ _ _ ⟨hw, hws, hx⟩ =>
    ⟨hw, hws, ⟨hs.1, hs.2.1, hx⟩, Follows.refl s.1⟩⟩

/-- What the two runs relate from `s` they relate at the frames of a state of each model that
agree and follow from `s`, in the worlds they relate. -/
theorem lifts (shared : Name → Bool) {s : State} {fr : Copy.State} {s₁ : State × World}
    (hag : AgreesIn fr s₁) (hev : Follows s s₁.1) :
    (Corr.relation Value.Safe s).Lifts Copy.memory (memory shared) fr s₁ :=
  ⟨fun _ _ _ _ h => ⟨h.1, h.2.1, ⟨hag.1, hag.2.1, h.2.2.1.2.2⟩, hev⟩,
    fun _ _ _ _ h => ⟨h.1, h.2.1, ⟨hag.1, hag.2.1, h.2.2.1.2.2⟩, hev⟩,
    fun _ _ _ _ h => ⟨h.1, h.2.1, ⟨hag.1, hag.2.1, h.2.2.1.2.2⟩, hev⟩,
    fun _ _ _ _ h => ⟨h.1, ⟨hag.1, hag.2.1, h.2.1.2.2⟩, hev⟩,
    fun _ _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1, ⟨hag.1, hag.2.1, h.2.2.2.1.2.2⟩, hev⟩⟩

/-- A `with` of a safe handler keeps the simulation (handlers.with), when calling a safe clause
on a safe value does. -/
theorem handleWith {D : Decls} (shared : Name → Bool) {run : Expr → Eval Copy.State Value}
    {run' : Expr → Eval (State × World) Value} (E : Name) (c : Bool)
    (hcall : ∀ f v, f.Safe → v.Safe → Sim Value.Safe (Eval.callAs D Copy.memory run c f [.value v])
      (Eval.callAs D (memory shared) run' c f [.value v]))
    {hv : Value} (hhv : hv.Safe) {m : Eval Copy.State Value} {m' : Eval (State × World) Value}
    (hm : Sim Value.Safe m m') :
    Sim Value.Safe
      (Eval.handleWith Copy.memory E c hv (fun f v => Eval.callAs D Copy.memory run c f [.value v]) m)
      (Eval.handleWith (memory shared) E c hv
        (fun f v => Eval.callAs D (memory shared) run' c f [.value v]) m') := by
  intro fr s hs
  refine Outcome.Rel.handleWith (R := Corr.relation Value.Safe s.1)
    (C := fun c c' => c = c' ∧ c.Safe)
    (fun _ _ _ _ _ _ h => h.1.symm) (fun n => ?_) ?_ (fun _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1.2.2⟩)
    (fun _ _ _ _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2.1.2.2⟩)
    (fun _ _ _ _ h => lifts shared h.2.2.1 h.2.2.2) (hm fr s hs)
  · unfold ClauseRel
    cases hcl : hv.clause? n
    · trivial
    · exact ⟨rfl, InPlace.Value.Safe.clause hhv hcl⟩
  · rintro f _ op v fr₁ _ s₁ ⟨rfl, hf⟩ ⟨-, rfl, hvs, hag, hev⟩
    exact (hcall f v hf hvs fr₁ s₁ hag).follow hev

end Sim

end Stilt.Sharing
