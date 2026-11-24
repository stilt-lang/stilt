import Stilt.Moves.Forms
import Stilt.Handling.Related

/-!
# Performances and handlers

A performance ends alike in copy-in, copy-out and `Moving`, and a `with`
handles alike what its block ends with: a clause is a call of the same closure
on the same value, from a performance whose states agree under the mask they
reached, and what a clause or the rest of the block ends with
relates the frame and the state it ends with, wherever the other runs left off
(handlers.performing-operation and handlers.with). A clause's argument is a
value, so the call passes no place and no last use.
-/

namespace Stilt.Moving

open InPlace

/-- A handler's clause, a field of a record that a run may hold, may be held too. -/
theorem VOk.clause {hv c : Value} {n : Name} (hhv : VOk hv) (h : hv.clause? n = some c) :
    VOk c := by
  cases hv <;> simp only [Value.clause?, reduceCtorEq] at h
  obtain ⟨hs, hj⟩ := hhv
  cases hs with
  | record hf =>
    cases hj with
    | record hg => exact ⟨hf _ (mem_of_lookup h), hg _ (mem_of_lookup h)⟩

/-- A call passing one value that a run may hold needs nothing more of its caller. -/
theorem readyP_value {L X : Live} {m : List Bool} {fr : Copy.State} {s : State × World}
    {v : Value} (hag : MAgreesIn m fr s) (hv : VOk v) : ReadyP L X m fr s [.value v] where
  agrees := hag
  places _ _ h := by simp at h
  moved _ _ h := by simp at h
  compat := List.pairwise_singleton _ _
  nodup := List.nodup_nil
  passed q hq w hw := by
    simp only [List.mem_singleton] at hq
    subst hq
    cases hw
    exact hv

namespace MSim

variable {Lb L X : Live}

/-- A performance of a value that a run may hold (handlers.performing-operation). -/
theorem perform {op : Operation} {v : Value} (hv : VOk v) :
    MSim VOk Lb L X (Eval.perform Copy.memory op v) (Eval.perform Moving.memory op v) :=
  fun fr s _ hag _ => ⟨⟨rfl, rfl, hv, Post.refl hag⟩, fun _ _ _ x' ⟨hw, hwok, hx⟩ =>
    ⟨hw, hwok, Post.refl (fr := (fr.1, _)) (s := (s.1, x')) ⟨hag.1, hx⟩⟩⟩

/-- A `with` of a handler that a run may hold keeps the simulation (handlers.with). -/
theorem handleWith {D : Decls} (hD : DeclsOk D) {run : Expr → Eval Copy.State Value}
    {run' : Expr → Eval (State × World) Value} (h : MRun run run') (E : Name) (c : Bool)
    {hv : Value}
    (hhv : VOk hv) {m : Eval Copy.State Value} {m' : Eval (State × World) Value}
    (hm : MSim VOk Lb L X m m') :
    MSim VOk Lb L X
      (Eval.handleWith Copy.memory E c hv
        (fun f v => Eval.callAs D Copy.memory run c f [.value v]) m)
      (Eval.handleWith Moving.memory E c hv
        (fun f v => Eval.callAs D Moving.memory run' c f [.value v]) m') := by
  intro fr s mk hag hinv
  refine Outcome.Rel.handleWith (R := MCorr.relation VOk L X mk s.1)
    (C := fun c c' => c = c' ∧ VOk c) (fun _ _ _ _ _ _ h => h.1.symm) (fun n => ?_) ?_
    (fun _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.world, h.2.2.safe⟩)
    (fun _ _ _ _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2.world, h.2.2.2.safe⟩) ?_ (hm fr s mk hag hinv)
  · unfold ClauseRel
    cases hcl : hv.clause? n
    · trivial
    · exact ⟨rfl, VOk.clause hhv hcl⟩
  · rintro f _ op v fr₁ _ s₁ ⟨rfl, hf⟩ ⟨-, rfl, hvok, m₁, hag₁, hk, henv, hev⟩
    exact (callAs_step hD h c hf (readyP_value hag₁ hvok)).prefix hag.1 hk henv hev
      (Live.Sub.refl L)
  · rintro _ fr₁ _ s₁ ⟨-, -, hp⟩
    exact ⟨fun _ _ _ _ h => ⟨h.1, h.2.1, hp.reworld h.2.2.world h.2.2.safe⟩,
      fun _ _ _ _ h => ⟨h.1, h.2.1, hp.reworld h.2.2.world h.2.2.safe⟩,
      fun _ _ _ _ h => ⟨h.1, h.2.1, hp.reworld h.2.2.world h.2.2.safe⟩,
      fun _ _ _ _ h => ⟨h.1, hp.reworld h.2.world h.2.safe⟩,
      fun _ _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1, hp.reworld h.2.2.2.world h.2.2.2.safe⟩⟩

end MSim

end Stilt.Moving
