import Stilt.Parallel.Typed
import Stilt.Quiet.Theorem
import Stilt.Handling.Unseen

/-!
# A lazy value's function runs unseen

The calculus computes a lazy value at each `get`, as a call of the function it keeps
(`TaskForm.lazyGet`), where the Reference computes it at the first `get` and keeps it for every
copy. The function's type has an empty row (`Decls.IsLazy`), and that is what makes the two
alike to the code around a `get`: a call of a function value of such a type, from a typed state,
runs the same from whatever frames it is called from, and gives them back (`call_unseen`); it
ends as no performance (`call_settled`) and as no raise, since its row allows none; and it keeps
the world's output, standard error and input (`call_keeps`). So what the code around a `get`
sees of the run is its value, or its panic.
-/

namespace Stilt

variable {D : Decls}

/-- Invoking a body on values alone from any frame: one outcome, with the frame put back. -/
theorem invoke_unseen_values (captured : List (Name × Value)) (params : List Param)
    (vs : List Value) (body : Eval Copy.State Value) (w : World) :
    ∃ o : Outcome Copy.State Value, ∀ fr : Copy.Frame,
      Eval.invoke Copy.memory captured params (vs.map .value) body (fr, w) = o.atFrame fr := by
  unfold Eval.invoke
  cases hb : bindArgs params (vs.map .value) with
  | none => exact ⟨.stuck, fun _ => rfl⟩
  | some bound =>
    have hv : AllValues bound := bindArgs_values hb
    simp only [Copy.memory, Frames.withWorld, Copy.frames]
    cases he : Copy.enter [] captured bound with
    | error f =>
      refine ⟨Outcome.fault f ([], w), fun fr => ?_⟩
      rw [Copy.enter_allValues (fr' := []) hv, he]
      cases f <;> rfl
    | ok callee =>
      refine ⟨body (callee, w), fun fr => ?_⟩
      rw [Copy.enter_allValues (fr' := []) hv, he]
      exact Outcome.leaveCall_allValues hv fr w _

/-- A call of a function value on values alone, from any frames, is one outcome with those frames
given back, whatever they hold: the callee reads nothing of its caller's frames. -/
theorem call_unseen (run : Expr → Eval Copy.State Value) (f : Value) (vs : List Value)
    (w : World) : ∃ o : Outcome Copy.State Value, ∀ fr : Copy.Frame,
      Eval.call D Copy.memory run f (vs.map .value) (fr, w) = o.atFrame fr := by
  unfold Eval.call
  split
  · exact invoke_unseen_values _ _ vs _ w
  · rename_i name types rows
    cases D.fn? name with
    | none => exact ⟨.stuck, fun _ => rfl⟩
    | some d => exact invoke_unseen_values [] d.params vs _ w
  · exact ⟨.stuck, fun _ => rfl⟩

/-- polymorphism.lazy-unobservable, as the calculus states it: a lazy value's function has a type
that takes nothing and whose row is empty (polymorphism.lazy-values), and a call of a function
value of such a type, from a typed state, is one outcome from whatever frames it is called from,
with those frames given back; it ends as no performance and as no raise; and it keeps the world's
output, standard error and input. So no code around a `get` can tell when the function ran, and
a run of it writes and reads nothing, which is how the calculus, which runs it at each `get`,
agrees with one run kept for every copy. The model states less than the paragraph: that two runs
give one value, the result that copies share, is left out, since a run may make a shared value,
a new cell at each `get` in the calculus, which only a `when` could tell apart, and the export
declines a program with a lazy value and a `when`. -/
theorem lazy_unobservable (hD : D.Typed) (n : Nat) {Γ : Ctx} {η : REnv} {f : Value} {τ : Ty}
    {γ : Copy.State} (hf : Value.Typed D f ((Ty.fn [] τ Row.pure).close η))
    (hγ : State.Typed D γ Γ η) :
    (∃ o : Outcome Copy.State Value, ∀ fr : Copy.Frame,
      Eval.call D Copy.memory (eval D Copy.memory n) f [] (fr, γ.2) = o.atFrame fr) ∧
    (Eval.call D Copy.memory (eval D Copy.memory n) f [] γ).Settled ∧
    (∀ e s, Eval.call D Copy.memory (eval D Copy.memory n) f [] γ ≠ .raised e s) ∧
    (Eval.call D Copy.memory (eval D Copy.memory n) f [] γ).KeepsIo D
      ⟨Row.pure.close η, fun _ => False, performsOf D (Row.pure.close η)⟩ γ.2.io := by
  refine ⟨call_unseen _ f [] γ.2,
    call_settled hD n (fun _ h => by simp [Row.pure_close] at h) hf .nil hγ, fun e s h => ?_,
    call_keeps (hD.quiet n) hD hf .nil (by simp [Row.pure_close]) γ hγ⟩
  have hok := call_ok (hD.sound n) hD hf .nil γ hγ
  rw [h] at hok
  obtain ⟨⟨F, hF, -⟩, -⟩ := hok
  simp [Row.pure_close] at hF

end Stilt
