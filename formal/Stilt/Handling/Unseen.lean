import Stilt.Parallel

/-!
# A handler's body sees no place of the calls it ends

A handler's clause is called on its operation's argument, a value, from the state the
performance left, in which every call between the performance and the `with` has written its
`inout` arguments back (handlers.call-that-handler-ends). The clause's body runs in a frame of
its own, of its captures, which are copies, and its parameter: a call that passes only values
reads nothing of its caller's frames, and leaves them as they were. So whatever frames the
clause is called from, it runs the same, and gives them back (`callAs_unseen`): whether a
place of an ended call is written back before or after the body runs can't be observed, and
the first code that sees it runs after the `with` (handlers.when-place-is-seen).
-/

namespace Stilt

/-- An outcome of a call that passes only values, from the caller's frame `fr`: the callee's
outcome with `fr` put back, a `return` the call's value. -/
def Outcome.atFrame (fr : Copy.Frame) : Outcome Copy.State Value → Outcome Copy.State Value
  | .done v s => .done v (fr, s.2)
  | .raised e s => .raised e (fr, s.2)
  | .jumped (.ret v) s => .done v (fr, s.2)
  | .jumped _ _ => .stuck
  | .panicked k s => .panicked k (fr, s.2)
  | .performed op v s k => .performed op v (fr, s.2) fun w x => (k w x).atFrame fr
  | .outOfFuel => .outOfFuel
  | .stuck => .stuck

theorem Copy.enter_allValues {fr fr' : Copy.Frame} {captured : Copy.Frame} :
    ∀ {bound : List (Name × Passed)}, AllValues bound →
      Copy.enter fr captured bound = Copy.enter fr' captured bound := by
  intro bound h
  unfold Copy.enter
  suffices ∀ (acc : Copy.Frame) (bound : List (Name × Passed)), AllValues bound →
      bound.foldlM (init := acc) (fun fr₀ (y, a) => match a with
        | .value v | .moved _ v => pure ((y, v) :: fr₀)
        | .place x path => (fun v => (y, v) :: fr₀) <$> Copy.read fr x path) =
      bound.foldlM (init := acc) (fun fr₀ (y, a) => match a with
        | .value v | .moved _ v => pure ((y, v) :: fr₀)
        | .place x path => (fun v => (y, v) :: fr₀) <$> Copy.read fr' x path) from this _ _ h
  intro acc bound h
  induction bound generalizing acc with
  | nil => rfl
  | cons p bound ih =>
    obtain ⟨y, a⟩ := p
    have hrest : AllValues bound := fun q hq => h q (List.mem_cons_of_mem _ hq)
    obtain ⟨v, hv⟩ := h (y, a) List.mem_cons_self
    simp only at hv
    subst hv
    exact ih _ hrest

/-- A call's end, when it passes only values, puts the caller's frame back. -/
theorem Outcome.leaveCall_allValues {bound : List (Name × Passed)} (h : AllValues bound)
    (fr : Copy.Frame) (w : World) :
    ∀ o : Outcome Copy.State Value, o.leaveCall Copy.memory bound (fr, w) = o.atFrame fr := by
  have hl : ∀ s : Copy.State, Copy.memory.leave (fr, w) s bound = .ok (fr, s.2) := fun s => by
    show (fun x => (x, s.2)) <$> Copy.leave fr s.1 bound = _
    rw [Copy.leave_values h]
    rfl
  intro o
  induction o with
  | done v s => simp only [Outcome.leaveCall, hl, Outcome.atFrame]
  | raised e s => simp only [Outcome.leaveCall, hl, Outcome.atFrame]
  | jumped j s =>
    cases j with
    | ret v => simp only [Outcome.leaveCall, hl, Outcome.atFrame]
    | brk | cont => rfl
  | panicked k s => simp only [Outcome.leaveCall, hl, Outcome.atFrame]
  | performed op v s k ih =>
    simp only [Outcome.leaveCall, hl, Outcome.atFrame]
    congr 1
    funext w' x
    exact ih w' x
  | outOfFuel | stuck => rfl

/-- Invoking a body on a value from any frame: one outcome, with the frame put back. -/
theorem invoke_unseen (captured : List (Name × Value)) (params : List Param) (v : Value)
    (body : Eval Copy.State Value) (w : World) :
    ∃ o : Outcome Copy.State Value, ∀ fr : Copy.Frame,
      Eval.invoke Copy.memory captured params [.value v] body (fr, w) = o.atFrame fr := by
  unfold Eval.invoke
  cases hb : bindArgs params [.value v] with
  | none => exact ⟨.stuck, fun _ => rfl⟩
  | some bound =>
    have hv : AllValues bound := bindArgs_values (vs := [v]) hb
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

/-- **A handler's body sees no place of the calls it ends** (handlers.when-place-is-seen): a
call of a function value on one value, as a `with` calls a clause, from any frames, is one
outcome with those frames given back, whatever they hold. -/
theorem callAs_unseen (D : Decls) (run : Expr → Eval Copy.State Value) (control : Bool)
    (f v : Value) (w : World) :
    ∃ o : Outcome Copy.State Value, ∀ fr : Copy.Frame,
      Eval.callAs D Copy.memory run control f [.value v] (fr, w) = o.atFrame fr := by
  unfold Eval.callAs
  split
  · exact ⟨.stuck, fun _ => rfl⟩
  · unfold Eval.call
    split
    · exact invoke_unseen _ _ v _ w
    · rename_i name types rows _
      cases hd : D.fn? name with
      | none => exact ⟨.stuck, fun _ => rfl⟩
      | some d =>
        obtain ⟨o, ho⟩ := invoke_unseen [] d.params v
          (run ((d.body.substTys (d.typeArgs types)).substRows (d.rowParams.zip rows))) w
        exact ⟨o, ho⟩
    · exact ⟨.stuck, fun _ => rfl⟩

end Stilt
