import Stilt.Panics.Runs

/-!
# Calls without panics

A call of a panic-free function value, with panic-free arguments, ends as
panic-free code may: entering it binds panic-free values, its body is
panic-free, a closure's by the value and a declared function's by the
program, and leaving it writes them back along fields.
-/

namespace Stilt

namespace Eval.PanicFree

variable (w : WriteBack) {G : List Known} {lim : Limited}

/-- Leaving a call, from a panic-free frame, writes back along fields to a
panic-free frame. -/
theorem leave_calm {s s' : Copy.Frame} {bound : List (Name × Passed)} (hs : Frame.PanicFree lim s)
    (hs' : Frame.PanicFree lim s') (hbound : ∀ ya ∈ bound, ya.2.PanicFree lim) :
    CalmTo (Frame.PanicFree lim) (Copy.leave s s' (w.order bound)) :=
  Frame.PanicFree.leave hs' (w.order bound) hs fun ya hya => hbound ya ((w.perm bound).mem_iff.1 hya)

/-- Ends a call through `leave_calm`. -/
macro "leaving" w:term:max hs:term:max hbody:term:max hbound:term:max : tactic =>
  `(tactic| (
    have hl := leave_calm $w $hs ($hbody).2.1 $hbound
    simp only [Outcome.leaveCall, Eval.Keeps.memoryWith_leave]
    cases hle : Copy.leave _ _ _ with
    | ok fr => exact ⟨($hbody).1, hl.2 fr hle, ($hbody).2.2⟩
    | error f => rw [hle] at hl; exact fault hl.1 ⟨$hs, ($hbody).2.2⟩))

/-- A callee's panic-free outcome, the call left from a panic-free frame, a
performance's rest included. -/
theorem leaveCall {s : Copy.State} (hs : Frame.PanicFree lim s.1) {bound : List (Name × Passed)}
    (hbound : ∀ ya ∈ bound, ya.2.PanicFree lim) :
    ∀ {o : Outcome Copy.State Value}, o.PanicFree lim (Value.PanicFree lim) →
      (o.leaveCall (Copy.memoryWith w) bound s).PanicFree lim (Value.PanicFree lim)
  | .done _ _, h => by leaving w hs h hbound
  | .raised _ _, h => by leaving w hs h hbound
  | .jumped (.ret _) _, h => by leaving w hs h hbound
  | .jumped .brk _, _ | .jumped .cont _, _ => trivial
  | .panicked _ _, h => by leaving w hs h hbound
  | .performed _ _ s' _, ⟨hv, hs', hk⟩ => by
    have hl := leave_calm w hs hs'.1 hbound
    simp only [Outcome.leaveCall, Eval.Keeps.memoryWith_leave]
    cases hle : Copy.leave s.1 s'.1 (w.order bound) with
    | ok fr => exact ⟨hv, ⟨hl.2 fr hle, hs'.2⟩, fun u x hu hx => leaveCall hs hbound (hk u x hu hx)⟩
    | error f => rw [hle] at hl; exact fault hl.1 ⟨hs, hs'.2⟩
  | .outOfFuel, _ | .stuck, _ => trivial

/-- A call of a function value whose body is panic-free. -/
theorem invoke {captured : List (Name × Value)} (hc : ∀ xv ∈ captured, xv.2.PanicFree lim)
    {params : List Param} {passed : List Passed} (hp : ∀ q ∈ passed, q.PanicFree lim)
    {body : Eval Copy.State Value} (hb : Eval.PanicFree lim [] (Value.PanicFree lim) body) :
    Eval.PanicFree lim G (Value.PanicFree lim) (Eval.invoke (Copy.memoryWith w) captured params passed body) := by
  intro s hs _
  unfold Eval.invoke
  cases hbind : bindArgs params passed with
  | none => trivial
  | some bound =>
    have hsnd := (InPlace.bindArgs_spec hbind).2
    have hbound : ∀ ya ∈ bound, ya.2.PanicFree lim := fun ya hya =>
      hp _ (hsnd ▸ List.mem_map_of_mem hya)
    have hent : CalmTo (Frame.PanicFree lim) (Copy.enter s.1 captured bound) :=
      Frame.PanicFree.enter hs.1 bound hc hbound
    dsimp only
    rw [Eval.Keeps.memoryWith_enter]
    cases he : Copy.enter s.1 captured bound with
    | error f => rw [he] at hent; exact fault hent.1 hs
    | ok callee =>
      exact leaveCall w hs.1 hbound (hb (callee, s.2) ⟨hent.2 callee he, hs.2⟩ (Frame.Meets.nil _))

/-- A call of a panic-free function value: a closure whose body is panic-free, or a function
that `lim` covers, whose body is. -/
theorem call {D : Decls} (hD : D.PanicCover lim)
    {run : Expr → Eval Copy.State Value} (h : PanicFreeRun lim run) {f : Value} (hf : f.PanicFree lim)
    {passed : List Passed} (hp : ∀ q ∈ passed, q.PanicFree lim) :
    Eval.PanicFree lim G (Value.PanicFree lim) (Eval.call D (Copy.memoryWith w) run f passed) := by
  cases f with
  | closure captured params result ρ body =>
    cases hf with
    | closure hb hc => exact invoke w hc hp (h [] body hb)
  | function name types rows =>
    unfold Eval.call
    dsimp only
    cases hd : D.fn? name with
    | none => exact stuck
    | some d =>
      refine invoke w (captured := []) (by simp) hp (h [] _ ?_)
      rw [Expr.panicFree_substRows, Expr.panicFree_substTys]
      have hname : d.name = name := by simpa using List.find?_some hd
      cases hf with
      | function hl => exact hD.fns d (List.mem_of_find?_eq_some hd) (hname ▸ hl)
  | _ => exact stuck

/-- A call as code or a `with` makes it. -/
theorem callAs {D : Decls} (hD : D.PanicCover lim)
    {run : Expr → Eval Copy.State Value} (h : PanicFreeRun lim run) (control : Bool) {f : Value}
    (hf : f.PanicFree lim) {passed : List Passed} (hp : ∀ q ∈ passed, q.PanicFree lim) :
    Eval.PanicFree lim G (Value.PanicFree lim) (Eval.callAs D (Copy.memoryWith w) run control f passed) := by
  unfold Eval.callAs
  split
  · exact stuck
  · exact call w hD h hf hp

end Eval.PanicFree

end Stilt
