import Stilt.OneShot.Runs
import Stilt.InPlace.Enter

/-!
# Calls that resume at most once

A call of a one-shot function value, with one-shot arguments, performs what its
body does: entering it binds one-shot values, its body passes the check, a
closure's by the value and a declared function's by the program, and leaving
it writes one-shot values back. A body may resume once only when its row holds
`resume`, and only a `with` that takes control calls such a body: a call as
code of one is stuck (handlers.resume-outside-operation). So a call as code
performs no `resume`, and a `with`'s call at most one.
-/

namespace Stilt

namespace Eval.OneShot

variable (w : WriteBack)

/-- A call of a function value whose body performs at most `k` `resume`s. -/
theorem invoke {captured : List (Name × Value)} (hc : ∀ xv ∈ captured, xv.2.OneShot)
    {params : List Param} {passed : List Passed} (hp : ∀ q ∈ passed, q.OneShot)
    {body : Eval Copy.State Value} {k : Nat} (hb : Eval.OneShot k Value.OneShot body) :
    Eval.OneShot k Value.OneShot (Eval.invoke (Copy.memoryWith w) captured params passed body) := by
  intro s hs
  unfold Eval.invoke
  cases hbind : bindArgs params passed with
  | none => trivial
  | some bound =>
    have hsnd := (InPlace.bindArgs_spec hbind).2
    have hbound : ∀ ya ∈ bound, ya.2.OneShot := fun ya hya => hp _ (hsnd ▸ List.mem_map_of_mem hya)
    dsimp only
    cases he : (Copy.memoryWith w).enter s captured bound with
    | error f => exact Outcome.OneShot.fault hs
    | ok callee =>
      obtain ⟨fr, hfr, rfl⟩ := Frames.withWorld_enter_ok _ he
      exact Outcome.OneShot.leaveCall w hs (hb _ ⟨Frame.OneShot.enter hs.1 bound hc hbound hfr, hs.2⟩)

/-- The count a body may reach when a call as code, or a `with` that takes
control, calls it. -/
theorem le_control {control : Bool} {ρ : Row} {k : Nat} (hk : k ≤ ρ.resumes)
    (hc : control = false → ρ.resume.isSome = false) : k ≤ if control then 1 else 0 := by
  unfold Row.resumes at hk
  cases control
  · simp only [hc rfl, Bool.false_eq_true, ↓reduceIte] at hk ⊢; exact hk
  · simp only [↓reduceIte]; split at hk <;> omega

/-- A call of a one-shot function value, in a program whose bodies pass the
check: none of `resume` as code, at most one by a `with` that takes control. -/
theorem callAs {D : Decls} (hD : ∀ d ∈ D.fns, d.body.bodyOneShot d.row = true)
    {run : Expr → Eval Copy.State Value} (h : OneShotRun run) (control : Bool) {f : Value}
    (hf : f.OneShot) {passed : List Passed} (hp : ∀ q ∈ passed, q.OneShot) :
    Eval.OneShot (if control then 1 else 0) Value.OneShot
      (Eval.callAs D (Copy.memoryWith w) run control f passed) := by
  unfold Eval.callAs
  by_cases hg : (!control && f.takesControl D) = true
  · rw [ite_eq_left hg]; exact stuck
  · rw [ite_eq_right hg]
    have hctl : control = false → f.takesControl D = false := fun hc => by
      subst hc; simpa using hg
    cases f with
    | closure captured params result ρ body =>
      cases hf with
      | closure hb hc =>
        simp only [Expr.bodyOneShot, Bool.and_eq_true, decide_eq_true_eq] at hb
        have hle := le_control hb.2 fun hc' => by simpa [Value.takesControl] using hctl hc'
        exact invoke w hc hp ((h body hb.1 (by split at hle <;> omega)).mono hle fun _ h => h)
    | function name types rows =>
      unfold Eval.call
      dsimp only
      cases hd : D.fn? name with
      | none => exact stuck
      | some d =>
        have hb := hD d (List.mem_of_find?_eq_some hd)
        simp only [Expr.bodyOneShot, Bool.and_eq_true, decide_eq_true_eq] at hb
        have hle := le_control hb.2 fun hc' => by
          simpa [Value.takesControl, hd] using hctl hc'
        refine invoke w (captured := []) (by simp) hp ((h _ ?_ ?_).mono (k := if control then 1 else 0)
          ?_ fun _ h => h) <;>
          simp only [Expr.oneShot_substRows, Expr.oneShot_substTys, Expr.resumes_substRows,
            Expr.resumes_substTys, hb.1]
        · split at hle <;> omega
        · exact hle
    | _ => exact stuck

end Eval.OneShot

end Stilt
