import Stilt.Div.Terminates

/-!
# Descent is needed

`descentTerminates` fails without the check of facts.descending-self-calls: `f(x) = f(x)`
passes its whole parameter, not a strict part, so the check rejects it, and a
call of it runs out of every fuel.
-/

namespace Stilt.Div

/-- `fn f(x) { f(x) }`. -/
def selfCall : Prog := [{ arity := 1, desc := 0, body := .call 0 (.cons (.var 0) .nil) }]

/-- The check rejects `selfCall`: its self-call passes the whole parameter. -/
theorem selfCall_unchecked : ¬ Checked selfCall := by
  intro h
  have := h 0 (by decide)
  simp [selfCall, ok, okArgs, argPart, roleOf, roles] at this

/-- A call of `selfCall`'s function never ends. -/
theorem selfCall_diverges : ∀ n, evalCall selfCall n 0 [.leaf] = none := by
  have body : ∀ n, eval selfCall n [.leaf] (.call 0 (.cons (.var 0) .nil)) = none := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        cases n with
        | zero => rfl
        | succ m =>
            cases m with
            | zero => rfl
            | succ j =>
                have hargs : evalArgs selfCall (j + 2) [.leaf] (.cons (.var 0) .nil) = some [.leaf] := by
                  simp [evalArgs, eval]
                simp only [eval, hargs, Option.bind_eq_bind, Option.bind_some]
                simpa [selfCall] using ih
  intro n
  simpa [evalCall, selfCall] using body n

/-- `DescentNeeded`: some program that fails the check has a call that never
ends, so the theorem needs the check. -/
theorem descent_needed : ∃ P : Prog, ¬ Checked P ∧ ∀ n, evalCall P n 0 [.leaf] = none :=
  ⟨selfCall, selfCall_unchecked, selfCall_diverges⟩

end Stilt.Div
