import Stilt.Ends.Theorem
import Stilt.Optimality.Eval

/-!
# Descent is needed

`Decls.Ranked.call` fails without the check of facts.descending-self-calls and
facts.shrinking-recursion: `fn f(n: i64) -> i64 { f(n) }` passes its parameter whole, neither a
strict part of it nor a counter stepped toward a bound, so no ranking and no way of going
down accepts it (`unranked`), and a call of it runs out of every fuel (`call_diverges`).
-/

namespace Stilt.Counterexamples.Ends

/-- `f(n)`. -/
private def self : Expr := .call (.fnRef "f" [] []) [.value (.var "n")] .i64

/-- `fn f(n: i64) -> i64 { f(n) }`. -/
def decls : Decls :=
  ⟨[], [], [⟨"f", [], [], [⟨.let, "n", .i64, none⟩], .i64, Row.pure, self, {}⟩], [], [], [], [], []⟩

/-- No ranking, and no way for `f`'s self-calls to go down, makes `f` free of `div`. -/
theorem unranked (lim : Limited) (B : Name → Nat) (desc : Name → Descent) (H : Name → List Nat)
    (hf : lim.fn "f" = true) : ¬ decls.Ranked lim B desc H := by
  intro h
  have := h "f" _ rfl hf
  revert this
  cases desc "f" with
  | parts k =>
    cases k with
    | zero =>
      have hn := startRoles_ne_part (hs := H "f") (x := "n")
        (d := ⟨"f", [], [], [⟨.let, "n", .i64, none⟩], .i64, Row.pure, self, {}⟩) (spec := .parts 0)
        (by simp [FnDecl.entryRoles, FnDecl.letParam?, Roles.of, Expr.writes, argsWrites, self])
      simp only [self] at hn
      simp only [self, Expr.divFree, Expr.callable, Expr.isSelf, descends, Descent.calls]
      simp [argPart, Expr.roleIn, hn]
    | succ k => simp [self, Expr.divFree, Expr.callable, Expr.isSelf, descends, Descent.calls, argPart]
  | shrinks k g b => cases k <;> simp [self, Expr.divFree, Expr.callable, Expr.isSelf, descends,
      Descent.calls, argWith, Expr.shrinksIn]

theorem self_out (w : WriteBack) : ∀ (n : Nat) (fr : Copy.Frame) (x : World) (v : Value),
    fr.lookup "n" = some v → eval decls (Copy.memoryWith w) n self (fr, x) = .outOfFuel
  | 0, _, _, _, _ => rfl
  | 1, _, _, _, _ => rfl
  | m + 2, fr, x, v, hv => by
    have ih := self_out w (m + 1) [("n", v)] x v rfl
    have h₁ : eval decls (Copy.memoryWith w) (m + 1) (.fnRef "f" [] []) (fr, x) =
        .done (.function "f" [] []) (fr, x) := rfl
    have h₀ : eval decls (Copy.memoryWith w) (m + 1) (.var "n") (fr, x) = .done v (fr, x) := by
      show Eval.ofExcept (Copy.read fr "n" []) (fr, x) = _
      simp [Copy.read, hv, Value.get, Eval.ofExcept]
    have h₂ : Eval.args (eval decls (Copy.memoryWith w) (m + 1)) [.value (.var "n")] (fr, x) =
        .done [.value v] (fr, x) := by
      show (eval decls (Copy.memoryWith w) (m + 1) (.var "n") >>= fun v =>
        Eval.args (eval decls (Copy.memoryWith w) (m + 1)) [] >>= fun vs =>
          pure (Passed.ofArg (.var "n") v :: vs)) (fr, x) = _
      rw [Optimality.bind_done h₀]
      rfl
    show (eval decls (Copy.memoryWith w) (m + 1) (.fnRef "f" [] []) >>= fun f =>
      Eval.args (eval decls (Copy.memoryWith w) (m + 1)) [.value (.var "n")] >>= fun passed =>
        Eval.callAs decls (Copy.memoryWith w) (eval decls (Copy.memoryWith w) (m + 1)) false f passed)
        (fr, x) = _
    rw [Optimality.bind_done h₁, Optimality.bind_done h₂]
    show (eval decls (Copy.memoryWith w) (m + 1) self ([("n", v)], x)).leaveCall
      (Copy.memoryWith w) [("n", .value v)] (fr, x) = _
    rw [ih]
    rfl

/-- A call of `f` runs out of every fuel, whatever it is passed and whatever the order of
write-back. -/
theorem call_diverges (w : WriteBack) (n : Nat) (v : Value) (s : Copy.State) :
    Eval.call decls (Copy.memoryWith w) (eval decls (Copy.memoryWith w) n) (.function "f" [] [])
      [.value v] s = .outOfFuel := by
  show (eval decls (Copy.memoryWith w) n self ([("n", v)], s.2)).leaveCall
    (Copy.memoryWith w) [("n", .value v)] s = _
  rw [self_out w n [("n", v)] s.2 v rfl]
  rfl

/-- `DescentNeeded`: some declarations that no ranking accepts have a call that never ends,
so `Decls.Ranked.call` needs the check. -/
theorem descent_needed : ∃ D : Decls, (∀ B desc H, ¬ D.Ranked Limited.all B desc H) ∧
    ∀ w n v s, Eval.call D (Copy.memoryWith w) (eval D (Copy.memoryWith w) n) (.function "f" [] [])
      [.value v] s = .outOfFuel :=
  ⟨decls, fun B desc H => unranked _ B desc H rfl, call_diverges⟩

end Stilt.Counterexamples.Ends
