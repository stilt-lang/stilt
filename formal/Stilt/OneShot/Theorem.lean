import Stilt.OneShot.Calls
import Stilt.OneShot.Holding

/-!
# Resuming at most once

**One-shot handlers** (handlers.resume-at-most-once): in a program whose bodies
all pass the check, code that may resume at most once performs at most the
`resume`s its text counts on each path, with every fuel, in copy-in, copy-out
whatever its order of write-back. So the body of an operation of a handler that
takes control performs at most one `resume` on each path, and `runBody` runs
the rest of the `with`'s block at most once on each (`Outcome.OneShot.runBody`):
no continuation is resumed twice. A body that never resumes ends the `with`,
and `main` performs none.

The proof goes by induction on the fuel, case by case on the expression: every
value a run makes is one-shot, so a call runs a checked body; a call as code of
a body that may resume is stuck (handlers.resume-outside-operation), and a
`with`'s block performs its own `resume`s through it, since its effect is
another.
-/

namespace Stilt

open Eval.OneShot in
/-- Evaluating checked code that may resume at most once, with any fuel. -/
theorem eval_oneShot {D : Decls} (hD : ∀ d ∈ D.fns, d.body.bodyOneShot d.row = true) (w : WriteBack) :
    ∀ n, OneShotRun (eval D (Copy.memoryWith w) n)
  | 0, _, _, _ => outOfFuel
  | n + 1, e, he, hn => by
    have ih := eval_oneShot hD w n
    have ap : ∀ {a b : Nat} {e : Expr}, e.oneShot = true → e.resumes = a → a ≤ b → b ≤ 1 →
        Eval.OneShot b Value.OneShot (eval D (Copy.memoryWith w) n e) := fun h₁ h₂ h₃ h₄ =>
      (ih _ h₁ (by omega)).mono (by omega) fun _ h => h
    cases e <;> (try simp only [Expr.oneShot, Bool.and_eq_true, decide_eq_true_eq] at he) <;>
      (try simp only [Expr.resumes] at hn ⊢)
    case var x => exact read w x
    case move x => exact read w x
    case int k => exact pure .int
    case bool b => exact pure .bool
    case unit => exact pure .unit
    case record R _ fs => exact bindLe (b := 0) (fields ih fs he hn) (fun _ hw => declare D R hw) (by omega)
    case variant T _ C es => exact bindLe (b := 0) (list ih es he hn) (fun _ hvs => pure (.variant hvs)) (by omega)
    case list τ es => exact bindLe (b := 0) (list ih es he hn) (fun _ hvs => pure (.list hvs)) (by omega)
    case op o es =>
      exact bindLe (b := 0) (list ih es he hn) (fun _ hvs => world w _ fun _ _ _ hx h =>
        ⟨Op.run_hereditary Value.OneShot.hereditary .unit hvs h, hx.run hvs h⟩) (by omega)
    case view es =>
      exact bindLe (b := 0) (list ih es he hn) (fun _ hvs => ofExcept fun _ h =>
        Op.apply_hereditary Value.OneShot.hereditary hvs h) (by omega)
    case field e f =>
      exact bindLe (b := 0) (ih e he hn) (fun _ hv => ofExcept fun _ h => hv.get h) (by omega)
    case index e i =>
      exact bindLe (ih e he.1 (by omega)) (fun _ hv => bindLe (b := 0) (bindLe (b := 0)
        (ih i he.2 (by omega)) (fun _ _ => asInt) (Nat.le_refl _))
        (fun _ _ => ofExcept fun _ h => hv.get h) (Nat.le_refl _)) (by omega)
    case fnRef f types rows => exact pure .function
    case method t m τ =>
      show Eval.OneShot 0 Value.OneShot (Eval.method D t m τ)
      unfold Eval.method
      split
      · split
        · exact pure .function
        · exact stuck
      · exact stuck
    case closure ps result ρ body =>
      exact bindLe (b := 0) (capture w _) (fun _ hc =>
        pure (.closure (by simp [Expr.bodyOneShot, he.1, he.2]) hc)) (Nat.le_refl _)
    case call callee as _ =>
      exact bindLe (ih callee he.1 (by omega)) (fun _ hf => bindLe (args ih as he.2 (by omega))
        (fun _ hp => callAs w hD ih false hf hp) (Nat.le_refl _)) (by simp)
    case letIn x τ init body =>
      exact bindLe (ih init he.1 (by omega)) (fun _ hv => withInit w hv (ih body he.2 (by omega)))
        (Nat.le_refl _)
    case varIn x τ init body =>
      exact bindLe (ih init he.1 (by omega)) (fun _ hv => withInit w hv (ih body he.2 (by omega)))
        (Nat.le_refl _)
    case assign p value =>
      obtain ⟨x, ps⟩ := p
      simp only [Expr.oneShot, Bool.and_eq_true] at he
      simp only [Expr.resumes] at hn ⊢
      exact assign ih w x he.1 he.2 hn
    case seq a b =>
      exact bindLe (ih a he.1 (by omega)) (fun _ _ => ih b he.2 (by omega)) (Nat.le_refl _)
    case «if» c τ a b =>
      exact bindLe (bindLe (b := 0) (ih c he.1.1 (by omega)) (fun _ _ => asBool) (Nat.le_refl _))
        (fun g _ => ite g (ap he.1.2 rfl (Nat.le_max_left _ _) (by omega))
          (ap he.2 rfl (Nat.le_max_right _ _) (by omega))) (Nat.le_refl _)
    case «match» e τ arms =>
      exact bindLe (ih e he.1 (by omega)) (fun _ hv => select ih w he.2 (by omega) hv) (Nat.le_refl _)
    case «for» x τ e body =>
      have hb0 := loopResumes_le (n := body.resumes) (by omega)
      rw [hb0, show loopResumes 0 = 0 from rfl, Nat.add_zero] at hn ⊢
      exact loop ih w x he.1 he.2 hn hb0
    case raise e => exact bindLe (b := 0) (ih e he hn) (fun _ hv => throw hv) (by omega)
    case «try» e => exact ih e he hn
    case form _ e => exact ih e he hn
    case tryCatch e E x h τ => exact handle (ih e he.1 (by omega)) fun _ hv => withVar w hv (ih h he.2 (by omega))
    case «while» c body =>
      have h0 := loopResumes_le (n := c.resumes + body.resumes) hn
      have hl := ih (.while c body) (by simp [Expr.oneShot, he.1, he.2]) (by simp [Expr.resumes, h0, loopResumes])
      simp only [Expr.resumes, h0] at hl
      exact bindLe (bindLe (b := 0) (ap he.1 (by omega) (Nat.le_refl 0) (by omega))
        (fun _ _ => asBool) (Nat.le_refl _)) (fun g _ => ite g (bindLe (b := 0)
          (turn (ap he.2 (by omega) (Nat.le_refl 0) (by omega))) (fun g' _ => ite g' hl (pure .unit))
          (Nat.le_refl _)) (pure .unit)) (by simp [h0, loopResumes])
    case «loop» body =>
      have h0 := loopResumes_le (n := body.resumes) hn
      have hl := ih (.loop body) (by simp [Expr.oneShot, he]) (by simp [Expr.resumes, h0, loopResumes])
      simp only [Expr.resumes, h0] at hl
      exact bindLe (b := 0) (turn (ap he h0 (Nat.le_refl 0) (by omega)))
        (fun g _ => ite g hl (pure .unit)) (by simp [h0, loopResumes])
    case «break» => exact jump trivial
    case «continue» => exact jump trivial
    case «return» e => exact bindLe (b := 0) (ih e he hn) (fun _ hv => jump hv) (by omega)
    case perform op e => exact bindLe (ih e he (by omega)) (fun _ hv => perform w hv) (Nat.le_refl _)
    case withH E c h b =>
      exact bindLe (ih h he.1.2 (by omega)) (fun _ hh s hs => Outcome.OneShot.letGo w _ <|
        Outcome.OneShot.handleWith w he.1.1 hh (fun _ v s' hc hv hs' =>
          callAs w hD ih c hc (passed := [.value v]) (fun q hq => by
            simp only [List.mem_singleton] at hq; subst hq; exact hv) s' hs')
          (ih b he.2 (by omega) s hs)) (Nat.le_refl _)
    case held ns hs b =>
      exact bindLe (list ih hs he.1 (by omega)) (fun vs _ => held w (ih b he.2 (by omega)) _ vs)
        (Nat.le_refl _)

/-- **One-shot handlers**: in a checked program, the body of an operation of a
handler that takes control, as a `with` calls it on any one-shot value, from
any one-shot frame in any world whose cells hold one-shot values, performs at most one `resume` on each path, so it runs the
rest of the block at most once (handlers.resume-at-most-once). -/
theorem Program.OneShot.clause {p : Program} (hp : p.OneShot) (w : WriteBack) (fuel : Nat)
    {c v : Value} (hc : c.OneShot) (hv : v.OneShot) {s : Copy.State} (hs : State.OneShot s) :
    (Eval.callAs p.decls (Copy.memoryWith w) (eval p.decls (Copy.memoryWith w) fuel) true c [.value v]
      s).OneShot Value.OneShot 1 :=
  Eval.OneShot.callAs w hp.1 (eval_oneShot hp.1 w fuel) true hc (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact hv) s hs

/-- A checked program's `main` performs no `resume` on any path: none outside
a handler's operation (handlers.resume-outside-operation). -/
theorem Program.OneShot.main {p : Program} (hp : p.OneShot) (w : WriteBack) (fuel : Nat) :
    (eval p.decls (Copy.memoryWith w) fuel p.main ([], {})).OneShot Value.OneShot 0 := by
  have h := eval_oneShot hp.1 w fuel p.main hp.2.1 (by rw [hp.2.2]; omega) ([], {}) ⟨(fun _ h => nomatch h), fun _ h => nomatch h⟩
  rwa [hp.2.2] at h

end Stilt
