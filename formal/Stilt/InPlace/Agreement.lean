import Stilt.Theorems
import Stilt.InPlace.Handling
import Stilt.InPlace.Bodies
import Stilt.InPlace.Holding

/-!
# In-place agreement

The proof of `InPlaceAgreement`: on a well-typed program that obeys the law of
exclusivity, copy-in, copy-out and in-place mutation give the same observation
(values.inout-arguments; modes.law).

Evaluation keeps the simulation of `Stilt.InPlace.Steps` at every fuel, by
induction on the fuel, case by case on the expression as `eval_mono` is in
`Stilt.Fuel`. A well-typed program gives what the simulation needs of its
bodies: they obey the law (`Program.Exclusive`) and name their parameters once
each (`Decls.WellFormed` and typing).
-/

namespace Stilt

namespace InPlace

/-- Evaluating a safe expression, with any fuel, ends alike in both models. -/
theorem eval_agrees {D : Decls} (hD : Sim.DeclsSafe D) :
    ∀ n, SimRun (eval D Copy.memory n) (eval D InPlace.memory n)
  | 0, _, _ => Sim.outOfFuel
  | n + 1, e, ⟨⟨r, hex⟩, hdp⟩ => by
    have ih := eval_agrees hD n
    cases e <;> try simp only [Expr.exclusive, Expr.distinctParams, Bool.and_eq_true,
      decide_eq_true_eq] at hex hdp
    case var x => exact Sim.read x
    case move x => exact Sim.read x
    case int k => exact Sim.pure .int
    case bool b => exact Sim.pure .bool
    case unit => exact Sim.pure .unit
    case record R fs =>
      exact Sim.bind (Sim.fields ih fs (fields_safe hex hdp)) fun _ hw => Sim.declare D R hw
    case variant T C es =>
      exact Sim.bind (Sim.list ih es (exprs_safe hex hdp)) fun _ hvs => Sim.pure (.variant hvs)
    case list τ es =>
      exact Sim.bind (Sim.list ih es (exprs_safe hex hdp)) fun _ hvs => Sim.pure (.list hvs)
    case op o es =>
      exact Sim.bind (Sim.list ih es (exprs_safe hex hdp)) fun _ hvs =>
        Sim.world _ fun _ _ _ hx h => ⟨Op.run_safe hvs h, hx.run hvs h⟩
    case view es =>
      exact Sim.bind (Sim.list ih es (exprs_safe hex hdp)) fun _ hvs =>
        Sim.ofExcept _ fun _ h => Op.apply_safe hvs h
    case field e f =>
      exact Sim.bind (ih e ⟨⟨r, hex⟩, hdp⟩) fun _ hv => Sim.ofExcept _ fun _ h => hv.get h
    case index e i =>
      exact Sim.bind (ih e ⟨⟨r, hex.1⟩, hdp.1⟩) fun _ hv =>
        Sim.bind (Sim.bind (ih i ⟨⟨r, hex.2⟩, hdp.2⟩) fun _ _ => Sim.asInt) fun _ _ =>
          Sim.ofExcept _ fun _ h => hv.get h
    case fnRef f types rows => exact Sim.pure .function
    case method t m τ =>
      show Sim Value.Safe (Eval.method D t m τ) (Eval.method D t m τ)
      unfold Eval.method
      split
      · split
        · exact Sim.pure .function
        · exact Sim.fail _
      · exact Sim.fail _
    case closure ps result ρ body =>
      exact Sim.bind Sim.capture fun _ hc => Sim.pure (.closure hdp.1 hex hdp.2 (captureOf_forall hc))
    case call callee as _ =>
      exact Sim.bind (ih callee ⟨⟨r, hex.1.1.1⟩, hdp.1⟩) fun _ hf =>
        Sim.bind (Sim.args ih as (args_safe hex.1.1.2 hdp.2)) fun _ hp =>
          Sim.callAs hD ih false hf hp.1 (compat_of_resolved hp.2 ((pairwiseDisjoint_iff _).1 hex.2))
    case letIn x τ init body =>
      exact Sim.bind (ih init ⟨⟨r, hex.1⟩, hdp.1⟩) fun _ hv =>
        Sim.withInit x init hv (ih body ⟨⟨_, hex.2⟩, hdp.2⟩)
    case varIn x τ init body =>
      exact Sim.bind (ih init ⟨⟨r, hex.1⟩, hdp.1⟩) fun _ hv =>
        Sim.withInit x init hv (ih body ⟨⟨_, hex.2⟩, hdp.2⟩)
    case assign p value =>
      obtain ⟨x, ps⟩ := p
      simp only [Expr.exclusive, Expr.distinctParams, Bool.and_eq_true] at hex hdp
      exact Sim.assign ih x (path_safe hex.1.1 hdp.1) ⟨⟨r, hex.1.2⟩, hdp.2⟩
    case seq a b => exact Sim.bind (ih a ⟨⟨r, hex.1⟩, hdp.1⟩) fun _ _ => ih b ⟨⟨r, hex.2⟩, hdp.2⟩
    case «if» c τ a b =>
      exact Sim.bind (Sim.bind (ih c ⟨⟨r, hex.1.1⟩, hdp.1.1⟩) fun _ _ => Sim.asBool) fun v _ =>
        Sim.ite v (ih a ⟨⟨r, hex.1.2⟩, hdp.1.2⟩) (ih b ⟨⟨r, hex.2⟩, hdp.2⟩)
    case «match» e τ arms =>
      exact Sim.bind (ih e ⟨⟨r, hex.1⟩, hdp.1⟩) fun _ hv =>
        Sim.select ih (arms_safe hex.2 hdp.2) hv
    case «for» x τ e body => exact Sim.loop ih x ⟨⟨r, hex.1⟩, hdp.1⟩ ⟨⟨_, hex.2⟩, hdp.2⟩
    case raise e => exact Sim.bind (ih e ⟨⟨r, hex⟩, hdp⟩) fun _ hv => Sim.throw hv
    case «try» e => exact ih e ⟨⟨r, hex⟩, hdp⟩
    case tryCatch e E x h τ =>
      exact Sim.handle (ih e ⟨⟨r, hex.1⟩, hdp.1⟩) fun _ he =>
        Sim.withVar x he (ih h ⟨⟨_, hex.2⟩, hdp.2⟩)
    case «while» c body =>
      have hl := ih (.while c body) ⟨⟨r, by simp [Expr.exclusive, hex.1, hex.2]⟩,
        by simp [Expr.distinctParams, hdp.1, hdp.2]⟩
      exact Sim.bind (Sim.bind (ih c ⟨⟨r, hex.1⟩, hdp.1⟩) fun _ _ => Sim.asBool) fun v _ =>
        Sim.ite v (Sim.bind (Sim.turn (ih body ⟨⟨r, hex.2⟩, hdp.2⟩)) fun g _ =>
          Sim.ite g hl (Sim.pure .unit)) (Sim.pure .unit)
    case «loop» body =>
      have hl := ih (.loop body) ⟨⟨r, by simpa [Expr.exclusive] using hex⟩,
        by simpa [Expr.distinctParams] using hdp⟩
      exact Sim.bind (Sim.turn (ih body ⟨⟨r, hex⟩, hdp⟩)) fun g _ => Sim.ite g hl (Sim.pure .unit)
    case «break» => exact Sim.jump trivial
    case «continue» => exact Sim.jump trivial
    case «return» e => exact Sim.bind (ih e ⟨⟨r, hex⟩, hdp⟩) fun _ hv => Sim.jump hv
    case perform op e => exact Sim.bind (ih e ⟨⟨r, hex⟩, hdp⟩) fun _ hv => Sim.perform hv
    case withH E c h b =>
      exact Sim.bind (ih h ⟨⟨r, hex.1⟩, hdp.1⟩) fun _ hhv =>
        Sim.letGo (Sim.handleWith hD ih E c hhv (ih b ⟨⟨r, hex.2⟩, hdp.2⟩))
    case held ns hs b =>
      exact Sim.bind (Sim.list ih hs (exprs_safe hex.1 hdp.1)) fun vs _ =>
        Sim.held (ih b ⟨⟨_, hex.2⟩, hdp.2⟩) _ vs

end InPlace

open InPlace in
/-- **In-place agreement.** On a well-typed program that obeys the law of
exclusivity, copy-in, copy-out and in-place mutation give the same
observation and write the same output, with the same fuel and input. -/
theorem inPlaceAgreement : InPlaceAgreement := by
  intro p fuel input hwt hex
  have hD : Sim.DeclsSafe p.decls := fun d hd => by
    obtain ⟨σ, hty, -⟩ := hwt.typedIn.fns d hd
    exact ⟨hwt.decls.paramNames d hd, hex.1 d hd, hty.distinctParams⟩
  have hmain : p.main.Safe := by
    obtain ⟨σ, hty, -⟩ := hwt.main
    exact ⟨⟨[], hex.2⟩, hty.distinctParams⟩
  have hc := eval_agrees hD fuel p.main hmain ([], World.start input) (⟨[], []⟩, World.start input)
    ⟨⟨trivial, .nil, by simp⟩, rfl, World.All.start input⟩
  unfold Program.runCopy Program.runInPlace Program.run
  rcases hc.cases with ⟨v, ⟨_, x⟩, ⟨_, y⟩, h₁, h₂, -, ⟨-, hw, -⟩, -⟩ |
    ⟨e, ⟨_, x⟩, ⟨_, y⟩, h₁, h₂, -, ⟨-, hw, -⟩, -⟩ | ⟨j, ⟨_, x⟩, ⟨_, y⟩, h₁, h₂, -, ⟨-, hw, -⟩, -⟩ |
    ⟨k, ⟨_, x⟩, ⟨_, y⟩, h₁, h₂, ⟨-, hw, -⟩, -⟩ | ⟨_, _, _, _, _, _, h₁, h₂, -⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
    rw [h₁, h₂] <;> (try cases (show x = y from hw)) <;> first | rfl | (cases j <;> rfl)

/-- In particular the two models observe the same. -/
theorem inPlaceAgreement_observe (p : Program) (fuel : Nat) (input : String) (hwt : p.WellTyped)
    (hex : p.Exclusive) : (p.runCopy fuel input).observe = (p.runInPlace fuel input).observe :=
  congrArg Prod.fst (inPlaceAgreement p fuel input hwt hex)

end Stilt
