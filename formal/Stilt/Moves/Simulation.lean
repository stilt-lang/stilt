import Stilt.Moves.Handling
import Stilt.Moves.Release

/-!
# The simulation

Evaluating a safe expression whose marks are last uses keeps the simulation
of copy-in, copy-out by `Moving`, with any fuel: by induction on the fuel,
case by case on the expression, as `InPlace.eval_agrees` is.
-/

namespace Stilt.Moving

open InPlace

/-- A last use evaluates as a read, or runs out of fuel. -/
theorem moveReads (D : Decls) : ∀ n, MoveReads (eval D Copy.memory n) (eval D Moving.memory n)
  | 0 => fun _ => .inr ⟨rfl, rfl⟩
  | _ + 1 => fun _ => .inl ⟨rfl, rfl⟩

/-- Evaluating a safe expression whose marks are last uses, with any fuel,
ends alike in copy-in, copy-out and `Moving`. -/
theorem eval_msim {D : Decls} (hD : DeclsOk D) :
    ∀ n, MRun (eval D Copy.memory n) (eval D Moving.memory n)
  | 0, _, _, _, _ => MSim.outOfFuel
  | n + 1, e, L, ⟨⟨r, hex⟩, hdp⟩, hm => by
    have ih := eval_msim hD n
    cases e
    case call callee as _ => exact call_case hD ih (moveReads D n) hex hdp hm
    case «while» c body => exact while_case ih ⟨⟨r, hex⟩, hdp⟩ hm
    case «loop» body => exact loop_case ih ⟨⟨r, hex⟩, hdp⟩ hm
    all_goals try simp only [Expr.exclusive, Expr.distinctParams, Expr.movesOk, Expr.mentions,
      Bool.and_eq_true, decide_eq_true_eq] at hex hdp hm ⊢
    case var x => exact MSim.read x (by simp)
    case move x => exact MSim.read x (by simp)
    case int k => exact MSim.pure ⟨.int, .int⟩
    case bool b => exact MSim.pure ⟨.bool, .bool⟩
    case unit => exact MSim.pure ⟨.unit, .unit⟩
    case record R _ fs =>
      exact MSim.bind (MSim.fields ih L fs (fields_safe hex hdp) hm)
        (fun _ hw => MSim.declare D R hw) (by live_sub) (Live.Sub.refl _)
    case variant T _ C es =>
      exact MSim.bind (MSim.list ih L es (exprs_safe hex hdp) hm) (fun _ hvs => MSim.pure
        ⟨.variant fun v h => (hvs v h).1, .variant fun v h => (hvs v h).2⟩) (by live_sub)
        (Live.Sub.refl _)
    case list τ es =>
      exact MSim.bind (MSim.list ih L es (exprs_safe hex hdp) hm) (fun _ hvs => MSim.pure
        ⟨.list fun v h => (hvs v h).1, .list fun v h => (hvs v h).2⟩) (by live_sub)
        (Live.Sub.refl _)
    case op o es =>
      exact MSim.bind (MSim.list ih L es (exprs_safe hex hdp) hm) (fun _ hvs =>
        MSim.world _ fun _ _ _ hx h => ⟨⟨Op.run_safe (fun v h => (hvs v h).1) h,
          Op.run_justified (fun v h => (hvs v h).2) h⟩, hx.run hvs h⟩) (by live_sub) (Live.Sub.refl _)
    case view es =>
      exact MSim.bind (MSim.list ih L es (exprs_safe hex hdp) hm) (fun _ hvs =>
        MSim.ofExcept _ fun _ h => ⟨Op.apply_safe (fun v h => (hvs v h).1) h,
          Op.apply_justified (fun v h => (hvs v h).2) h⟩) (by live_sub) (Live.Sub.refl _)
    case field e f =>
      exact MSim.bind (ih e L ⟨⟨r, hex⟩, hdp⟩ hm) (fun _ hv => MSim.get hv _) (by live_sub)
        (Live.Sub.refl _)
    case index e i => exact index_case ih ⟨⟨r, hex.1⟩, hdp.1⟩ ⟨⟨r, hex.2⟩, hdp.2⟩ hm.1 hm.2
    case fnRef f types rows => exact MSim.pure ⟨.function, .function⟩
    case method t m τ =>
      show MSim VOk _ L _ (Eval.method D t m τ) (Eval.method D t m τ)
      unfold Eval.method
      split
      · split
        · exact MSim.pure ⟨.function, .function⟩
        · exact MSim.fail _
      · exact MSim.fail _
    case closure ps result ρ body => exact closure_case hdp.1 hex hdp.2 hm
    case letIn x τ init body =>
      exact let_case ih (moveReads D n) ⟨⟨r, hex.1⟩, hdp.1⟩ ⟨⟨_, hex.2⟩, hdp.2⟩ hm.1 hm.2
    case varIn x τ init body =>
      exact let_case ih (moveReads D n) ⟨⟨r, hex.1⟩, hdp.1⟩ ⟨⟨_, hex.2⟩, hdp.2⟩ hm.1 hm.2
    case assign p value =>
      obtain ⟨x, ps⟩ := p
      simp only [Expr.exclusive, Expr.distinctParams, Expr.movesOk, Expr.mentions,
        Bool.and_eq_true] at hex hdp hm ⊢
      exact assign_case ih (path_safe hex.1.1 hdp.1) ⟨⟨r, hex.1.2⟩, hdp.2⟩ hm.1 hm.2
    case seq a b =>
      exact MSim.bind ((ih a _ ⟨⟨r, hex.1⟩, hdp.1⟩ hm.1).mono (by live_sub) (Live.Sub.refl _)
        (by live_sub)) (fun _ _ => (ih b L ⟨⟨r, hex.2⟩, hdp.2⟩ hm.2).mono (Live.Sub.refl _)
          (Live.Sub.refl _) (by live_sub)) (by live_sub) (by live_sub)
    case «if» c τ a b =>
      exact if_case ih ⟨⟨r, hex.1.1⟩, hdp.1.1⟩ ⟨⟨r, hex.1.2⟩, hdp.1.2⟩ ⟨⟨r, hex.2⟩, hdp.2⟩
        hm.1.1 hm.1.2 hm.2
    case «match» e τ arms =>
      exact MSim.bind ((ih e _ ⟨⟨r, hex.1⟩, hdp.1⟩ hm.1).mono (by live_sub) (Live.Sub.refl _)
        (by live_sub)) (fun _ hv => (MSim.select ih (arms_safe hex.2 hdp.2) hm.2 hv).mono
          (Live.Sub.refl _) (Live.Sub.refl _) (by live_sub)) (by live_sub) (by live_sub)
    case «for» x τ e body => exact for_case ih ⟨⟨r, hex.1⟩, hdp.1⟩ ⟨⟨_, hex.2⟩, hdp.2⟩ hm.1 hm.2
    case raise e =>
      exact MSim.bind (ih e L ⟨⟨r, hex⟩, hdp⟩ hm) (fun _ hv => MSim.throw hv) (by live_sub)
        (Live.Sub.refl _)
    case «try» e => exact ih e L ⟨⟨r, hex⟩, hdp⟩ hm
    case form _ e => exact ih e L ⟨⟨r, hex⟩, hdp⟩ hm
    case tryCatch e E x h τ => exact catch_case ih ⟨⟨r, hex.1⟩, hdp.1⟩ ⟨⟨_, hex.2⟩, hdp.2⟩ hm.1 hm.2
    case «break» => exact MSim.jump trivial
    case «continue» => exact MSim.jump trivial
    case «return» e =>
      exact MSim.bind (ih e L ⟨⟨r, hex⟩, hdp⟩ hm) (fun _ hv => MSim.jump hv) (by live_sub)
        (Live.Sub.refl _)
    case perform op e =>
      exact MSim.bind (ih e L ⟨⟨r, hex⟩, hdp⟩ hm) (fun _ hv => MSim.perform hv) (by live_sub)
        (Live.Sub.refl _)
    case withH E c h b =>
      exact MSim.bind ((ih h _ ⟨⟨r, hex.1⟩, hdp.1⟩ hm.1).mono (by live_sub) (Live.Sub.refl _)
        (by live_sub)) (fun _ hhv => MSim.letGo ((MSim.handleWith hD ih E c hhv
          (ih b L ⟨⟨r, hex.2⟩, hdp.2⟩ hm.2)).mono (Live.Sub.refl _) (Live.Sub.refl _)
            (by live_sub))) (by live_sub) (by live_sub)
    case held ns hs b =>
      exact MSim.bind ((MSim.list ih _ hs (exprs_safe hex.1 hdp.1) hm.1).mono
        (by live_sub) (Live.Sub.refl _) (by live_sub))
        (fun vs _ => MSim.held _ vs (ih b _ ⟨⟨_, hex.2⟩, hdp.2⟩ hm.2)
          (by live_sub) (by live_sub) (Live.sub_union_left _ _) (by live_sub))
        (by live_sub) (Live.sub_union_left _ _)

end Stilt.Moving
