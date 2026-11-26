import Stilt.Theorems
import Stilt.Sharing.Call
import Stilt.Sharing.Assignment
import Stilt.Sharing.Let
import Stilt.Sharing.Capture
import Stilt.Sharing.Handling
import Stilt.Sharing.Holding
import Stilt.Sharing.Scope
import Stilt.Sharing.Alias

/-!
# Copies and sharing agree when every binding is shared

The simulation of copies by sharing, form by form: every evaluation of a safe expression ends
alike in both models when every binding is shared (modes.shared-writes), each binding reading in
the sharing model's store what it holds as a copy. So a run of `main` shows the same in both.
-/

namespace Stilt.Sharing

open InPlace (Passed.Compat)

/-- A `when` in both models (shared.when). -/
theorem Sim.held {shared : Name → Bool} {m : Eval Copy.State Value}
    {m' : Eval (State × World) Value} (hm : Sim Value.Safe m m') (names : List Name)
    (vs : List Value) :
    Sim Value.Safe (Eval.held Copy.memory m names vs) (Eval.held (memory shared) m' names vs) := by
  unfold Eval.held
  refine Sim.bind (G := fun _ => True) (Sim.ofExcept _ fun _ _ => trivial) fun cells _ => ?_
  refine Sim.bind (Sim.bind (Sim.world shared _ fun x v x' hx h => ?_) fun _ hv => Sim.asList hv)
    fun us hus => ?_
  · cases ht : World.take cells x with
    | error e => rw [ht] at h; cases h
    | ok p =>
      rw [ht] at h
      cases h
      obtain ⟨hp, hx'⟩ := hx.take ht
      exact ⟨.list hp, hx'⟩
  · split
    · exact Sim.withVars shared (fun fr s hs => Corr.release _ (hm fr s hs)) _
        fun xv hxv => hus _ (List.of_mem_zip hxv).2
    · exact Sim.fail _

/-- Calling a clause: one value, no place, so no root stops sharing. -/
theorem Sim.callValue {D : Decls} (hD : InPlace.Sim.DeclsSafe D) {shared : Name → Bool}
    (hsh : ∀ y, shared y = true) {run : Expr → Eval Copy.State Value}
    {run' : Expr → Eval (State × World) Value} (h : SimRun run run') (c : Bool) (f v : Value)
    (hf : f.Safe) (hv : v.Safe) :
    Sim Value.Safe (Eval.callAs D Copy.memory run c f [.value v])
      (Eval.callAs D (memory shared) run' c f [.value v]) := by
  have hp : InPlace.Sim.PassedSafe [.value v] := by
    intro q hq w hw
    simp only [List.mem_singleton] at hq
    subst hq
    cases hw
    exact hv
  exact Sim.callAs hD hsh h c hf hp (List.pairwise_singleton _ _)

/-- Evaluating a safe expression, with any fuel, ends alike with copies and with sharing when
every binding is shared. -/
theorem eval_agrees {D : Decls} (hD : InPlace.Sim.DeclsSafe D) {shared : Name → Bool}
    (hsh : ∀ y, shared y = true) :
    ∀ n, SimRun (Stilt.eval D Copy.memory n) (Sharing.eval D shared n)
  | 0, _, _ => Sim.outOfFuel
  | n + 1, e, ⟨⟨r, hex⟩, hdp⟩ => by
    have ih := eval_agrees hD hsh n
    have ha : ∀ e s v s₁, Sharing.eval D shared n e s = .done v s₁ → ∀ r,
        aliasRef? s₁.1 e = some r → deref s₁.1 r [] = .ok v ∧ r.toPath.Under s₁.1.paths :=
      fun e => eval_alias D shared n e
    cases e <;> try simp only [Expr.exclusive, Expr.distinctParams, Bool.and_eq_true,
      decide_eq_true_eq] at hex hdp
    case var x => exact Sim.read shared x
    case move x => exact Sim.read shared x
    case int k => exact Sim.pure .int
    case bool b => exact Sim.pure .bool
    case unit => exact Sim.pure .unit
    case record R _ fs =>
      exact Sim.bind (Sim.fields ih fs (fields_safe hex hdp)) fun _ hw => Sim.declare D R hw
    case variant T _ C es =>
      exact Sim.bind (Sim.list ih es (exprs_safe hex hdp)) fun _ hvs => Sim.pure (.variant hvs)
    case list τ es =>
      exact Sim.bind (Sim.list ih es (exprs_safe hex hdp)) fun _ hvs => Sim.pure (.list hvs)
    case op o es =>
      exact Sim.bind (Sim.list ih es (exprs_safe hex hdp)) fun _ hvs =>
        Sim.world shared _ fun _ _ _ hx h => ⟨Op.run_safe hvs h, hx.run hvs h⟩
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
      exact Sim.closure ps result ρ body fun _ hc => .closure hdp.1 hex hdp.2 hc
    case call callee as _ =>
      exact Sim.bind (ih callee ⟨⟨r, hex.1.1.1⟩, hdp.1⟩) fun _ hf =>
        Sim.bind (Sim.args ih as (args_safe hex.1.1.2 hdp.2)) fun _ hp =>
          Sim.callAs hD hsh ih false hf hp.1
            (InPlace.compat_of_resolved hp.2 ((pairwiseDisjoint_iff _).1 hex.2))
    case letIn x τ init body =>
      exact Sim.letIn D hsh x τ init (ih init ⟨⟨r, hex.1⟩, hdp.1⟩) (ha init)
        (fun hp s => eval_simple D shared n init s hp)
        (ih body ⟨⟨_, hex.2⟩, hdp.2⟩)
    case varIn x τ init body =>
      exact Sim.letIn D hsh x τ init (ih init ⟨⟨r, hex.1⟩, hdp.1⟩) (ha init)
        (fun hp s => eval_simple D shared n init s hp)
        (ih body ⟨⟨_, hex.2⟩, hdp.2⟩)
    case assign p value =>
      obtain ⟨x, ps⟩ := p
      simp only [Expr.exclusive, Expr.distinctParams, Bool.and_eq_true] at hex hdp
      exact Sim.assign ih x (path_safe hex.1.1 hdp.1) ⟨⟨r, hex.1.2⟩, hdp.2⟩ (ha value)
        (fun hp s => eval_simple D shared n value s hp)
    case seq a b => exact Sim.bind (ih a ⟨⟨r, hex.1⟩, hdp.1⟩) fun _ _ => ih b ⟨⟨r, hex.2⟩, hdp.2⟩
    case «if» c τ a b =>
      exact Sim.bind (Sim.bind (ih c ⟨⟨r, hex.1.1⟩, hdp.1.1⟩) fun _ _ => Sim.asBool) fun v _ =>
        Sim.ite v (ih a ⟨⟨r, hex.1.2⟩, hdp.1.2⟩) (ih b ⟨⟨r, hex.2⟩, hdp.2⟩)
    case «match» e τ arms =>
      exact Sim.bind (ih e ⟨⟨r, hex.1⟩, hdp.1⟩) fun _ hv =>
        Sim.select shared ih (arms_safe hex.2 hdp.2) hv
    case «for» x τ e body => exact Sim.loop shared ih x ⟨⟨r, hex.1⟩, hdp.1⟩ ⟨⟨_, hex.2⟩, hdp.2⟩
    case raise e => exact Sim.bind (ih e ⟨⟨r, hex⟩, hdp⟩) fun _ hv => Sim.throw hv
    case «try» e => exact ih e ⟨⟨r, hex⟩, hdp⟩
    case form _ e => exact ih e ⟨⟨r, hex⟩, hdp⟩
    case tryCatch e E x h τ =>
      exact Sim.handle (ih e ⟨⟨r, hex.1⟩, hdp.1⟩) fun _ he =>
        Sim.withVar shared x he (ih h ⟨⟨_, hex.2⟩, hdp.2⟩)
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
    case perform op e => exact Sim.bind (ih e ⟨⟨r, hex⟩, hdp⟩) fun _ hv => Sim.perform shared hv
    case withH E c h b =>
      exact Sim.bind (ih h ⟨⟨r, hex.1⟩, hdp.1⟩) fun _ hhv =>
        Sim.letGo (Sim.handleWith shared E c (fun f v hf hv => Sim.callValue hD hsh ih c f v hf hv)
          hhv (ih b ⟨⟨r, hex.2⟩, hdp.2⟩))
    case held ns hs b =>
      exact Sim.bind (Sim.list ih hs (exprs_safe hex.1 hdp.1)) fun vs _ =>
        Sim.held (ih b ⟨⟨_, hex.2⟩, hdp.2⟩) _ vs

/-- A run of `main`, every binding shared, shows what copies show. -/
theorem shows_all {p : Program} (hwt : p.WellTyped) (hex : p.Exclusive)
    {shared : Name → Bool} (hsh : ∀ y, shared y = true) (fuel : Nat) (input : String) :
    (p.runCopy fuel input).shows =
      (Sharing.eval p.decls shared fuel p.main (⟨[], #[]⟩, World.start input)).leaveBody.shows := by
  have hD : InPlace.Sim.DeclsSafe p.decls := fun d hd => by
    obtain ⟨σ, hty, -⟩ := hwt.typedIn.fns d hd
    exact ⟨hwt.decls.paramNames d hd, hex.1 d hd, hty.distinctParams⟩
  have hmain : p.main.Safe := by
    obtain ⟨σ, hty, -⟩ := hwt.main
    exact ⟨⟨[], hex.2⟩, hty.distinctParams⟩
  have h0 : AgreesIn ([], World.start input) (⟨[], #[]⟩, World.start input) :=
    ⟨⟨rfl, rfl, trivial, by simp, .nil, by simp⟩, ⟨by simp, by simp, by simp⟩, rfl, World.All.start input⟩
  have hc := eval_agrees hD hsh fuel p.main hmain _ _ h0
  unfold Program.runCopy Program.run
  rcases hc.cases with ⟨v, ⟨_, x⟩, ⟨_, y⟩, h₁, h₂, -, ⟨-, -, hw, -⟩, -⟩ |
    ⟨e, ⟨_, x⟩, ⟨_, y⟩, h₁, h₂, -, ⟨-, -, hw, -⟩, -⟩ |
    ⟨j, ⟨_, x⟩, ⟨_, y⟩, h₁, h₂, -, ⟨-, -, hw, -⟩, -⟩ |
    ⟨k, ⟨_, x⟩, ⟨_, y⟩, h₁, h₂, ⟨-, -, hw, -⟩, -⟩ | ⟨_, _, _, _, _, _, h₁, h₂, -⟩ | ⟨h₁, h₂⟩ |
    ⟨h₁, h₂⟩ <;>
    rw [h₁, h₂] <;> (try cases (show x = y from hw)) <;> first | rfl | (cases j <;> rfl)

/-- A well-typed, exclusive program that binds a name twice runs with sharing as with copies:
the inference calls every binding of it shared, and sharing every binding agrees with copies
(modes.shared-writes). -/
theorem Program.runSharing_shows_of_not_nodup {p : Program} (hwt : p.WellTyped)
    (hex : p.Exclusive) (hdup : ¬p.binders.Nodup) (fuel : Nat) (input : String) :
    (p.runCopy fuel input).shows = (p.runSharing fuel input).shows :=
  shows_all hwt hex (p.isShared_of_not_nodup hdup) fuel input

end Stilt.Sharing
