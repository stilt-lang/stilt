import Stilt.Windows.Effects
import Stilt.Windows.Closure
import Stilt.Windows.Match
import Stilt.Windows.Assign
import Stilt.Windows.Held
import Stilt.Windows.Top
import Stilt.Soundness.Identity
import Stilt.Windows.Call.Call
import Stilt.Windows.Call.Callee

/-!
# The simulation of in-place mutation by windows

By induction on the fuel, every expression that the checks of views accept, run in a context
whose scope keeps its bindings' sources, ends alike in both models, each form by its own case.
The call and a handler's call of its clauses are cases of their own (`Cases`), which every
program whose functions the checks accept gives (`cases_of`).
-/

namespace Stilt

namespace Windows

variable {D : Decls}

/-- The cases of the induction proved on their own: a call, and a call of a value as a handler
calls its clauses. -/
structure Cases (D : Decls) : Prop where
  call : ∀ (n : Nat) (c : Ctx) (pend : List (Window × Value)), ScopeKeeps D c.Γ → RunsAll D n →
    ∀ {callee₀ callee : Expr} {args₀ args : List Arg} {τ₀ τ : Ty},
      Expr.Inst D (.call callee₀ args₀ τ₀) (.call callee args τ) →
      (Expr.call callee₀ args₀ τ₀).viewsRead D c.Γ c.R = true →
      (Expr.call callee₀ args₀ τ₀).contained D c.Γ c.P = true →
      Sim D c pend ((Expr.call callee₀ args₀ τ₀).sources D c.Γ)
        (Stilt.eval D InPlace.memory (n + 1) (.call callee args τ))
        (Windows.eval D (n + 1) (.call callee args τ))
  calls : ∀ (n : Nat) (c : Ctx) (pend : List (Window × Value)), ScopeKeeps D c.Γ → RunsAll D n →
    CallsValues D c pend n

/-- The functions of a program that the checks accept give the cases of a call. -/
theorem cases_of (hD : DeclsChecked D) : Cases D :=
  ⟨fun n _ _ hΓ ih _ _ _ _ _ _ hi hr hc => SimP.call hD n hΓ ih hi hr hc,
    fun n c pend _ ih => callsValues hD n c pend ih⟩

/-- **The simulation.** With any fuel, an instance of an expression that the checks of views
accept runs alike in place and with windows. -/
theorem eval_sim (hk : Cases D) : ∀ n, RunsAll D n
  | 0, _, _, _, _, _ => fun _ _ _ _ => SimP.outOfFuel
  | n + 1, c, hΓ, _, _, hi => by
    have ih : RunsAll D n := eval_sim hk n
    intro X pend hr hc
    have hΓ' : ScopeKeeps D { c with R := X }.Γ := hΓ
    cases hi with
    | var x => exact SimP.var n x
    | move x => exact SimP.move n x
    | int k => exact SimP.int n k
    | bool b => exact SimP.bool n b
    | unit => exact SimP.unit n
    | record R h => exact SimP.record n hΓ' R h ih hr hc
    | variant T C h => exact SimP.variant n hΓ' T C h ih hr hc
    | list τ₀ τ h => exact SimP.listLit n hΓ' τ₀ τ h ih hr hc
    | op o₀ o h => exact SimP.opOf n hΓ' o₀ o h ih hr hc
    | view h =>
      rename_i es₀ es
      cases h with
      | nil => exact SimP.fail .stuck
      | cons h hs => exact SimP.view n hΓ' h hs ih hr hc
    | field f h => exact SimP.fieldOf n hΓ' f h ih hr hc
    | index he hi => exact SimP.indexOf n hΓ' he hi ih hr hc
    | fnRef f tys tys' rows rows' => exact SimP.fnRef n f tys' rows'
    | method t m τ τ' => exact SimP.method n t m τ'
    | closure ρ ρ' hnd hps hτ hb => exact SimP.closure n hΓ' (.closure ρ ρ' hnd hps hτ hb) hr hc
    | call hx hf has hτ => exact hk.call n _ pend hΓ' ih (.call hx hf has hτ) hr hc
    | letIn x hτ hi hb => exact SimP.bindLet n hΓ' hτ hi hb ih hr hc
    | varIn x hτ hi hb => exact SimP.bindVar n hΓ' hτ hi hb ih hr hc
    | assign x hps hv => exact SimP.assign n hps hv hΓ' ih hr hc
    | seq ha hb => exact SimP.seq n hΓ' ha hb ih hr hc
    | «if» τ₀ τ hk' ha hb => exact SimP.cond n hΓ' τ₀ τ hk' ha hb ih hr hc
    | «match» τ₀ τ he has => exact SimP.matchArms n hΓ' he has ih hr hc
    | «for» x τ₀ τ he hb => exact SimP.forLoop n hΓ' τ₀ τ he hb ih hr hc
    | raise he => exact SimP.raiseOf n hΓ' he ih hr hc
    | «try» he => exact ih c hΓ _ _ he X pend hr hc
    | tryCatch E₀ E x τ₀ τ he hh => exact SimP.catchOf n hΓ' E₀ E x τ₀ τ he hh ih hr hc
    | «while» hk' hb => exact SimP.whileLoop n hΓ' hk' hb ih hr hc
    | «loop» hb => exact SimP.loopBody n hΓ' hb ih hr hc
    | «break» => exact SimP.jumpPlain .brk (.inl rfl)
    | «continue» => exact SimP.jumpPlain .cont (.inr rfl)
    | «return» he => exact SimP.returnOf n hΓ' he ih hr hc
    | perform op he => exact SimP.performOf n hΓ' op he ih hr hc
    | withH E ctl hh hb =>
      exact SimP.handleOf n hΓ' E ctl hh hb ih (hk.calls n _ pend hΓ' ih) hr hc
    | held hns hs hb => exact SimP.held n hΓ' (.held hns hs hb) ih hr hc

/-- An expression whose closure literals name their parameters once, and that obeys the law,
is an instance of itself. -/
theorem Expr.inst_self {e : Expr} {r : List Shape} (hd : e.distinctParams = true)
    (hx : e.exclusive r = true) : Expr.Inst D e e := by
  have h := Expr.inst_subst D [] [] e r hd hx
  rwa [Expr.substTys_nil, Expr.substRows_nil] at h

/-- A run of `main`, when the program's checks of views accept it, shows in place what it shows
with windows. -/
theorem shows_windows {p : Program} (hk : Cases p.decls) (hd : p.main.distinctParams = true)
    (hx : p.main.exclusive [] = true) (hr : p.ViewsRead) (hc : p.ViewsContained) (fuel : Nat) (input : String) :
    (p.runInPlace fuel input).shows = (p.runWindows fuel input).shows :=
  shows_of_main (eval_sim hk fuel Ctx.main (ScopeKeeps.nil _) p.main p.main
    (Expr.inst_self hd hx) [] [] hr.2 hc.2) input

end Windows

end Stilt
