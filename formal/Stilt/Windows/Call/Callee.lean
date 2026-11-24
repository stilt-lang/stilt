import Stilt.Windows.Call.Value
import Stilt.Windows.Checked
import Stilt.Windows.Effects

/-!
# Calling a function value

A call of a closure or of a declared function runs its body as `Eval.invoke` does, in the
context the checks read it in: a function's parameters (`FnDecl.viewScope`), or a closure's
parameters on top of the variables around its literal (`ViewScope.enter`). A value that can't be
called, or a clause that takes control called where none may be, is stuck in both models. Both
models end alike: what the call gives is read alike, each window of the value of windows reading
the region of a window of a value passed (views.across-calls).
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls}

variable {c : Ctx} {pend : List (Window × Value)} {run : Expr → Eval IState Value}
  {run' : Expr → Eval WState Value}

/-- A callee's body run with its parameters bound to arguments passed alike. -/
theorem SimP.invoke
    (ih : ∀ c' : Ctx, ScopeKeeps D c'.Γ → ∀ e₀ e, Expr.Inst D e₀ e → RunsIn D c' run run' e₀ e)
    {captured : List (Name × Value)} (hcap : ∀ xv ∈ captured, xv.2.Viewed D) {Γ₀ : ViewScope}
    (hΓ₀ : ∀ xb ∈ Γ₀, xb.2.param = true) {params ps₀ : List Param}
    (hK : ScopeKeeps D (ViewScope.params D Γ₀ ps₀)) (hps : ParamsInst D ps₀ params)
    (hnd : (ps₀.map Param.name).Nodup) {result₀ : Ty} {b₀ body : Expr} (hinst : Expr.Inst D b₀ body)
    (hr : b₀.viewsRead D (ViewScope.params D Γ₀ ps₀) [] = true)
    (hc : b₀.contained D (ViewScope.params D Γ₀ ps₀) (resultParams D ps₀ result₀) = true)
    (hl : leaves (resultParams D ps₀ result₀) (b₀.sources D (ViewScope.params D Γ₀ ps₀)) = true)
    {ps ps' : List Passed} :
    SimP D c pend (fun si sw => PassRel D c si sw ps ps' ∧ ps.Pairwise InPlace.Passed.Compat ∧
        KeptFor D params ps')
      (ValueG D ps') (Eval.invoke InPlace.memory captured params ps (run body))
      (settled (Eval.invoke memory captured params ps' (run' body))) := by
  intro si sw hp hg ⟨hrel, hcomp, hkept⟩
  show Outcome.Rel _ (Eval.invoke InPlace.memory captured params ps (run body) si)
    ((Eval.invoke memory captured params ps' (run' body) sw).settle sw.1.store.length)
  rcases bindArgs_rel params hrel with ⟨h₁, h₂⟩ | ⟨b, b', h₁, h₂⟩
  · simp only [Eval.invoke, h₁, h₂]
    trivial
  rcases enter_rel hp hg hrel hkept hcomp h₁ h₂ hcap hΓ₀ hps hnd result₀ with
    ⟨e, he₁, he₂⟩ | ⟨si', sw', c', he₁, he₂, hΓ, hR, hP, hIn, hp', hg', hL⟩
  · simp only [Eval.invoke, h₁, h₂, he₁, he₂]
    exact fault_settle hp e
  · simp only [Eval.invoke, h₁, h₂, he₁, he₂]
    obtain ⟨Γ', R', In', L', P', Old', Start'⟩ := c'
    simp only at hΓ hR hP hIn
    subst hΓ hR hP
    have ho := ih ⟨_, [], In', L', _, Old', Start'⟩ hK b₀ body hinst [] pend hr hc si' sw' hp' hg'
      trivial
    exact Outcome.Rel.mono (Outcome.Rel.settle hL (mem_of_leaves hl) b b' _ _ ho)
      ⟨fun _ _ _ _ ⟨k₁, k₂, k₃⟩ => ⟨k₁, k₂, callG_value h₂ hIn k₃⟩, CorrG.escapes⟩

theorem stuck_settled {Q : IState → WState → Prop} {G : Value → Value → IState → WState → Prop} :
    SimP D c pend Q G (Eval.fail .stuck) (settled (Eval.fail .stuck)) :=
  fun _ _ _ _ _ => trivial

/-- A call of a value the checks accept, with arguments passed alike: a closure's or a declared
function's body run as a call, or stuck in both models. -/
theorem SimP.callValue (hD : DeclsChecked D)
    (ih : ∀ c' : Ctx, ScopeKeeps D c'.Γ → ∀ e₀ e, Expr.Inst D e₀ e → RunsIn D c' run run' e₀ e)
    (ctl : Bool) {f : Value} (hf : f.Viewed D) {ps ps' : List Passed} :
    SimP D c pend (fun si sw => PassRel D c si sw ps ps' ∧ ps.Pairwise InPlace.Passed.Compat ∧
        KeptFor D (paramsOf D f) ps')
      (ValueG D ps') (Eval.callAs D InPlace.memory run ctl f ps)
      (callSettled D run' ctl f ps') := by
  show SimP _ _ _ _ _ _ (settled (Eval.callAs D memory run' ctl f ps'))
  unfold Eval.callAs
  by_cases hct : (!ctl && f.takesControl D) = true
  · simp only [hct, ↓reduceIte]
    exact stuck_settled
  simp only [Bool.not_eq_true] at hct
  simp only [hct, Bool.false_eq_true, ↓reduceIte]
  unfold Eval.call
  cases hf with
  | closure hcap hcc =>
    obtain ⟨Γ, ps₀, result₀, b₀, hK, hnd, hps, hinst, hr, hc, hl⟩ := hcc
    exact SimP.invoke ih hcap
      (Γ₀ := List.map (fun xb : Name × ViewBinding => (xb.1, { xb.2 with param := true })) Γ)
      (fun xb hxb => by obtain ⟨_, -, rfl⟩ := List.mem_map.1 hxb; rfl) (ScopeKeeps.enter hK ps₀)
      hps hnd hinst hr hc hl
  | @function name types rows =>
    cases hd : D.fn? name with
    | none =>
      simp only [hd]
      exact stuck_settled
    | some d =>
      simp only [hd]
      obtain ⟨hnd', hdp, hex, hr, hc, hl⟩ := hD d (List.mem_of_find?_eq_some hd)
      have hpo : paramsOf D (.function name types rows) = d.params := by simp [paramsOf, hd]
      rw [hpo]
      exact SimP.invoke ih (fun _ h => by cases h) (Γ₀ := []) (fun _ h => by cases h)
        (ScopeKeeps.fn d) (ParamsInst.refl d.params) hnd'
        (Expr.inst_subst D _ _ d.body [] hdp hex) hr hc hl
  | _ => exact stuck_settled

theorem Outcome.bind_done {σ α : Type} : ∀ o : Outcome σ α, o.bind (fun a s => .done a s) = o
  | .done _ _ | .raised _ _ | .jumped _ _ | .panicked _ _ | .outOfFuel | .stuck => rfl
  | .performed op v s k => by
    simp only [Outcome.bind]
    congr
    funext w x
    exact Outcome.bind_done (k w x)

theorem Eval.bind_pure' {σ α : Type} (m : Eval σ α) : m >>= Pure.pure = m := by
  funext s
  exact Outcome.bind_done (m s)

/-- A call's value read through its windows, on the windows' side, as the in-place value. -/
theorem SimP.thenResolve {Q : IState → WState → Prop} {ps' : List Passed} {m : Eval IState Value}
    {m' : Eval WState Value} (h : SimP D c pend Q (ValueG D ps') m m') :
    SimP D c pend Q (FreeG D) m (m' >>= resolveE) := by
  rw [← Eval.bind_pure' m]
  refine SimP.bind h fun u w si sw hp _ hq => ?_
  show Outcome.Rel _ (Outcome.done u si) (Eval.ofExcept (resolve sw.1.store w) sw)
  rw [hq.1.resolve]
  exact ⟨hp, rfl, rfl, hq.2.1.free, hq.2.1⟩

/-- A clause called as a `with` calls it, with a value that holds no window: what
`SimP.withHandler` asks of its calls (`hcall`). -/
theorem SimP.callFree (hD : DeclsChecked D)
    (ih : ∀ c' : Ctx, ScopeKeeps D c'.Γ → ∀ e₀ e, Expr.Inst D e₀ e → RunsIn D c' run run' e₀ e)
    (ctl : Bool) {f : Value} (hf : f.Viewed D) {v : Value} (hv : Free v)
    (hvv : v.Viewed D) :
    SimP D c pend (fun _ _ => True) (FreeG D) (Eval.callAs D InPlace.memory run ctl f [.value v])
      (callSettled D run' ctl f [.value v] >>= resolveE) := by
  refine SimP.thenResolve ((SimP.callValue hD ih ctl hf).mono (fun si sw _ => ?_)
    fun _ _ _ _ h => h)
  refine ⟨.value (VRel.free hv) hvv (fun _ h => absurd h (not_mem_of_free hv)) .nil,
    List.pairwise_singleton _ _, fun i p a _ ha w hw hfw => absurd ?_ hfw⟩
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
    subst ha
    simp only [Passed.value?, Option.some.injEq] at hw
    exact hw ▸ hv
  | succ i => simp at ha

/-- The calls a `with` makes of its clauses run alike (`Cases.calls`). -/
theorem callsValues (hD : DeclsChecked D) (n : Nat) (c : Ctx)
    (pend : List (Window × Value)) (hk : RunsAll D n) : CallsValues D c pend n :=
  fun ctl _ hf _ _ hv hvv => SimP.callFree hD hk ctl hf hv hvv

end Windows

end Stilt
