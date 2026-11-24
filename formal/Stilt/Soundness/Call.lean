import Stilt.Soundness.Frames

/-!
# Calls

A call of a function value runs its body as the value's type promises: a
closure's body in the frame it captured, under the environment of the body
that made it, and a declared function's body under the environment that its
use composed. `Sound D n` says that evaluating with fuel `n` keeps typing's
promises; a call at fuel `n + 1` runs its body at fuel `n`, so it rests on
`Sound D n` alone. A call contributes its callee's row, and effects.missing-effects and
effects.catch-around-row-variables put that row within what the code around the call may raise.
-/

namespace Stilt

/-- Declarations whose functions' bodies check against their signatures
(declarations.function-declarations). -/
structure Decls.Typed (D : Decls) : Prop where
  wf : D.WellFormed
  fns : ∀ d ∈ D.fns, d.WellTyped D d.scope

/-- Evaluating any instantiation of a well-typed expression with fuel `n`, from
a frame of its context, under an environment that keeps its scope's promises,
ends as `Outcome.Ok` says. A call runs its callee's body instantiated (effects.inference), so the property is about every instantiation. -/
def Sound (D : Decls) (n : Nat) : Prop :=
  ∀ {scope : RowScope} {Γ : Ctx} {fx : Effects} {e : Expr} {τ : Ty},
    HasType D scope Γ fx e τ → ∀ {η : REnv}, η.Respects scope → ∀ θ : RowSubst,
      Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (τ.close η))
        (eval D Copy.memory n (e.substRows θ))

theorem Decls.mem_of_fn? {D : Decls} {f : Name} {d : FnDecl} (h : D.fn? f = some d) : d ∈ D.fns :=
  List.mem_of_find?_eq_some h

section

variable {D : Decls}

theorem Frame.Typed.freeze :
    ∀ {γ : Copy.Frame} {Γ : Ctx} {η : REnv}, Frame.Typed D γ Γ η → Frame.Typed D γ Γ.freeze η
  | _, _, _, .nil => .nil
  | _, _, _, .cons hv hrest => .cons hv (Frame.Typed.freeze hrest)

theorem copy_leave_ok {γ s' : Copy.State} {bound : List (Name × Passed)} {fr : Copy.Frame}
    (h : Copy.leave γ.1 s'.1 bound = .ok fr) : Copy.memory.leave γ s' bound = .ok (fr, s'.2) := by
  show (·, s'.2) <$> Copy.leave γ.1 s'.1 bound = _
  rw [h]
  rfl

theorem copy_leave_error {γ s' : Copy.State} {bound : List (Name × Passed)} {f : Fault}
    (h : Copy.leave γ.1 s'.1 bound = .error f) : Copy.memory.leave γ s' bound = .error f := by
  show (·, s'.2) <$> Copy.leave γ.1 s'.1 bound = _
  rw [h]
  rfl

theorem copy_enter_ok {γ : Copy.State} {captured : Copy.Frame} {bound : List (Name × Passed)}
    {fr : Copy.Frame} (h : Copy.enter γ.1 captured bound = .ok fr) :
    Copy.memory.enter γ captured bound = .ok (fr, γ.2) := by
  show (·, γ.2) <$> Copy.enter γ.1 captured bound = _
  rw [h]
  rfl

theorem copy_enter_error {γ : Copy.State} {captured : Copy.Frame} {bound : List (Name × Passed)}
    {f : Fault} (h : Copy.enter γ.1 captured bound = .error f) :
    Copy.memory.enter γ captured bound = .error f := by
  show (·, γ.2) <$> Copy.enter γ.1 captured bound = _
  rw [h]
  rfl

/-- A callee's outcome in the callee's context, left as its call: its value,
the value of a `return` (expressions.closure-boundaries), its raises and its
performances go where the call's type says, and the caller's frame stays typed.
A body makes no other jump. -/
theorem _root_.Stilt.Outcome.Ok.leaveCall {Γ Γc : Ctx} {η ηc : REnv} {X Xc : Exits}
    {P Pc : Value → Prop} {bound : List (Name × Passed)} {ps₀ : List Param} {γ : Copy.State}
    (hbound : Bound.Typed D Γ η ηc bound ps₀)
    (hl : ∀ p ∈ ps₀, Γc.lookup p.name = some ⟨p.type, p.mode = .inout⟩)
    (hγ : Frame.Typed D γ.1 Γ η) (hP : ∀ v, Pc v → P v) (hR : Xc.Raises D X)
    (hret : ∀ v, Xc.jumps (.ret v) → P v) (hbrk : ¬ Xc.jumps .brk) (hcont : ¬ Xc.jumps .cont)
    (hO : Xc.Performs X) :
    ∀ {o : Outcome Copy.State Value}, o.Ok D Γc ηc Xc Pc →
      (o.leaveCall Copy.memory bound γ).Ok D Γ η X P
  | .done v s', ⟨hv, hs'⟩ => by
    simp only [Outcome.leaveCall]
    rcases hbound.leave hs'.1 hl hγ with ⟨s'', hlv, hs''⟩ | hlv
    · rw [copy_leave_ok hlv]
      exact ⟨hP v hv, hs'', hs'.2⟩
    · rw [copy_leave_error hlv]
      exact ⟨hγ, hs'.2⟩
  | .raised e s', ⟨⟨F, hF, he⟩, hs'⟩ => by
    simp only [Outcome.leaveCall]
    rcases hbound.leave hs'.1 hl hγ with ⟨s'', hlv, hs''⟩ | hlv
    · rw [copy_leave_ok hlv]
      exact ⟨hR e F hF he, hs'', hs'.2⟩
    · rw [copy_leave_error hlv]
      exact ⟨hγ, hs'.2⟩
  | .jumped (.ret v) s', ⟨hv, hs'⟩ => by
    simp only [Outcome.leaveCall]
    rcases hbound.leave hs'.1 hl hγ with ⟨s'', hlv, hs''⟩ | hlv
    · rw [copy_leave_ok hlv]
      exact ⟨hret v hv, hs'', hs'.2⟩
    · rw [copy_leave_error hlv]
      exact ⟨hγ, hs'.2⟩
  | .jumped .brk _, ⟨h, _⟩ => absurd h hbrk
  | .jumped .cont _, ⟨h, _⟩ => absurd h hcont
  | .panicked k s', hs' => by
    simp only [Outcome.leaveCall]
    rcases hbound.leave hs'.1 hl hγ with ⟨s'', hlv, hs''⟩ | hlv
    · rw [copy_leave_ok hlv]
      exact ⟨hs'', hs'.2⟩
    · rw [copy_leave_error hlv]
      exact ⟨hγ, hs'.2⟩
  | .performed op v s' k, ⟨⟨τ, ρ, hop, hv, hk⟩, hs'⟩ => by
    simp only [Outcome.leaveCall]
    rcases hbound.leave hs'.1 hl hγ with ⟨s'', hlv, hs''⟩ | hlv
    · rw [copy_leave_ok hlv]
      exact ⟨⟨τ, ρ, hO op _ _ hop, hv, fun w x hw hx =>
        Outcome.Ok.leaveCall hbound hl hγ hP hR hret hbrk hcont hO (hk w x hw hx)⟩, hs'', hs'.2⟩
    · rw [copy_leave_error hlv]
      exact ⟨hγ, hs'.2⟩
  | .outOfFuel, _ => trivial
  | .stuck, h => h

/-- A body typed in the callee's context, run as a call: its result, the
value of a `return` (expressions.closure-boundaries), its raises and its
performances go where the call's type says, and the caller's frame stays
typed. -/
theorem invoke_ok {Γ Δ : Ctx} {η ηc : REnv} {X Xc : Exits} {P Pc : Value → Prop}
    {captured : Copy.Frame} {params ps₀ : List Param} {passed : List Passed}
    {bound : List (Name × Passed)} {body : Eval Copy.State Value}
    (hbind : bindArgs params passed = some bound) (hbound : Bound.Typed D Γ η ηc bound ps₀)
    (hcap : Frame.Typed D captured Δ ηc) (hnd : (ps₀.map Param.name).Nodup)
    (hbody : Eval.Ok D (Δ.params ps₀) ηc Xc Pc body) (hP : ∀ v, Pc v → P v)
    (hR : Xc.Raises D X) (hret : ∀ v, Xc.jumps (.ret v) → P v) (hbrk : ¬ Xc.jumps .brk)
    (hcont : ¬ Xc.jumps .cont) (hO : Xc.Performs X) :
    Eval.Ok D Γ η X P (Eval.invoke Copy.memory captured params passed body) := by
  intro γ hγ
  have hl : ∀ p ∈ ps₀, (Δ.params ps₀).lookup p.name = some ⟨p.type, p.mode = .inout⟩ :=
    fun p hp => Ctx.lookup_params hnd hp
  unfold Eval.invoke
  rw [hbind]
  dsimp only
  rcases hbound.enter hγ.1 hcap with ⟨callee, he, hc⟩ | he
  · rw [copy_enter_ok he]
    exact (hbody (callee, γ.2) ⟨hc, hγ.2⟩).leaveCall hbound hl hγ.1 hP hR hret hbrk hcont hO
  · rw [copy_enter_error he]
    exact hγ

theorem Effects.raises_body (η : REnv) (ρ : Row) (m : Bool) (result : Ty) :
    Effects.raises η ⟨ρ, m, false, result, false, false⟩ = ρ.close η := rfl

/-- A row holds no label of a `resume` when it holds no `resume` of its own:
none of its variables stands for one. -/
theorem Row.resume_not_mem_close {η : REnv} {scope : RowScope} (hη : η.Respects scope) {σ : Row}
    (hσ : σ.resume = none) (a r : Ty) : STy.resume a r ∉ σ.close η := fun h => by
  rcases Row.mem_close.1 h with ⟨E, _, hE⟩ | ⟨v, _, hv⟩ | ⟨_, _, hE⟩ | ⟨p, hp, _⟩
  · exact Ty.close_not_label η E (hE ▸ trivial)
  · exact hη.noResume v a r hv
  · exact nomatch hE
  · rw [hσ] at hp; exact nomatch hp

/-- A function value of a type whose row holds no `resume` is no clause of a
handler that takes control: the row its literal or its declaration gives holds
no label the type's lacks. -/
theorem Value.Typed.takesControl_eq_false {η : REnv} {scope : RowScope} (hη : η.Respects scope)
    {f : Value} {ps : List (Mode × Ty)} {result : Ty} {σ : Row}
    (hf : Value.Typed D f ((Ty.fn ps result σ).close η)) (hσ : σ.resume = none) :
    f.takesControl D = false := by
  cases hf with
  | @closure _ _ _ ρ _ _ _ _ ηc _ _ _ ρ₀ _ _ _ _ _ _ _ _ _ _ hσ' hρ =>
    obtain ⟨_, _, _, hc, hff⟩ := hσ'.fn_inv (D := D) rfl
    obtain ⟨-, -, rfl⟩ : _ ∧ _ ∧ _ := by injection hc with h₁ h₂ h₃; exact ⟨h₁.symm, h₂.symm, h₃.symm⟩
    simp only [Value.takesControl, hρ, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
    cases hp : ρ₀.resume with
    | none => rfl
    | some p =>
      exact absurd (hff.labels _ (Row.mem_close.2 (.inr (.inr (.inr ⟨p, hp, rfl⟩)))) trivial)
        (Row.resume_not_mem_close hη hσ p.1 p.2)
  | @function name _ _ _ d ηf hd _ _ hσ' =>
    have hσ'' : ((Ty.fn (substParamTys _ (d.params.map Param.sig)) (d.result.substTys _)
        d.row).close ηf).Fits _ := hσ'
    obtain ⟨_, _, _, hc, hff⟩ := hσ''.fn_inv (D := D) rfl
    obtain ⟨-, -, rfl⟩ : _ ∧ _ ∧ _ := by injection hc with h₁ h₂ h₃; exact ⟨h₁.symm, h₂.symm, h₃.symm⟩
    simp only [Value.takesControl, hd, Option.any_some, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none]
    cases hp : d.row.resume with
    | none => rfl
    | some p =>
      exact absurd (hff.labels _ (Row.mem_close.2 (.inr (.inr (.inr ⟨p, hp, rfl⟩)))) trivial)
        (Row.resume_not_mem_close hη hσ p.1 p.2)
  | handle _ => rfl

/-- A call of a function value, of the type the call sees, with arguments of
its parameter types: the result has the type's result type, and a raise one of
its row's error types. -/
theorem call_ok {n : Nat} (hs : Sound D n) (hD : D.Typed) {Γ : Ctx} {η : REnv} {f : Value}
    {passed : List Passed} {ps : List (Mode × Ty)} {result : Ty} {σ : Row}
    (hf : Value.Typed D f ((Ty.fn ps result σ).close η)) (hp : Passed.Typed D Γ η passed ps) :
    Eval.Ok D Γ η ⟨σ.close η, fun _ => False, performsOf D (σ.close η)⟩
      (fun v => Value.Typed D v (result.close η))
      (Eval.call D Copy.memory (eval D Copy.memory n) f passed) := by
  cases hf with
  | @closure captured _ _ _ _ _ _ Γc ηc θ ps₀ result₀ ρ₀ body₀ m τb hps hb hnd hη hty hfit hcap
      hσ _ =>
    subst hps hb
    obtain ⟨_, _, _, hc, hff⟩ := hσ.fn_inv (D := D) rfl
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by injection hc with h₁ h₂ h₃; exact ⟨h₁.symm, h₂.symm, h₃.symm⟩
    have hmatch := hff.params
    rw [closeParams_sig, closeParams_map_sig] at hmatch
    obtain ⟨bound, hbind, hbound⟩ := hp.bind hmatch
    exact invoke_ok (by rw [bindArgs_substRows]; exact hbind) hbound hcap.freeze hnd
      (hs hty hη θ) (fun v hv => hff.result v (hv.fits (hfit.close ηc))) hff.raises
      hff.result Bool.false_ne_true Bool.false_ne_true fun _ _ _ h => performsOf_of_labels hff.labels h
  | @function name types rows _ d ηf hd hδ hη hσ =>
    obtain ⟨τb, hty, hfit⟩ := (hD.fns d (Decls.mem_of_fn? hd)).instance hD.wf (Decls.mem_of_fn? hd) hδ
    have hσ' : ((Ty.fn (substParamTys (d.typeArgs types) (d.params.map Param.sig))
        (d.result.substTys (d.typeArgs types)) d.row).close ηf).Fits _ := hσ
    obtain ⟨_, _, _, hc, hff⟩ := hσ'.fn_inv (D := D) rfl
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by injection hc with h₁ h₂ h₃; exact ⟨h₁.symm, h₂.symm, h₃.symm⟩
    have hmatch := hff.params
    rw [← map_sig_substTys, closeParams_sig, closeParams_map_sig] at hmatch
    obtain ⟨bound, hbind, hbound⟩ := hp.bind hmatch
    show Eval.Ok D Γ η _ _ (match D.fn? name with
      | some d => Eval.invoke Copy.memory [] d.params passed
          (eval D Copy.memory n ((d.body.substTys (d.typeArgs types)).substRows (d.rowParams.zip rows)))
      | none => Eval.fail .stuck)
    rw [hd]
    exact invoke_ok (Δ := []) (by rw [← bindArgs_substTys (d.typeArgs types)]; exact hbind) hbound
      .nil (by simpa [Param.substTys, Function.comp_def] using hD.wf.paramNames d (Decls.mem_of_fn? hd))
      (hs hty hη _) (fun v hv => hff.result v (hv.fits (hfit.close ηf))) hff.raises
      hff.result Bool.false_ne_true Bool.false_ne_true fun _ _ _ h => performsOf_of_labels hff.labels h
  | handle hσ =>
    obtain ⟨_, h⟩ := hσ.shared_shared rfl
    simp [Ty.close] at h

/-- A call's row is within what the code around it may raise: its row fits
the row around it (effects.missing-effects), and inside a `catch` operand each of its
variables is paired with the caught type (effects.catch-around-row-variables), which the
environment keeps. -/
theorem CallAllowed.raises {scope : RowScope} {fx : Effects} {σ : Row} {η : REnv}
    (hc : CallAllowed scope fx σ) (hη : η.Respects scope) :
    Exits.Raises D ⟨σ.close η, fun _ => False, performsOf D (σ.close η)⟩ (fx.exits D η) := by
  intro e F hF he
  unfold Effects.exits Effects.raises
  cases hcatch : fx.catching with
  | false => exact ⟨F, hc.within.close η F hF, he⟩
  | true =>
    simp only [ite_true]
    rcases Row.mem_close.1 hF with ⟨E, hE, rfl⟩ | ⟨v, hv, hFv⟩
    · exact ⟨_, by simp [hc.within.raise E hE], he⟩
    · obtain ⟨E, hE, hpair⟩ := hc.paired hcatch v hv
      exact ⟨_, by simp [hc.within.raise E hE], he.fits (hη.pairs v E hpair F hFv he.not_label)⟩
    · rename_i h
      rcases h with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> exact absurd trivial he.not_label

/-- A call's row holds no label that the row around it lacks (effects.missing-effects), so
the call performs only what the code around it may. -/
theorem CallAllowed.performs {scope : RowScope} {fx : Effects} {σ : Row} {η : REnv}
    (hc : CallAllowed scope fx σ) :
    Exits.Performs ⟨σ.close η, fun _ => False, performsOf D (σ.close η)⟩ (fx.exits D η) :=
  fun _ _ _ h => performsOf_of_labels (fun x hx _ => hc.within.close η x hx) h

end

end Stilt
