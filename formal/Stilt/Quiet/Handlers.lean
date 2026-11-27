import Stilt.Quiet.Forms

/-!
# Handlers keep the world's output and input

The clause of a handler for an operation is a closure whose row, but for its `resume`, fits
within the row around the `with` (handlers.handler-literals). Around code whose row reads as
no `io`, its row reads as none either, so its call keeps the world, and so does the `with`.
-/

namespace Stilt

section

variable {D : Decls} {n : Nat} (hq : Quiet D n) (hs : Sound D n) {scope : RowScope} {η : REnv}
  (hη : η.Respects scope) (θ : RowSubst) {Γ : Ctx} {fx : Effects}
  (hio : STy.io ∉ fx.row.close η)
include hq hs hη hio

/-- A handler's clause for an operation of its effect, called on an argument of the
operation's type, ends as `ClauseOk` says and keeps the world. -/
theorem clause_keeps (hD : D.Typed) {E : Name} {eff : EffectDecl} {R : Name} {r : RecordDecl}
    {hv : Value} {control : Option Ty} {τw : Ty} (hEne : E ≠ Operation.resume.effect)
    (heff : D.effect? E = some eff) (hr : D.record? R = some r)
    (hh : Value.Typed D hv (.record R [])) (hfits : HandlerFits scope fx eff r.fields control)
    (hctl : ∀ τ, control = some τ → τ = τw) {op : Operation} {τ ρ : STy} {v : Value}
    {γ : Copy.State} (hE : op.effect = E)
    (hop : performsOf D ((fx.row.withEffect E).close η) op τ ρ)
    (hvt : Value.Typed D v τ) (hγ : State.Typed D γ Γ η) :
    ∃ c, hv.clause? op.name = some c ∧ ClauseKeeps D Γ η (fx.exits D η) (τw.close η) ρ
      control.isSome (Eval.callAs D Copy.memory (eval D Copy.memory n) control.isSome c [.value v] γ)
      γ.2.io := by
  have hne : op ≠ .resume := fun h => hEne (by rw [← hE, h])
  obtain ⟨_, A, B, hAB, rfl, rfl⟩ := (performsOf_of_ne hne).1 hop
  have ho : eff.ops.lookup op.name = some (A, B) := by
    simpa [Decls.operation?, hE, heff] using hAB
  obtain ⟨c, ρc, hc, hct, hcl, hres, hcall⟩ := HandlerFits.clause hD.wf hr hh hfits ho η
  obtain ⟨hA, hrt, hρc⟩ := hcl.fn_close η
  have hok := call_ok hs hD hct (.value (hA ▸ hvt) .nil) γ hγ
  have hkeep := call_keeps hq hD hct (.value (hA ▸ hvt) .nil)
    (fun h => hio (hcall.within.close η _ (Row.close_dropResume h fun _ _ h' => nomatch h'))) γ hγ
  refine ⟨c, hc, ?_⟩
  unfold ClauseKeeps Eval.callAs
  cases control with
  | none =>
    rw [hct.takesControl_eq_false hη hres]
    have hcall' : CallAllowed scope fx ρc := Row.dropResume_eq hres ▸ hcall
    exact ⟨hok.mono (fun w hw => hrt ▸ hw) (hcall'.raises hη) (fun _ h => h.elim) hcall'.performs,
      hkeep.mono hcall'.performs⟩
  | some τc =>
    obtain rfl := hctl τc rfl
    simp only [Option.isSome_some, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    refine ⟨⟨ρc.close η, fun _ => False, performsOf D (ρc.close η)⟩, fun e F hF he => (hcall.raises hη) e F (Row.close_dropResume hF fun a r h => ?_) he,
      fun _ h => h.elim, fun op τ ρ hne h => hcall.performs op τ ρ (performsOf_dropResume rfl hne h),
      fun τ' ρ' h => ?_, hok, hkeep⟩
    · subst h
      exact he.not_label trivial
    · obtain ⟨B', R', hm, rfl, rfl⟩ := (performsOf_resume (D := D)).1 h
      rw [hρc] at hm
      obtain ⟨rfl, rfl⟩ := Row.resume_of_close hres hm
      exact ⟨fun _ hu => hu, fun _ hr => hrt ▸ hr⟩

omit hq hs hη hio in
/-- An operation of a `with`'s effect gives values of one type. -/
theorem withEffect_unique {E : Name} (hEne : E ≠ Operation.resume.effect) {op : Operation}
    {τ ρ τ' ρ' : STy} (hE : op.effect = E)
    (h : performsOf D ((fx.row.withEffect E).close η) op τ ρ)
    (h' : performsOf D ((fx.row.withEffect E).close η) op τ' ρ') : ρ' = ρ :=
  performsOf_unique (fun hr => hEne (by rw [← hE, hr])) h h'

theorem withH_keeps (hD : D.Typed) {E : Name} {eff : EffectDecl} {h b : Expr} {R : Name}
    {r : RecordDecl} {τ : Ty} (hEne : E ≠ Operation.resume.effect) (heff : D.effect? E = some eff)
    (hh : HasType D scope Γ fx h (.record R [])) (hr : D.record? R = some r)
    (hfits : HandlerFits scope fx eff r.fields none)
    (hb : HasType D scope Γ { fx with row := fx.row.withEffect E } b τ) :
    Eval.KeepsIo D Γ η (fx.exits D η)
      (eval D Copy.memory (n + 1) ((Expr.withH E false h b).substRows θ)) :=
  Eval.KeepsIo.bind (hs hh hη θ) (hq hh hη hio θ) fun _ hhv γ hγ =>
    Outcome.KeepsIo.letGo _ (Outcome.KeepsIo.handleWith Effects.raises_withEffect (fun _ h => h)
      (fun _ _ _ hne hp => performsOf_withEffect hne hp)
      (fun _ _ _ _ _ hE hp hp' => withEffect_unique hEne hE hp hp')
      (fun _ _ _ _ _ hE hp hvt hγ' =>
        clause_keeps hq hs hη hio hD hEne heff hr hhv hfits (fun _ h => nomatch h) hE hp hvt hγ')
      (hs hb hη θ γ hγ) (hq hb hη (Row.io_not_mem_withEffect hio) θ γ hγ))

theorem withControl_keeps (hD : D.Typed) {E : Name} {eff : EffectDecl} {h b : Expr} {R : Name}
    {r : RecordDecl} {σ τ : Ty} (hEne : E ≠ Operation.resume.effect)
    (heff : D.effect? E = some eff) (hh : HasType D scope Γ fx h (.record R []))
    (hr : D.record? R = some r) (hfits : HandlerFits scope fx eff r.fields (some τ))
    (hb : HasType D scope Γ { fx with row := fx.row.withEffect E } b σ) (hfit : Fits σ τ) :
    Eval.KeepsIo D Γ η (fx.exits D η)
      (eval D Copy.memory (n + 1) ((Expr.withH E true h b).substRows θ)) :=
  Eval.KeepsIo.bind (hs hh hη θ) (hq hh hη hio θ) fun _ hhv γ hγ =>
    Outcome.KeepsIo.letGo _ (Outcome.KeepsIo.handleWith Effects.raises_withEffect (fun _ h => h)
      (fun _ _ _ hne hp => performsOf_withEffect hne hp)
      (fun _ _ _ _ _ hE hp hp' => withEffect_unique hEne hE hp hp')
      (fun _ _ _ _ _ hE hp hvt hγ' =>
        clause_keeps hq hs hη hio hD hEne heff hr hhv hfits (fun _ h => (Option.some.inj h).symm)
          hE hp hvt hγ')
      ((hs hb hη θ γ hγ).mono (fun _ hv => hv.fits (hfit.close η)) (fun _ F hF he => ⟨F, hF, he⟩)
        (fun _ h => h) fun _ _ _ h => h)
      (hq hb hη (Row.io_not_mem_withEffect hio) θ γ hγ))

end

end Stilt
