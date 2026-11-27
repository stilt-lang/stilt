import Stilt.Quiet.With

/-!
# The forms of expressions keep the world's output and input

Each form of expression whose row reads as no `io`, evaluated with fuel `n + 1`, keeps the
world when its parts, which the evaluator runs with fuel `n`, do. An operation is no read or
write of the world (`HasType.op`), and a call's callee has a row that fits within the row
around it, so it reads as no `io` either (effects.missing-effects).
-/

namespace Stilt

section

variable {D : Decls} {n : Nat} (hq : Quiet D n) (hs : Sound D n) {scope : RowScope} {η : REnv}
  (hη : η.Respects scope) (θ : RowSubst) {Γ : Ctx} {fx : Effects}
  (hio : STy.io ∉ fx.row.close η)
include hq hs hη hio

theorem seq_keeps {a b : Expr} {σ τ : Ty} (ha : HasType D scope Γ fx a σ)
    (hb : HasType D scope Γ fx b τ) :
    Eval.KeepsIo D Γ η (fx.exits D η) (eval D Copy.memory (n + 1) ((Expr.seq a b).substRows θ)) :=
  Eval.KeepsIo.bind (hs ha hη θ) (hq ha hη hio θ) fun _ _ => hq hb hη hio θ

theorem ite_keeps {c a b : Expr} {σc σa σb τ : Ty} (hc : HasType D scope Γ fx c σc)
    (hfc : Fits σc .bool) (ha : HasType D scope Γ fx a σa) (hb : HasType D scope Γ fx b σb) :
    Eval.KeepsIo D Γ η (fx.exits D η) (eval D Copy.memory (n + 1) ((Expr.if c τ a b).substRows θ)) := by
  refine Eval.KeepsIo.bind (P := fun _ => True) (Eval.Ok.bind (hs hc hη θ) fun v hv => ?_)
    (Eval.KeepsIo.bindAny (hq hc hη hio θ) fun _ _ => Outcome.KeepsIo.asBool) fun k _ => ?_
  · obtain ⟨k, rfl⟩ := (hv.fits (hfc.close η)).bool_inv
    exact Eval.Ok.pure trivial
  · cases k
    · exact hq hb hη hio θ
    · exact hq ha hη hio θ

theorem letIn_keeps {x : Name} {τ σ σ' : Ty} {init body : Expr} (hi : HasType D scope Γ fx init σ)
    (hfit : Fits σ τ) (hb : HasType D scope (Γ.bind x ⟨τ, false⟩) fx body σ') :
    Eval.KeepsIo D Γ η (fx.exits D η)
      (eval D Copy.memory (n + 1) ((Expr.letIn x τ init body).substRows θ)) :=
  Eval.KeepsIo.bind (hs hi hη θ) (hq hi hη hio θ) fun v hv => by
    rw [Eval.withInit_eq_withVar _ _ (Expr.substRows_ne_move hi.not_move θ)]
    exact Eval.KeepsIo.withVar (b := ⟨τ, false⟩) (hv.fits (hfit.close η)) (hq hb hη hio θ)

theorem varIn_keeps {x : Name} {τ σ σ' : Ty} {init body : Expr} (hi : HasType D scope Γ fx init σ)
    (hfit : Fits σ τ) (hb : HasType D scope (Γ.bind x ⟨τ, true⟩) fx body σ') :
    Eval.KeepsIo D Γ η (fx.exits D η)
      (eval D Copy.memory (n + 1) ((Expr.varIn x τ init body).substRows θ)) :=
  Eval.KeepsIo.bind (hs hi hη θ) (hq hi hη hio θ) fun v hv => by
    rw [Eval.withInit_eq_withVar _ _ (Expr.substRows_ne_move hi.not_move θ)]
    exact Eval.KeepsIo.withVar (b := ⟨τ, true⟩) (hv.fits (hfit.close η)) (hq hb hη hio θ)

theorem tryCatch_keeps {e h : Expr} {E x τ σ σ'}
    (he : HasType D scope Γ ⟨fx.row.withRaise E, true, true, fx.result, fx.breaks, fx.continues⟩ e σ)
    (hh : HasType D scope (Γ.bind x ⟨E, false⟩) fx h σ') :
    Eval.KeepsIo D Γ η (fx.exits D η)
      (eval D Copy.memory (n + 1) ((Expr.tryCatch e E x h τ).substRows θ)) := by
  refine Eval.KeepsIo.handle (hs he hη θ) (hq he hη (Row.io_not_mem_withRaise hio) θ)
    (fun err F hF herr => ?_) fun _ _ _ h => performsOf_of_labels Row.labels_withRaise h
  unfold Effects.exits at hF
  rw [Effects.raises_catch, List.mem_singleton] at hF
  subst hF
  exact Eval.KeepsIo.withVar (b := ⟨E, false⟩) herr (hq hh hη hio θ)

omit hs in
theorem field_keeps {e : Expr} {f : Name} {σ : Ty} (he : HasType D scope Γ fx e σ) :
    Eval.KeepsIo D Γ η (fx.exits D η) (eval D Copy.memory (n + 1) ((Expr.field e f).substRows θ)) :=
  Eval.KeepsIo.bindAny (hq he hη hio θ) fun _ _ => Outcome.KeepsIo.ofExcept_any

theorem index_keeps {e i : Expr} {τ σ : Ty} (he : HasType D scope Γ fx e (.list τ))
    (hi : HasType D scope Γ fx i σ) (hfit : Fits σ .i64) :
    Eval.KeepsIo D Γ η (fx.exits D η) (eval D Copy.memory (n + 1) ((Expr.index e i).substRows θ)) := by
  refine Eval.KeepsIo.bind (hs he hη θ) (hq he hη hio θ) fun v _ => ?_
  refine Eval.KeepsIo.bind (P := fun _ => True) (Eval.Ok.bind (hs hi hη θ) fun k hk => ?_)
    (Eval.KeepsIo.bindAny (hq hi hη hio θ) fun _ _ => Outcome.KeepsIo.asInt)
    fun _ _ _ _ => Outcome.KeepsIo.ofExcept_any
  obtain ⟨k, rfl⟩ := (hk.fits (hfit.close η)).i64_inv
  exact Eval.Ok.pure trivial

theorem apply_keeps (hD : D.Typed) {callee : Expr} {args : List Arg} {ps : List (Mode × Ty)}
    {result : Ty} {σ : Row} (hc : HasType D scope Γ fx callee (.fn ps result σ))
    (ha : ArgsFit D scope Γ fx args ps) (hallow : CallAllowed scope fx σ) :
    Eval.KeepsIo D Γ η (fx.exits D η)
      (eval D Copy.memory (n + 1) ((Expr.call callee args result).substRows θ)) :=
  Eval.KeepsIo.bind (hs hc hη θ) (hq hc hη hio θ) fun _ hf =>
    Eval.KeepsIo.bind (ArgsFit.ok hs hD.wf hη θ ha) (ArgsFit.keeps hq hs hη θ hD.wf ha hio)
      fun _ hp => by
        unfold Eval.callAs
        rw [hf.takesControl_eq_false hη hallow.resume]
        exact (call_keeps hq hD hf hp fun h => hio (hallow.within.close η _ h)).mono
          hallow.performs

theorem assign_keeps (hD : D.WellFormed) {p : Place} {e : Expr} {τ σ : Ty}
    (hp : PlaceFits D scope Γ fx p τ) (he : HasType D scope Γ fx e σ) :
    Eval.KeepsIo D Γ η (fx.exits D η) (eval D Copy.memory (n + 1) ((Expr.assign p e).substRows θ)) := by
  obtain ⟨x, path⟩ := p
  obtain ⟨_, hpath⟩ := hp
  refine Eval.KeepsIo.bind (PathFits.ok hs hD hη θ hpath) (PathFits.keeps hq hs hη θ hD hpath hio)
    fun _ _ => Eval.KeepsIo.bind (hs he hη θ) (hq he hη hio θ) fun _ _ =>
      Eval.KeepsIo.bindAny (Eval.KeepsIo.update fun γ γ' h => ?_) fun _ _ => rfl
  revert h
  show (·, γ.2) <$> Copy.write _ _ _ _ = _ → _
  cases Copy.write γ.1 x _ _ with
  | error => intro h; cases h
  | ok fr => intro h; cases h; rfl

theorem op_keeps {o : Op} {es : List Expr} {τs : List Ty} (hes : ExprsFit D scope Γ fx es τs)
    (hoio : o.io = true → fx.row.io = true) :
    Eval.KeepsIo D Γ η (fx.exits D η) (eval D Copy.memory (n + 1) ((Expr.op o es).substRows θ)) := by
  have ho : o.io = false := by
    cases h : o.io
    · rfl
    · exact absurd (Row.mem_close.2 (.inr (.inr (.inr (.inr ⟨hoio h, rfl⟩))))) hio
  exact Eval.KeepsIo.bindAny (ExprsFit.keeps hq hs hη θ hes hio) fun _ _ =>
    Outcome.KeepsIo.world (fun _ _ _ h => Op.run_io ho h) _

end

end Stilt
