import Stilt.Soundness.Methods
import Stilt.Strengthen

/-!
# The forms of expressions

Each form of expression, evaluated with fuel `n + 1`, ends soundly when its
parts, which the evaluator runs with fuel `n`, do. A use of a function makes a
value whose environment keeps its signature's promises: effects.one-error-type and
effects.passing-to-paired-variables, as `PassesOnPairs` states them, give that from the use's own
environment.
-/

namespace Stilt

/-- A raise's error type is one that its effects allow. -/
theorem Effects.mem_raises {η : REnv} {fx : Effects} {E : Ty} (h : fx.row.raise = some E) :
    E.close η ∈ fx.raises η := by
  unfold Effects.raises
  cases fx.catching <;> simp [h, Row.mem_close]

theorem Effects.raises_catch (η : REnv) (ρ : Row) (E result : Ty) (b c : Bool) :
    Effects.raises η ⟨ρ.withRaise E, true, true, result, b, c⟩ = [E.close η] := rfl

section

variable {D : Decls} {n : Nat} (hs : Sound D n) {scope : RowScope} {η : REnv}
  (hη : η.Respects scope) (θ : RowSubst) {Γ : Ctx} {fx : Effects}
include hs hη

theorem seq_ok {a b : Expr} {σ τ : Ty} (ha : HasType D scope Γ fx a σ) (hb : HasType D scope Γ fx b τ) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (τ.close η))
      (eval D Copy.memory (n + 1) ((Expr.seq a b).substRows θ)) :=
  Eval.Ok.bind (P := fun _ => True)
    ((hs ha hη θ).mono (fun _ _ => trivial) (fun _ F hF he => ⟨F, hF, he⟩) fun _ h => h)
    fun _ _ => hs hb hη θ

theorem raise_ok {e : Expr} {E σ : Ty} (hE : fx.row.raise = some E) (he : HasType D scope Γ fx e σ)
    (hfit : Fits σ E) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (Ty.never.close η))
      (eval D Copy.memory (n + 1) ((Expr.raise e).substRows θ)) :=
  Eval.Ok.bind (hs he hη θ) fun _ hv =>
    Eval.Ok.throw (Effects.mem_raises hE) (hv.fits (hfit.close η))

theorem if_ok {c a b : Expr} {τ σc σa σb : Ty} (hc : HasType D scope Γ fx c σc) (hfc : Fits σc .bool)
    (ha : HasType D scope Γ fx a σa) (hfa : Fits σa τ) (hb : HasType D scope Γ fx b σb)
    (hfb : Fits σb τ) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (τ.close η))
      (eval D Copy.memory (n + 1) ((Expr.if c τ a b).substRows θ)) := by
  refine Eval.Ok.bind (P := fun _ => True) (Eval.Ok.bind (hs hc hη θ) fun v hv => ?_) fun k _ => ?_
  · obtain ⟨k, rfl⟩ := (hv.fits (hfc.close η)).bool_inv
    exact Eval.Ok.pure trivial
  · cases k
    · exact (hs hb hη θ).mono (fun v hv => hv.fits (hfb.close η))
        (fun _ F hF he => ⟨F, hF, he⟩) fun _ h => h
    · exact (hs ha hη θ).mono (fun v hv => hv.fits (hfa.close η))
        (fun _ F hF he => ⟨F, hF, he⟩) fun _ h => h

omit hs hη in
theorem var_ok {x : Name} {τ : Ty} {mutable : Bool} (hx : Γ.lookup x = some ⟨τ, mutable⟩) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (τ.close η))
      (eval D Copy.memory (n + 1) ((Expr.var x).substRows θ)) :=
  Eval.Ok.inspect fun _ hγ => hγ.1.read hx .nil

theorem letIn_ok {x : Name} {τ σ σ' : Ty} {init body : Expr} (hi : HasType D scope Γ fx init σ)
    (hfit : Fits σ τ) (hb : HasType D scope (Γ.bind x ⟨τ, false⟩) fx body σ') :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (σ'.close η))
      (eval D Copy.memory (n + 1) ((Expr.letIn x τ init body).substRows θ)) :=
  Eval.Ok.bind (hs hi hη θ) fun v hv => by
    rw [Eval.withInit_eq_withVar _ _ (Expr.substRows_ne_move hi.not_move θ)]
    exact Eval.Ok.withVar (b := ⟨τ, false⟩) (hv.fits (hfit.close η)) (hs hb hη θ)

theorem varIn_ok {x : Name} {τ σ σ' : Ty} {init body : Expr} (hi : HasType D scope Γ fx init σ)
    (hfit : Fits σ τ) (hb : HasType D scope (Γ.bind x ⟨τ, true⟩) fx body σ') :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (σ'.close η))
      (eval D Copy.memory (n + 1) ((Expr.varIn x τ init body).substRows θ)) :=
  Eval.Ok.bind (hs hi hη θ) fun v hv => by
    rw [Eval.withInit_eq_withVar _ _ (Expr.substRows_ne_move hi.not_move θ)]
    exact Eval.Ok.withVar (b := ⟨τ, true⟩) (hv.fits (hfit.close η)) (hs hb hη θ)

theorem tryCatch_ok {e h : Expr} {E x τ σ σ'}
    (he : HasType D scope Γ ⟨fx.row.withRaise E, true, true, fx.result, fx.breaks, fx.continues⟩ e σ)
    (hfe : Fits σ τ) (hh : HasType D scope (Γ.bind x ⟨E, false⟩) fx h σ') (hfh : Fits σ' τ) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (τ.close η))
      (eval D Copy.memory (n + 1) ((Expr.tryCatch e E x h τ).substRows θ)) := by
  refine Eval.Ok.handle ((hs he hη θ).mono (fun v hv => hv.fits (hfe.close η))
    (fun e F hF he => ⟨F, hF, he⟩) fun _ h => h) (fun err F hF herr => ?_) (fun _ h => h)
    fun _ _ _ h => performsOf_of_labels Row.labels_withRaise h
  unfold Effects.exits at hF
  rw [Effects.raises_catch, List.mem_singleton] at hF
  subst hF
  exact Eval.Ok.withVar (b := ⟨E, false⟩) herr
    ((hs hh hη θ).mono (fun v hv => hv.fits (hfh.close η)) (fun _ F hF he => ⟨F, hF, he⟩)
      fun _ h => h)

theorem field_ok (hD : D.WellFormed) {e : Expr} {R : Name} {args : List Ty} {r : RecordDecl}
    {f : Name} {τ : Ty} (he : HasType D scope Γ fx e (.record R args)) (hR : D.record? R = some r)
    (hf : (r.fieldsAt args).lookup f = some τ) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (τ.close η))
      (eval D Copy.memory (n + 1) ((Expr.field e f).substRows θ)) := by
  refine Eval.Ok.bind (hs he hη θ) fun v hv => Eval.Ok.ofExcept ?_
  obtain ⟨τ₀, hf₀, hτ⟩ := hD.close_fieldsAt hR hf η
  rw [hτ]
  exact (PathTyped.field hR hf₀ .nil).get hv

theorem index_ok {e i : Expr} {τ σ : Ty} (he : HasType D scope Γ fx e (.list τ))
    (hi : HasType D scope Γ fx i σ) (hfit : Fits σ .i64) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (τ.close η))
      (eval D Copy.memory (n + 1) ((Expr.index e i).substRows θ)) := by
  refine Eval.Ok.bind (hs he hη θ) fun v hv => ?_
  refine Eval.Ok.bind (P := fun _ => True) (Eval.Ok.bind (hs hi hη θ) fun k hk => ?_)
    fun k _ => Eval.Ok.ofExcept ((PathTyped.index (k := k) .nil).get hv)
  obtain ⟨k, rfl⟩ := (hk.fits (hfit.close η)).i64_inv
  exact Eval.Ok.pure trivial

omit hs in
theorem fnRef_ok (hD : D.WellFormed) {f : Name} {d : FnDecl} {types : List Ty} {rows : List Row}
    (hd : D.fn? f = some d) (hlen : rows.length = d.rowParams.length)
    (hinst : d.type.InstantiableBy (d.rowParams.zip rows)) (hres : ∀ ρ ∈ rows, ρ.resume = none)
    (hpass : PassesOnPairs scope d (d.rowParams.zip rows))
    (htys : TypeArgsFit D scope d.typeParams types) :
    Eval.Ok D Γ η (fx.exits D η)
      (fun v => Value.Typed D v
        (((d.type.substTys (d.typeArgs types)).substRows (d.rowParams.zip rows)).close η))
      (eval D Copy.memory (n + 1) ((Expr.fnRef f types rows).substRows θ)) := by
  have hδ := TypeArgsFit.fits hD (Decls.mem_of_fn? hd) hη.types htys
  have hv : Value.Typed D (Value.function f types (rows.map (Row.substRows θ)))
      (((d.type.substTys (d.typeArgs types)).substRows (d.rowParams.zip rows)).close η) :=
    .function hd hδ (hη.compose hD (Decls.mem_of_fn? hd) hlen hinst hres hpass)
      (.of_eqv (Ty.close_substRows _ η _ (hinst.substTys hδ.ground)).symm)
  show Eval.Ok D Γ η _ _ (pure (Value.function f (substTysRows θ types) (rows.map (Row.substRows θ))))
  rw [htys.substRows θ]
  exact Eval.Ok.pure hv

omit hs hη in
/-- The newest bindings of a frame are typed by the newest of its context. -/
theorem Frame.Typed.newestOf :
    ∀ (keep : Name → Bool) {γ : Copy.Frame} {Γ : Ctx} {η : REnv}, Frame.Typed D γ Γ η →
      Frame.Typed D (Stilt.newestOf keep γ) (Stilt.newestOf keep Γ) η
  | _, _, _, _, .nil => .nil
  | keep, _, _, _, .cons (x := x) hv hrest => by
    by_cases hk : keep x = true
    · simp only [Stilt.newestOf, hk, ↓reduceIte]
      exact .cons hv (Frame.Typed.newestOf _ hrest)
    · simp only [Stilt.newestOf, hk, Bool.false_eq_true, ↓reduceIte]
      exact Frame.Typed.newestOf _ hrest

omit hs hη in
/-- The frame of what a closure captures is typed by the context of it. -/
theorem Frame.Typed.captureOf {ps : List Param} {body : Expr} {γ : Copy.Frame} {Γ : Ctx}
    {η : REnv} (h : Frame.Typed D γ Γ η) :
    Frame.Typed D (Stilt.captureOf ps body γ) (Stilt.captureOf ps body Γ) η :=
  h.newestOf _

omit hs in
theorem closure_ok {ps : List Param} {result : Ty} {ρ : Row} {body : Expr} {σ : Ty}
    (hnd : (ps.map Param.name).Nodup)
    (hb : HasType D scope (Γ.freeze.params ps) ⟨ρ, fx.marked, false, result, false, false⟩ body σ)
    (hfit : Fits σ result) :
    Eval.Ok D Γ η (fx.exits D η)
      (fun v => Value.Typed D v ((Ty.fn (ps.map Param.sig) result ρ).close η))
      (eval D Copy.memory (n + 1) ((Expr.closure ps result ρ body).substRows θ)) :=
  Eval.Ok.bind (Eval.Ok.inspect (P := fun c => Frame.Typed D c (Stilt.captureOf ps body Γ) η)
      fun γ hγ => .inl ⟨Stilt.captureOf ps body γ.1, by rw [Expr.captures_substRows]; rfl,
        hγ.1.captureOf⟩)
    fun _ hc => Eval.Ok.pure (.closure rfl rfl hnd hη (HasType.captured (result := result) (ρ := ρ) hb)
        hfit hc (.refl _) (Row.substRows_resume θ ρ))

theorem apply_ok (hD : D.Typed) {callee : Expr} {args : List Arg} {ps : List (Mode × Ty)}
    {result : Ty} {σ : Row} (hc : HasType D scope Γ fx callee (.fn ps result σ))
    (ha : ArgsFit D scope Γ fx args ps) (hallow : CallAllowed scope fx σ) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (result.close η))
      (eval D Copy.memory (n + 1) ((Expr.call callee args result).substRows θ)) :=
  Eval.Ok.bind (hs hc hη θ) fun _ hf =>
    Eval.Ok.bind (ArgsFit.ok hs hD.wf hη θ ha) fun _ hp => by
      unfold Eval.callAs
      rw [hf.takesControl_eq_false hη hallow.resume]
      exact (call_ok hs hD hf hp).mono (fun _ h => h) (hallow.raises hη) (fun _ h => h.elim)
        hallow.performs

theorem assign_ok (hD : D.WellFormed) {p : Place} {e : Expr} {τ σ : Ty}
    (hp : PlaceFits D scope Γ fx p τ) (he : HasType D scope Γ fx e σ) (hfit : Fits σ τ) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (Ty.unit.close η))
      (eval D Copy.memory (n + 1) ((Expr.assign p e).substRows θ)) := by
  obtain ⟨x, path⟩ := p
  obtain ⟨hx, hpath⟩ := hp
  exact Eval.Ok.bind (PathFits.ok hs hD hη θ hpath) fun _ hpth =>
    Eval.Ok.bind (hs he hη θ) fun _ hv =>
      Eval.Ok.bind (Eval.Ok.update fun γ hγ => (hγ.1.write hx hpth (hv.fits (hfit.close η))).imp
          (fun ⟨γ', h, ht⟩ => ⟨(γ', γ.2), by show (·, γ.2) <$> Copy.write _ _ _ _ = _; rw [h]; rfl, ht, hγ.2⟩)
          (fun h => by show (·, γ.2) <$> Copy.write _ _ _ _ = _; rw [h]; rfl))
        fun _ _ => Eval.Ok.pure .unit

theorem try_ok {e : Expr} {τ : Ty} (he : HasType D scope Γ { fx with marked := true } e τ) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (τ.close η))
      (eval D Copy.memory (n + 1) ((Expr.try e).substRows θ)) :=
  hs he hη θ

end

end Stilt
