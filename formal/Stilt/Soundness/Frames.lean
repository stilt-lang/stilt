import Stilt.Soundness.Outcome

/-!
# The frames of a call

A call starts once its arguments are evaluated: it pairs each parameter with
its argument, and builds the callee's frame from the captured variables, a copy
of each `let` argument and the value of each `inout` argument's place
(values.inout-argument-order). It ends by writing each `inout` parameter's final value back
to its place (values.inout-arguments). Each step keeps the frames typed, or panics on
an index out of bounds.
-/

namespace Stilt

section

variable {D : Decls}

/-- The arguments a call passes, against the parameter types that the call
sees: a value of the parameter's type for a `let` parameter, and for an
`inout` one a place of the caller's frame whose path leads to the parameter's
type exactly (effects.inout-function-arguments). -/
inductive Passed.Typed (D : Decls) (Γ : Ctx) (η : REnv) : List Passed → List (Mode × Ty) → Prop
  | nil : Passed.Typed D Γ η [] []
  | value {v : Value} {τ : Ty} {passed : List Passed} {ps : List (Mode × Ty)} :
      Value.Typed D v (τ.close η) → Passed.Typed D Γ η passed ps →
      Passed.Typed D Γ η (.value v :: passed) ((.let, τ) :: ps)
  | place {x : Name} {path : Path} {σ τ : Ty} {passed : List Passed} {ps : List (Mode × Ty)} :
      Γ.lookup x = some ⟨σ, true⟩ → PathTyped D (σ.close η) path (τ.close η) →
      Passed.Typed D Γ η passed ps → Passed.Typed D Γ η (.place x path :: passed) ((.inout, τ) :: ps)

/-- Each parameter of the callee paired with its argument, which the callee
reads at its own parameter's type, and an `inout` argument's place with the
caller's type, whose values are the callee's (values.inout-arguments and values.inout-argument-order). -/
inductive Bound.Typed (D : Decls) (Γ : Ctx) (η ηc : REnv) : List (Name × Passed) → List Param → Prop
  | nil : Bound.Typed D Γ η ηc [] []
  | value {p : Param} {v : Value} {bound : List (Name × Passed)} {ps : List Param} :
      p.mode = .let → Value.Typed D v (p.type.close ηc) → Bound.Typed D Γ η ηc bound ps →
      Bound.Typed D Γ η ηc ((p.name, .value v) :: bound) (p :: ps)
  | place {p : Param} {x : Name} {path : Path} {σ : Ty} {τ : STy} {bound : List (Name × Passed)}
      {ps : List Param} :
      p.mode = .inout → Γ.lookup x = some ⟨σ, true⟩ → PathTyped D (σ.close η) path τ →
      (∀ v, Value.Typed D v τ → Value.Typed D v (p.type.close ηc)) →
      (∀ v, Value.Typed D v (p.type.close ηc) → Value.Typed D v τ) →
      Bound.Typed D Γ η ηc bound ps → Bound.Typed D Γ η ηc ((p.name, .place x path) :: bound) (p :: ps)

theorem closeParams_sig (η : REnv) :
    ∀ ps : List Param, closeParams η (ps.map Param.sig) = ps.map fun p => (p.mode, p.type.close η)
  | [] => rfl
  | p :: ps => by simp [closeParams, Param.sig, closeParams_sig η ps]

theorem closeParams_map_sig (η : REnv) (ps : List (Mode × Ty)) :
    closeParams η ps = ps.map fun p => (p.1, p.2.close η) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [closeParams, ih]

theorem bindArgs_substRows (θ : RowSubst) :
    ∀ (ps : List Param) (args : List Passed),
      bindArgs (ps.map (Param.substRows θ)) args = bindArgs ps args
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, a :: args => by
    simp only [List.map_cons, bindArgs, Param.substRows]
    rw [bindArgs_substRows θ ps args]

theorem bindArgs_substTys (δ : TySubst) :
    ∀ (ps : List Param) (args : List Passed),
      bindArgs (ps.map (Param.substTys δ)) args = bindArgs ps args
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, a :: args => by
    simp only [List.map_cons, bindArgs, Param.substTys]
    rw [bindArgs_substTys δ ps args]

/-- Passed arguments pair with the callee's parameters, when these match the
parameters that the call sees. -/
theorem Passed.Typed.bind {Γ : Ctx} {η ηc : REnv} :
    ∀ {passed : List Passed} {ps : List (Mode × Ty)} {ps₀ : List Param},
      Passed.Typed D Γ η passed ps →
      ParamsMatch D (ps₀.map fun p => (p.mode, p.type.close ηc)) (ps.map fun p => (p.1, p.2.close η)) →
      ∃ bound, bindArgs ps₀ passed = some bound ∧ Bound.Typed D Γ η ηc bound ps₀
  | _, _, ps₀, .nil, h => by
    cases ps₀ with
    | nil => exact ⟨[], rfl, .nil⟩
    | cons => cases h
  | _, _, ps₀, .value hv hrest, h => by
    cases ps₀ with
    | nil => cases h
    | cons p ps₀ =>
      obtain ⟨mode, name, type, implicit⟩ := p
      cases mode with
      | inout => simp only [List.map_cons] at h; cases h
      | «let» =>
        simp only [List.map_cons] at h
        cases h with
        | cons _ hb' hm =>
          obtain ⟨bound, hb, ht⟩ := Passed.Typed.bind hrest hm
          exact ⟨_, by simp [bindArgs, hb], .value rfl (hb' _ hv) ht⟩
  | _, _, ps₀, .place hx hp hrest, h => by
    cases ps₀ with
    | nil => cases h
    | cons p ps₀ =>
      obtain ⟨mode, name, type, implicit⟩ := p
      cases mode with
      | «let» => simp only [List.map_cons] at h; cases h
      | inout =>
        simp only [List.map_cons] at h
        cases h with
        | cons hf hb' hm =>
          obtain ⟨bound, hb, ht⟩ := Passed.Typed.bind hrest hm
          exact ⟨_, by simp [bindArgs, hb], .place rfl hx hp hb' hf ht⟩

/-! ## The callee's frame -/

theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a :=
  rfl

theorem except_error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e :=
  rfl

theorem Ctx.params_cons (Δ : Ctx) (p : Param) (ps : List Param) :
    Δ.params (p :: ps) = (Δ.bind p.name ⟨p.type, p.mode = .inout⟩).params ps := rfl

theorem Ctx.lookup_params_not_mem {x : Name} :
    ∀ {Δ : Ctx} {ps : List Param}, x ∉ ps.map Param.name → (Δ.params ps).lookup x = Δ.lookup x
  | _, [], _ => rfl
  | Δ, p :: ps, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    show (Ctx.params (Δ.bind p.name _) ps).lookup x = _
    rw [Ctx.lookup_params_not_mem h.2]
    exact lookup_cons_ne h.1

/-- A function's or closure's parameter, named once, is bound with its type. -/
theorem Ctx.lookup_params {p : Param} :
    ∀ {Δ : Ctx} {ps : List Param}, (ps.map Param.name).Nodup → p ∈ ps →
      (Δ.params ps).lookup p.name = some ⟨p.type, p.mode = .inout⟩
  | _, [], _, hp => nomatch hp
  | Δ, q :: ps, hnd, hp => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    show (Ctx.params (Δ.bind q.name _) ps).lookup p.name = _
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [Ctx.lookup_params_not_mem hnd.1]
      simp [Ctx.lookup, Ctx.bind]
    · exact Ctx.lookup_params hnd.2 hp

/-- The start of a call builds a frame of the callee's context from the
captured frame, or panics on an `inout` place out of bounds. -/
theorem Bound.Typed.enter {Γ : Ctx} {η ηc : REnv} {γ : Copy.Frame} (hγ : Frame.Typed D γ Γ η) :
    ∀ {bound : List (Name × Passed)} {ps₀ : List Param}, Bound.Typed D Γ η ηc bound ps₀ →
      ∀ {fr : Copy.Frame} {Δ : Ctx}, Frame.Typed D fr Δ ηc →
        (∃ fr', Copy.enter γ fr bound = .ok fr' ∧ Frame.Typed D fr' (Δ.params ps₀) ηc) ∨
          Copy.enter γ fr bound = .error (.panic .bounds)
  | _, _, .nil, fr, _, hfr => .inl ⟨fr, rfl, hfr⟩
  | _, _, .value (p := p) _ hv hrest, fr, Δ, hfr => by
    have := Bound.Typed.enter hγ hrest (fr := (p.name, _) :: fr)
      (Δ := Δ.bind p.name ⟨p.type, p.mode = .inout⟩) (.cons hv hfr)
    simpa [Copy.enter, List.foldlM_cons, Ctx.params_cons] using this
  | _, _, .place (p := p) _ hx hpath hin _ hrest, fr, Δ, hfr => by
    rcases hγ.read hx hpath with ⟨w, hw, hwt⟩ | hw
    · have := Bound.Typed.enter hγ hrest (fr := (p.name, w) :: fr)
        (Δ := Δ.bind p.name ⟨p.type, p.mode = .inout⟩) (.cons (hin w hwt) hfr)
      simpa [Copy.enter, List.foldlM_cons, hw, Ctx.params_cons, except_ok_bind] using this
    · exact .inr (by simp [Copy.enter, List.foldlM_cons, hw]; rfl)

/-- The end of a call writes each `inout` parameter's final value back to its
place, which keeps the caller's frame typed, or panics. -/
theorem Bound.Typed.leave {Γ Γc : Ctx} {η ηc : REnv} {callee : Copy.Frame}
    (hc : Frame.Typed D callee Γc ηc) :
    ∀ {bound : List (Name × Passed)} {ps₀ : List Param}, Bound.Typed D Γ η ηc bound ps₀ →
      (∀ p ∈ ps₀, Γc.lookup p.name = some ⟨p.type, p.mode = .inout⟩) →
      ∀ {fr : Copy.Frame}, Frame.Typed D fr Γ η →
        (∃ fr', Copy.leave fr callee bound = .ok fr' ∧ Frame.Typed D fr' Γ η) ∨
          Copy.leave fr callee bound = .error (.panic .bounds)
  | _, _, .nil, _, fr, hfr => .inl ⟨fr, rfl, hfr⟩
  | _, _, .value _ _ hrest, hl, fr, hfr => by
    have := Bound.Typed.leave hc hrest (fun p hp => hl p (List.mem_cons_of_mem _ hp)) hfr
    simpa [Copy.leave, List.foldlM_cons] using this
  | _, _, .place (p := p) _ hx hpath _ hout hrest, hl, fr, hfr => by
    have hl' := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    rcases hc.read (hl p List.mem_cons_self) .nil with ⟨w, hw, hwt⟩ | hw
    · rcases hfr.write hx hpath (hout w hwt) with ⟨fr', hfr', hfr't⟩ | hfr'
      · have := Bound.Typed.leave hc hrest hl' hfr't
        simpa [Copy.leave, List.foldlM_cons, hw, hfr', except_ok_bind] using this
      · exact .inr (by simp [Copy.leave, List.foldlM_cons, hw, hfr', except_ok_bind]; rfl)
    · exact .inr (by simp [Copy.leave, List.foldlM_cons, hw]; rfl)

end

end Stilt
