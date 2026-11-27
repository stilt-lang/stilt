import Stilt.Quiet.Steps

/-!
# Calls that keep the world's output and input

A call of a function value whose type's row reads as no `io` runs a body whose own row reads
as none: a closure's literal, or a declared function's signature, holds no label the type's
row lacks (`FnFits.labels`). Starting a call and ending it change frames alone, and the
caller goes on in the world the body ended in, so the call keeps what the body kept.
-/

namespace Stilt

variable {D : Decls} {α : Type} {X : Exits}

/-- A fault at a state keeps that state's world. -/
theorem Outcome.KeepsIo.fault {f : Fault} {s : Copy.State} {c} (h : s.2.io = c) :
    (Outcome.fault f s : Outcome Copy.State α).KeepsIo D X c := by
  cases f
  · exact h
  · trivial

theorem copy_leave_world {γ s' s'' : Copy.State} {bound : List (Name × Passed)}
    (h : Copy.memory.leave γ s' bound = .ok s'') : s''.2 = s'.2 := by
  revert h
  show (·, s'.2) <$> Copy.leave γ.1 s'.1 bound = _ → _
  cases Copy.leave γ.1 s'.1 bound with
  | error => intro h; cases h
  | ok fr => intro h; cases h; rfl

/-- A callee's outcome left as its call's keeps what the callee kept. -/
theorem Outcome.KeepsIo.leaveCall {Xc : Exits} {bound : List (Name × Passed)} {γ : Copy.State}
    (hO : Xc.Performs X) :
    ∀ {o : Outcome Copy.State Value} {c}, o.KeepsIo D Xc c →
      (o.leaveCall Copy.memory bound γ).KeepsIo D X c
  | .done _ _, _, hk | .raised _ _, _, hk | .jumped (.ret _) _, _, hk | .panicked _ _, _, hk => by
    simp only [Outcome.leaveCall]
    split
    · rename_i h
      exact (congrArg World.io (copy_leave_world h)).trans hk
    · exact Outcome.KeepsIo.fault hk
  | .jumped .brk _, _, _ | .jumped .cont _, _, _ => trivial
  | .performed _ _ _ _, _, ⟨hc, hk⟩ => by
    simp only [Outcome.leaveCall]
    split
    · rename_i h
      exact ⟨(congrArg World.io (copy_leave_world h)).trans hc, fun w x hx hw =>
        Outcome.KeepsIo.leaveCall hO (hk w x hx fun τ ρ h' hv => hw τ ρ (hO _ _ _ h') hv)⟩
    · exact Outcome.KeepsIo.fault hc
  | .outOfFuel, _, _ | .stuck, _, _ => trivial

/-- A body run as a call keeps the world when the body does, from each typed state of the
callee's context. -/
theorem invoke_keeps {Γ Δ : Ctx} {η ηc : REnv} {Xc : Exits} {captured : Copy.Frame}
    {params ps₀ : List Param} {passed : List Passed} {bound : List (Name × Passed)}
    {body : Eval Copy.State Value} (hbind : bindArgs params passed = some bound)
    (hbound : Bound.Typed D Γ η ηc bound ps₀) (hcap : Frame.Typed D captured Δ ηc)
    (hbody : Eval.KeepsIo D (Δ.params ps₀) ηc Xc body) (hO : Xc.Performs X) :
    Eval.KeepsIo D Γ η X (Eval.invoke Copy.memory captured params passed body) := by
  intro γ hγ
  unfold Eval.invoke
  rw [hbind]
  dsimp only
  rcases hbound.enter hγ.1 hcap with ⟨callee, he, hc⟩ | he
  · rw [copy_enter_ok he]
    exact (hbody (callee, γ.2) ⟨hc, hγ.2⟩).leaveCall hO
  · rw [copy_enter_error he]
    exact Outcome.KeepsIo.fault rfl

/-- A call of a function value whose type's row reads as no `io`, with arguments of its
parameter types, keeps the world's output, standard error and input. -/
theorem call_keeps {n : Nat} (hq : Quiet D n) (hD : D.Typed) {Γ : Ctx}
    {η : REnv} {f : Value} {passed : List Passed} {ps : List (Mode × Ty)} {result : Ty} {σ : Row}
    (hf : Value.Typed D f ((Ty.fn ps result σ).close η)) (hp : Passed.Typed D Γ η passed ps)
    (hio : STy.io ∉ σ.close η) :
    Eval.KeepsIo D Γ η ⟨σ.close η, fun _ => False, performsOf D (σ.close η)⟩
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
    exact invoke_keeps (by rw [bindArgs_substRows]; exact hbind) hbound hcap.freeze
      (hq hty hη (fun h => hio (hff.labels _ h trivial)) θ)
      fun _ _ _ h => performsOf_of_labels hff.labels h
  | @function name types rows _ d ηf hd hδ hη hσ =>
    obtain ⟨τb, hty, hfit⟩ := (hD.fns d (Decls.mem_of_fn? hd)).instance hD.wf (Decls.mem_of_fn? hd) hδ
    have hσ' : ((Ty.fn (substParamTys (d.typeArgs types) (d.params.map Param.sig))
        (d.result.substTys (d.typeArgs types)) d.row).close ηf).Fits _ := hσ
    obtain ⟨_, _, _, hc, hff⟩ := hσ'.fn_inv (D := D) rfl
    obtain ⟨rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ := by injection hc with h₁ h₂ h₃; exact ⟨h₁.symm, h₂.symm, h₃.symm⟩
    have hmatch := hff.params
    rw [← map_sig_substTys, closeParams_sig, closeParams_map_sig] at hmatch
    obtain ⟨bound, hbind, hbound⟩ := hp.bind hmatch
    show Eval.KeepsIo D Γ η _ (match D.fn? name with
      | some d => Eval.invoke Copy.memory [] d.params passed
          (eval D Copy.memory n ((d.body.substTys (d.typeArgs types)).substRows (d.rowParams.zip rows)))
      | none => Eval.fail .stuck)
    rw [hd]
    exact invoke_keeps (Δ := []) (by rw [← bindArgs_substTys (d.typeArgs types)]; exact hbind)
      hbound .nil (hq hty hη (fun h => hio (hff.labels _ h trivial)) _)
      fun _ _ _ h => performsOf_of_labels hff.labels h
  | handle hσ =>
    obtain ⟨_, h⟩ := hσ.shared_shared rfl
    simp [Ty.close] at h

end Stilt
