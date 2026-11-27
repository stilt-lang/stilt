import Stilt.Quiet.Handling

/-!
# A `with` keeps the world's output and input

A `with` whose block's row reads as no `io` has clauses whose rows read as none, since each
fits within the row around the `with` (handlers.handler-literals). So each clause, called on
an argument of its operation's type, keeps the world, and a `with` keeps what its block
kept: the rests it resumes keep the world they resume in.
-/

namespace Stilt

variable {D : Decls} {Γ : Ctx} {η : REnv}

/-- What a clause of a handler ends with, as `ClauseOk` says, keeping the world `c`. -/
def ClauseKeeps (D : Decls) (Γ : Ctx) (η : REnv) (X : Exits) (R ρ : STy) (control : Bool)
    (o : Outcome Copy.State Value) (c : String × String × String) : Prop :=
  if control then
    ∃ Xr, Xr.Raises D X ∧ (∀ j, Xr.jumps j → X.jumps j) ∧
      (∀ op τ ρ, op ≠ .resume → Xr.performs op τ ρ → X.performs op τ ρ) ∧
      Xr.Resumes D ρ R ∧ o.Ok D Γ η Xr (fun w => Value.Typed D w R) ∧ o.KeepsIo D Xr c
  else o.Ok D Γ η X (fun w => Value.Typed D w ρ) ∧ o.KeepsIo D X c

theorem ClauseKeeps.ok {X : Exits} {R ρ : STy} {control : Bool} {o : Outcome Copy.State Value}
    {c : String × String × String} (h : ClauseKeeps D Γ η X R ρ control o c) :
    ClauseOk D Γ η X R ρ control o := by
  unfold ClauseKeeps at h
  unfold ClauseOk
  cases control with
  | true =>
    obtain ⟨Xr, h₁, h₂, h₃, h₄, h₅, -⟩ := h
    exact ⟨Xr, h₁, h₂, h₃, h₄, h₅⟩
  | false => exact h.1

/-- **Handling keeps the world.** The block's outcome, keeping the world, handled by a
handler whose clauses keep it, keeps it, when an operation of the handler's effect gives
values of one type. -/
theorem Outcome.KeepsIo.handleWith {Xb X : Exits} {R : STy} {effect : Name} {control : Bool}
    {hv : Value} {call : Value → Value → Copy.State → Outcome Copy.State Value}
    (hR : Xb.Raises D X) (hJ : ∀ j, Xb.jumps j → X.jumps j)
    (hout : ∀ op τ ρ, op.effect ≠ effect → Xb.performs op τ ρ → X.performs op τ ρ)
    (huniq : ∀ op τ ρ τ' ρ', op.effect = effect → Xb.performs op τ ρ → Xb.performs op τ' ρ' →
      ρ' = ρ)
    (hcall : ∀ op τ ρ v γ, op.effect = effect → Xb.performs op τ ρ → Value.Typed D v τ →
      State.Typed D γ Γ η → ∃ c, hv.clause? op.name = some c ∧
        ClauseKeeps D Γ η X R ρ control (call c v γ) γ.2.io) :
    ∀ {o : Outcome Copy.State Value} {c}, o.Ok D Γ η Xb (fun v => Value.Typed D v R) →
      o.KeepsIo D Xb c → (o.handleWith Copy.memory effect control hv call).KeepsIo D X c
  | .done _ _, _, _, h | .raised _ _, _, _, h | .jumped _ _, _, _, h | .panicked _ _, _, _, h => h
  | .performed op v γ k, c, ⟨⟨τ, ρ, hop, hvt, hok⟩, hγ⟩, ⟨hc, hk⟩ => by
    have hcall' : ∀ op τ ρ v γ, op.effect = effect → Xb.performs op τ ρ → Value.Typed D v τ →
        State.Typed D γ Γ η → ∃ c, hv.clause? op.name = some c ∧
          ClauseOk D Γ η X R ρ control (call c v γ) := fun op τ ρ v γ h₁ h₂ h₃ h₄ =>
      let ⟨c, hc, h⟩ := hcall op τ ρ v γ h₁ h₂ h₃ h₄
      ⟨c, hc, h.ok⟩
    unfold Outcome.handleWith
    split
    · rename_i heff
      obtain ⟨cl, hcl, hck⟩ := hcall op τ ρ v γ heff hop hvt hγ
      rw [hcl]
      dsimp only
      unfold ClauseKeeps at hck
      subst hc
      have hw : ∀ w, Value.Typed D w ρ → ∀ τ' ρ', Xb.performs op τ' ρ' → Value.Typed D v τ' →
          Value.Typed D w ρ' := fun w hw τ' ρ' h _ => by
        rw [huniq op τ ρ τ' ρ' heff hop h]
        exact hw
      cases control with
      | true =>
        obtain ⟨Xr, -, -, hOr, hres, hb, hbk⟩ := hck
        exact Outcome.KeepsIo.runBody hOr hres
          (fun u x hu hx => Outcome.Ok.handleWith hR hJ hout hcall' (hok u x hu hx))
          (fun u x hu hx => Outcome.KeepsIo.handleWith hR hJ hout huniq hcall (hok u x hu hx)
            (hk u x hx (hw u hu)))
          hb hbk
      | false =>
        obtain ⟨hb, hbk⟩ := hck
        exact hb.keeps_bind (fun w γ' hwt hγ' => Outcome.KeepsIo.handleWith hR hJ hout huniq hcall
          (hok w _ hwt hγ'.2) (hk w _ hγ'.2 (hw w hwt))) hbk
    · rename_i heff
      exact ⟨hc, fun w x hx hw => Outcome.KeepsIo.handleWith hR hJ hout huniq hcall
        (hok w x (hw τ ρ (hout op _ _ heff hop) hvt) hx)
        (hk w x hx fun τ' ρ' h hv' => hw τ' ρ' (hout op _ _ heff h) hv')⟩
  | .outOfFuel, _, _, h | .stuck, _, _, h => h

/-- An operation of an effect other than `resume`'s gives values of one type. -/
theorem performsOf_unique {L : List STy} {op : Operation} (hne : op ≠ .resume) {τ ρ τ' ρ' : STy}
    (h : performsOf D L op τ ρ) (h' : performsOf D L op τ' ρ') : ρ' = ρ := by
  obtain ⟨_, A, B, hAB, -, rfl⟩ := (performsOf_of_ne hne).1 h
  obtain ⟨_, A', B', hAB', -, rfl⟩ := (performsOf_of_ne hne).1 h'
  rw [hAB] at hAB'
  cases hAB'
  rfl

/-- A row whose `resume` is dropped holds the same `io`. -/
theorem Row.io_not_mem_dropResume {ρ : Row} (h : STy.io ∉ ({ ρ with resume := none } : Row).close η) :
    STy.io ∉ ρ.close η := fun hm => h (Row.close_dropResume hm fun _ _ h' => nomatch h')

end Stilt
