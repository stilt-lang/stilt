import Stilt.Handling
import Stilt.Soundness.Outcome

/-!
# Handling keeps outcomes sound

A `with` whose clauses end soundly, called on arguments of their operations'
types, ends soundly: a handler that resumes ends each clause with a value of
the type its operation gives, which resumes the rest of the block, and one that
takes control ends each with a value of the `with`'s type, its `resume`s taking
values of the type the operation gives to rests of the block of the `with`'s
type (handlers.resuming). Every other performance of the block goes on with
the `with`'s exits.
-/

namespace Stilt

variable {D : Decls} {Γ : Ctx} {η : REnv}

/-- An outcome whose frames are all `γ`'s, which are of `Γ`, each in the world the outcome
had, is as sound as it was. -/
theorem Outcome.Ok.lift {X : Exits} {P : Value → Prop} {γ : Copy.State}
    (hγ : Frame.Typed D γ.1 Γ η) :
    ∀ {o : Outcome Copy.State Value}, o.Ok D Γ η X P → (o.lift Copy.memory γ).Ok D Γ η X P
  | .done _ _, ⟨ha, _, hw⟩ => ⟨ha, hγ, hw⟩
  | .raised _ _, ⟨he, _, hw⟩ => ⟨he, hγ, hw⟩
  | .jumped _ _, ⟨hj, _, hw⟩ => ⟨hj, hγ, hw⟩
  | .panicked _ _, ⟨_, hw⟩ => ⟨hγ, hw⟩
  | .performed _ _ _ _, ⟨⟨τ, ρ, hop, hv, hk⟩, _, hw⟩ =>
    ⟨⟨τ, ρ, hop, hv, fun w x hw hx => Outcome.Ok.lift hγ (hk w x hw hx)⟩, hγ, hw⟩
  | .outOfFuel, h => h
  | .stuck, h => h

/-- What the `resume` of the body of a handler's operation takes, at the
exits `Xr` of the body: a value of the type `ρ` the operation gives, whose rest
of the block ends with a value of the `with`'s type `R`. -/
def Exits.Resumes (D : Decls) (Xr : Exits) (ρ R : STy) : Prop :=
  ∀ τ' ρ', Xr.performs .resume τ' ρ' →
    (∀ u, Value.Typed D u τ' → Value.Typed D u ρ) ∧ ∀ r, Value.Typed D r R → Value.Typed D r ρ'

/-- The body of a handler that takes control, whose `resume`s take values of
`ρ` to rests of the block that end soundly, ends soundly. -/
theorem Outcome.Ok.runBody {X Xr : Exits} {R ρ : STy}
    {resume : Value → World → Outcome Copy.State Value}
    (hR : Xr.Raises D X) (hJ : ∀ j, Xr.jumps j → X.jumps j)
    (hO : ∀ op τ ρ, op ≠ .resume → Xr.performs op τ ρ → X.performs op τ ρ)
    (hres : Xr.Resumes D ρ R)
    (hr : ∀ u x, Value.Typed D u ρ → World.Typed D x →
      (resume u x).Ok D Γ η X (fun v => Value.Typed D v R)) :
    ∀ {o : Outcome Copy.State Value}, o.Ok D Γ η Xr (fun v => Value.Typed D v R) →
      (o.runBody Copy.memory resume).Ok D Γ η X (fun v => Value.Typed D v R)
  | .done _ _, h => h
  | .raised e _, ⟨⟨F, hF, he⟩, h⟩ => ⟨hR e F hF he, h⟩
  | .jumped j _, ⟨hj, h⟩ => ⟨hJ j hj, h⟩
  | .panicked _ _, h => h
  | .performed op u γ k, ⟨⟨τ, ρ', hop, hu, hk⟩, hγ⟩ => by
    unfold Outcome.runBody
    split
    · rename_i h
      subst h
      obtain ⟨hu', hr'⟩ := hres τ ρ' hop
      exact (hr u _ (hu' u hu) hγ.2).bind fun r γ₃ hrt hγ₃ =>
        Outcome.Ok.lift hγ₃.1 (Outcome.Ok.runBody hR hJ hO hres hr (hk r _ (hr' r hrt) hγ₃.2))
    · rename_i h
      exact ⟨⟨τ, ρ', hO op _ _ h hop, hu, fun w x hw hx =>
        Outcome.Ok.runBody hR hJ hO hres hr (hk w x hw hx)⟩, hγ⟩
  | .outOfFuel, h => h
  | .stuck, h => h

/-- What a clause of a handler ends with, called on an argument of its
operation's type from a frame of `Γ`: for a handler that takes control, a value
of the `with`'s type `R`, at exits whose `resume` takes the operation's type
`ρ`; for one that resumes, a value of `ρ`. -/
def ClauseOk (D : Decls) (Γ : Ctx) (η : REnv) (X : Exits) (R ρ : STy) (control : Bool)
    (o : Outcome Copy.State Value) : Prop :=
  if control then
    ∃ Xr, Xr.Raises D X ∧ (∀ j, Xr.jumps j → X.jumps j) ∧
      (∀ op τ ρ, op ≠ .resume → Xr.performs op τ ρ → X.performs op τ ρ) ∧
      Xr.Resumes D ρ R ∧ o.Ok D Γ η Xr (fun w => Value.Typed D w R)
  else o.Ok D Γ η X (fun w => Value.Typed D w ρ)

/-- **Handling keeps outcomes sound.** The block's outcome, sound with the
exits `Xb`, handled by a handler whose clauses end soundly, is sound with the
`with`'s exits `X`. -/
theorem Outcome.Ok.handleWith {Xb X : Exits} {R : STy} {effect : Name} {control : Bool}
    {hv : Value} {call : Value → Value → Copy.State → Outcome Copy.State Value}
    (hR : Xb.Raises D X) (hJ : ∀ j, Xb.jumps j → X.jumps j)
    (hout : ∀ op τ ρ, op.effect ≠ effect → Xb.performs op τ ρ → X.performs op τ ρ)
    (hcall : ∀ op τ ρ v γ, op.effect = effect → Xb.performs op τ ρ → Value.Typed D v τ →
      State.Typed D γ Γ η → ∃ c, hv.clause? op.name = some c ∧
        ClauseOk D Γ η X R ρ control (call c v γ)) :
    ∀ {o : Outcome Copy.State Value}, o.Ok D Γ η Xb (fun v => Value.Typed D v R) →
      (o.handleWith Copy.memory effect control hv call).Ok D Γ η X (fun v => Value.Typed D v R)
  | .done _ _, h => h
  | .raised e _, ⟨⟨F, hF, he⟩, h⟩ => ⟨hR e F hF he, h⟩
  | .jumped j _, ⟨hj, h⟩ => ⟨hJ j hj, h⟩
  | .panicked _ _, h => h
  | .performed op v γ k, ⟨⟨τ, ρ, hop, hvt, hk⟩, hγ⟩ => by
    unfold Outcome.handleWith
    split
    · rename_i heff
      obtain ⟨c, hc, hcall'⟩ := hcall op τ ρ v γ heff hop hvt hγ
      rw [hc]
      dsimp only
      unfold ClauseOk at hcall'
      cases control with
      | true =>
        obtain ⟨Xr, hRr, hJr, hOr, hres, hb⟩ := hcall'
        exact hb.runBody hRr hJr hOr hres fun u x hu hx =>
          Outcome.Ok.handleWith hR hJ hout hcall (hk u x hu hx)
      | false =>
        exact hcall'.bind fun w _ hw hγ' => Outcome.Ok.handleWith hR hJ hout hcall (hk w _ hw hγ'.2)
    · rename_i heff
      exact ⟨⟨τ, ρ, hout op _ _ heff hop, hvt, fun w x hw hx =>
        Outcome.Ok.handleWith hR hJ hout hcall (hk w x hw hx)⟩, hγ⟩
  | .outOfFuel, h => h
  | .stuck, h => h

end Stilt
