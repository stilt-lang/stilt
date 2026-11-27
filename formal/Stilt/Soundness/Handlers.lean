import Stilt.Soundness.Cases
import Stilt.Handling.Sound
import Stilt.Soundness.Holding

/-!
# Performances and handlers

A performance of an operation whose effect the row holds ends as a performance
that the exits allow, on an argument of the operation's type, and its rest,
resumed with a value of the operation's result type, ends with that value
(handlers.performing-operation and handlers.resuming). A `with` runs its block
with the handler's effect in its row, and handles the block's performances of
that effect by calling the handler's clauses, which a call where the `with` is
may make (handlers.with): `Outcome.Ok.handleWith` does the rest.
-/

namespace Stilt

theorem Row.close_withEffect {η : REnv} {ρ : Row} {E : Name} {x : STy}
    (hx : x ∈ (ρ.withEffect E).close η) : x = .effect E ∨ x ∈ ρ.close η := by
  rcases Row.mem_close.1 hx with h | h | ⟨E', hE', rfl⟩ | h
  · exact .inr (Row.mem_close.2 (.inl h))
  · exact .inr (Row.mem_close.2 (.inr (.inl h)))
  · rcases List.mem_cons.1 hE' with rfl | hE'
    · exact .inl rfl
    · exact .inr (Row.mem_close.2 (.inr (.inr (.inl ⟨E', hE', rfl⟩))))
  · exact .inr (Row.mem_close.2 (.inr (.inr (.inr h))))

theorem Row.close_dropResume {η : REnv} {ρ : Row} {x : STy} (hx : x ∈ ρ.close η)
    (h : ∀ a r, x ≠ .resume a r) : x ∈ ({ ρ with resume := none } : Row).close η := by
  rcases Row.mem_close.1 hx with h₁ | h₁ | h₁ | ⟨p, _, rfl⟩ | h₁
  · exact Row.mem_close.2 (.inl h₁)
  · exact Row.mem_close.2 (.inr (.inl h₁))
  · exact Row.mem_close.2 (.inr (.inr (.inl h₁)))
  · exact absurd rfl (h p.1 p.2)
  · exact Row.mem_close.2 (.inr (.inr (.inr (.inr h₁))))

theorem Row.dropResume_eq {ρ : Row} (h : ρ.resume = none) : ({ ρ with resume := none } : Row) = ρ := by
  cases ρ
  simp_all

section

variable {D : Decls}

theorem performsOf_dropResume {L : List STy} {ρ : Row} {η : REnv} (hL : L = ρ.close η)
    {op : Operation} {τ ρ' : STy} (hne : op ≠ .resume) (h : performsOf D L op τ ρ') :
    performsOf D (({ ρ with resume := none } : Row).close η) op τ ρ' := by
  subst hL
  obtain ⟨hm, h'⟩ := (performsOf_of_ne hne).1 h
  exact (performsOf_of_ne hne).2 ⟨Row.close_dropResume hm (fun _ _ h'' => nomatch h''), h'⟩

/-- A `with`'s block raises what the code around it may. -/
theorem Effects.raises_withEffect {η : REnv} {fx : Effects} {E : Name} :
    Exits.Raises D (({ fx with row := fx.row.withEffect E } : Effects).exits D η) (fx.exits D η) := by
  intro e F hF he
  refine ⟨F, ?_, he⟩
  unfold Effects.exits Effects.raises at hF ⊢
  cases hc : fx.catching
  · simp only [hc] at hF ⊢
    rcases Row.close_withEffect hF with rfl | h
    · exact absurd trivial he.not_label
    · exact h
  · simpa [hc, Row.withEffect] using hF

/-- A `with`'s block performs, but for its handler's effect, what the code
around it may. -/
theorem performsOf_withEffect {η : REnv} {ρ : Row} {E : Name} {op : Operation} {τ ρ' : STy}
    (hne : op.effect ≠ E) (h : performsOf D ((ρ.withEffect E).close η) op τ ρ') :
    performsOf D (ρ.close η) op τ ρ' := by
  by_cases hr : op = Operation.resume
  · subst hr
    obtain ⟨B, R, hm, h₁, h₂⟩ := performsOf_resume.1 h
    rcases Row.close_withEffect hm with h' | h'
    · cases h'
    · exact performsOf_resume.2 ⟨B, R, h', h₁, h₂⟩
  · obtain ⟨hm, h''⟩ := (performsOf_of_ne hr).1 h
    rcases Row.close_withEffect hm with h' | h'
    · cases h'
      exact absurd rfl hne
    · exact (performsOf_of_ne hr).2 ⟨h', h''⟩


/-- A closed function type reads as itself, part by part, under every
environment. -/
theorem Ty.Closed.fn_close {A r : Ty} {ρ : Row} (h : (Ty.fn [(.let, A)] r ρ).Closed) (η : REnv) :
    A.close η = A.sem ∧ r.close η = r.sem ∧ ρ.close η = ρ.close (fun _ => []) := by
  have h' := h.close η
  simp only [Ty.sem, Ty.close, closeParams] at h'
  injection h' with h₁ h₂ h₃
  injection h₁ with h₁
  injection h₁ with _ h₁
  exact ⟨h₁, h₂, h₃⟩

/-- The clause of a handler value for an operation of its effect: a closure of
the closed type its record declares for the operation (handlers.handler-literals). -/
theorem HandlerFits.clause {scope : RowScope} {fx : Effects} (hD : D.WellFormed)
    {eff : EffectDecl} {R : Name} {r : RecordDecl} {hv : Value} {control : Option Ty} {o : Name}
    {A B : Ty} (hr : D.record? R = some r) (hh : Value.Typed D hv (.record R []))
    (hfits : HandlerFits scope fx eff r.fields control) (ho : eff.ops.lookup o = some (A, B))
    (η : REnv) :
    ∃ c ρc, hv.clause? o = some c ∧
      Value.Typed D c ((Ty.fn [(.let, A)] (control.getD B) ρc).close η) ∧
      (Ty.fn [(.let, A)] (control.getD B) ρc).Closed ∧
      ρc.resume = control.map (B, ·) ∧ CallAllowed scope fx { ρc with resume := none } := by
  obtain ⟨ρc, hf, hres, hcall⟩ := hfits o A B ho
  obtain ⟨r', fields, rfl, hr', -, hfs⟩ := hh.record_inv
  rw [hr] at hr'
  cases hr'
  obtain ⟨c, hc, hct⟩ := hfs.lookup hf
  rw [List.zip_nil_right, Ty.semAt, STy.substParams_nil] at hct
  have hcl := hD.fieldsClosed _ (Decls.mem_of_record? hr) _ (List.mem_of_lookup hf)
  exact ⟨c, ρc, hc, (hcl.close η).symm ▸ hct, hcl, hres, hcall⟩

/-- The `resume` labels of a closed row: its own. -/
theorem Row.resume_of_close {ρ : Row} {B R : Ty} {a r : Ty}
    (hres : ρ.resume = some (a, r)) (hm : STy.resume B R ∈ ρ.close (fun _ => [])) :
    B = a ∧ R = r := by
  rcases Row.mem_close.1 hm with ⟨E, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨p, hp, h⟩ | ⟨_, h⟩
  · exact absurd (show (E.close fun _ => []).IsLabel from h ▸ trivial) (Ty.close_not_label _ E)
  · exact nomatch h
  · exact nomatch h
  · rw [hres] at hp
    cases hp
    injection h with h₁ h₂
    exact ⟨h₁, h₂⟩
  · exact nomatch h

end

section

variable {D : Decls} {n : Nat} (hs : Sound D n) {scope : RowScope} {η : REnv}
  (hη : η.Respects scope) (θ : RowSubst) {Γ : Ctx} {fx : Effects}
include hs hη

theorem perform_ok {op : Operation} {e : Expr} {A B σ : Ty} (hne : op ≠ .resume)
    (hop : D.operation? op = some (A, B)) (hA : A.Ground) (hB : B.Ground)
    (hE : op.effect ∈ fx.row.effects) (he : HasType D scope Γ fx e σ) (hfit : Fits σ A) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (B.close η))
      (eval D Copy.memory (n + 1) ((Expr.perform op e).substRows θ)) :=
  Eval.Ok.bind (hs he hη θ) fun _ hv _ hγ =>
    ⟨⟨A.sem, B.sem, (performsOf_of_ne hne).2
        ⟨Row.mem_close.2 (.inr (.inr (.inl ⟨_, hE, rfl⟩))), A, B, hop, rfl, rfl⟩,
      hA.1.close η ▸ hv.fits (hfit.close η), fun _ _ hw hx => ⟨(hB.1.close η).symm ▸ hw, hγ.1, hx⟩⟩, hγ⟩

theorem resume_ok {e : Expr} {B R σ : Ty} (hr : fx.row.resume = some (B, R)) (hB : B.Ground)
    (hR : R.Ground) (he : HasType D scope Γ fx e σ) (hfit : Fits σ B) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (R.close η))
      (eval D Copy.memory (n + 1) ((Expr.perform Operation.resume e).substRows θ)) :=
  Eval.Ok.bind (hs he hη θ) fun _ hv _ hγ =>
    ⟨⟨B.sem, R.sem, (performsOf_resume (D := D)).2
        ⟨B, R, Row.mem_close.2 (.inr (.inr (.inr (.inl ⟨_, hr, rfl⟩)))), rfl, rfl⟩,
      hB.1.close η ▸ hv.fits (hfit.close η), fun _ _ hw hx => ⟨(hR.1.close η).symm ▸ hw, hγ.1, hx⟩⟩, hγ⟩

/-- A handler's clause for an operation of its effect, called on an argument of
the operation's type, ends as `ClauseOk` says: a call where the `with` is may
make it, and the `resume` its row holds takes the operation's result type to
the `with`'s type (handlers.resuming). -/
theorem clause_ok (hD : D.Typed) {E : Name} {eff : EffectDecl} {R : Name} {r : RecordDecl}
    {hv : Value} {control : Option Ty} {τw : Ty} (hEne : E ≠ Operation.resume.effect)
    (heff : D.effect? E = some eff) (hr : D.record? R = some r)
    (hh : Value.Typed D hv (.record R [])) (hfits : HandlerFits scope fx eff r.fields control)
    (hctl : ∀ τ, control = some τ → τ = τw) {op : Operation} {τ ρ : STy} {v : Value}
    {γ : Copy.State} (hE : op.effect = E)
    (hop : performsOf D ((fx.row.withEffect E).close η) op τ ρ)
    (hvt : Value.Typed D v τ) (hγ : State.Typed D γ Γ η) :
    ∃ c, hv.clause? op.name = some c ∧ ClauseOk D Γ η (fx.exits D η) (τw.close η) ρ
      control.isSome (Eval.callAs D Copy.memory (eval D Copy.memory n) control.isSome c [.value v] γ) := by
  have hne : op ≠ .resume := fun h => hEne (by rw [← hE, h])
  obtain ⟨_, A, B, hAB, rfl, rfl⟩ := (performsOf_of_ne hne).1 hop
  have ho : eff.ops.lookup op.name = some (A, B) := by
    simpa [Decls.operation?, hE, heff] using hAB
  obtain ⟨c, ρc, hc, hct, hcl, hres, hcall⟩ := HandlerFits.clause hD.wf hr hh hfits ho η
  obtain ⟨hA, hrt, hρc⟩ := hcl.fn_close η
  have hok := call_ok hs hD hct (.value (hA ▸ hvt) .nil) γ hγ
  refine ⟨c, hc, ?_⟩
  unfold ClauseOk Eval.callAs
  cases control with
  | none =>
    rw [hct.takesControl_eq_false hη hres]
    have hcall' : CallAllowed scope fx ρc := Row.dropResume_eq hres ▸ hcall
    exact hok.mono (fun w hw => hrt ▸ hw) (hcall'.raises hη) (fun _ h => h.elim) hcall'.performs
  | some τc =>
    obtain rfl := hctl τc rfl
    simp only [Option.isSome_some, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    refine ⟨⟨ρc.close η, fun _ => False, performsOf D (ρc.close η)⟩, fun e F hF he => (hcall.raises hη) e F (Row.close_dropResume hF fun a r h => ?_) he,
      fun _ h => h.elim, fun op τ ρ hne h => hcall.performs op τ ρ (performsOf_dropResume rfl hne h),
      fun τ' ρ' h => ?_, hok⟩
    · subst h
      exact he.not_label trivial
    · obtain ⟨B', R', hm, rfl, rfl⟩ := (performsOf_resume (D := D)).1 h
      rw [hρc] at hm
      obtain ⟨rfl, rfl⟩ := Row.resume_of_close hres hm
      exact ⟨fun _ hu => hu, fun _ hr => hrt ▸ hr⟩

theorem withH_ok (hD : D.Typed) {E : Name} {eff : EffectDecl} {h b : Expr} {R : Name}
    {r : RecordDecl} {τ : Ty} (hEne : E ≠ Operation.resume.effect) (heff : D.effect? E = some eff)
    (hh : HasType D scope Γ fx h (.record R [])) (hr : D.record? R = some r)
    (hfits : HandlerFits scope fx eff r.fields none)
    (hb : HasType D scope Γ { fx with row := fx.row.withEffect E } b τ) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (τ.close η))
      (eval D Copy.memory (n + 1) ((Expr.withH E false h b).substRows θ)) :=
  Eval.Ok.bind (hs hh hη θ) fun _ hhv γ hγ =>
    ((hs hb hη θ γ hγ).handleWith Effects.raises_withEffect (fun _ h => h)
      (fun _ _ _ hne hp => performsOf_withEffect hne hp)
      fun _ _ _ _ _ hE hp hvt hγ' =>
        clause_ok hs hη hD hEne heff hr hhv hfits (fun _ h => nomatch h) hE hp hvt hγ').letGo _

theorem withControl_ok (hD : D.Typed) {E : Name} {eff : EffectDecl} {h b : Expr} {R : Name}
    {r : RecordDecl} {σ τ : Ty} (hEne : E ≠ Operation.resume.effect)
    (heff : D.effect? E = some eff) (hh : HasType D scope Γ fx h (.record R []))
    (hr : D.record? R = some r) (hfits : HandlerFits scope fx eff r.fields (some τ))
    (hb : HasType D scope Γ { fx with row := fx.row.withEffect E } b σ) (hfit : Fits σ τ) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (τ.close η))
      (eval D Copy.memory (n + 1) ((Expr.withH E true h b).substRows θ)) :=
  Eval.Ok.bind (hs hh hη θ) fun _ hhv γ hγ =>
    (((hs hb hη θ γ hγ).mono (fun _ hv => hv.fits (hfit.close η)) (fun _ F hF he => ⟨F, hF, he⟩)
        (fun _ h => h) fun _ _ _ h => h).handleWith Effects.raises_withEffect (fun _ h => h)
      (fun _ _ _ hne hp => performsOf_withEffect hne hp)
      fun _ _ _ _ _ hE hp hvt hγ' =>
        clause_ok hs hη hD hEne heff hr hhv hfits (fun _ h => (Option.some.inj h).symm) hE hp hvt
          hγ').letGo _

end

end Stilt
