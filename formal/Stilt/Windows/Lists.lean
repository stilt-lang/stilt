import Stilt.Windows.Wait

/-!
# Operands evaluated in turn

The operands of a list, a variant, an operation, a view or a call, and the fields of a record
literal, run from left to right; each one's value waits while those after it run, with its
sources being read (`exprsViewsRead`, `fieldsViewsRead`). Both models end alike, their values
read alike one by one, their windows tracked by the sources of all of them.
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls}

/-- Values evaluated in turn, read alike one by one, their windows tracked by the sources `S`,
the in-place ones values the checks accept. -/
def ValsG (D : Decls) (c : Ctx) (S : List Shape) (vs ws : List Value) (si : IState)
    (sw : WState) : Prop :=
  mapWindowsValues (partIn si.1.store) ws = .ok vs ∧
    (∀ win ∈ windowsOfValues ws, Holds sw.1.store si.1.store win ∧ Tracked sw.1.env c.In S win) ∧
      ∀ v ∈ vs, v.Viewed D

/-- An expression's runs, in any reads around it: what the evaluation of an operand gives. -/
def RunsIn (D : Decls) (c : Ctx) (run : Expr → Eval IState Value) (run' : Expr → Eval WState Value)
    (e₀ e : Expr) : Prop :=
  ∀ (X : List Shape) (pend : List (Window × Value)), e₀.viewsRead D c.Γ X = true →
    e₀.contained D c.Γ c.P = true → Sim D { c with R := X } pend (e₀.sources D c.Γ) (run e) (run' e)

theorem ValsG.nil (c : Ctx) (S : List Shape) (si : IState) (sw : WState) :
    ValsG D c S [] [] si sw :=
  ⟨rfl, fun _ h => by simp [windowsOfValues] at h, fun _ h => by cases h⟩

/-- A value read alike, waiting before values read alike, gives the values read alike. -/
theorem ValsG.cons {c : Ctx} {S S' : List Shape} {v w : Value} {vs ws : List Value} {si : IState}
    {sw : WState} (hv : VRel si.1.store sw.1.store w v)
    (ht : ∀ win ∈ windowsOf w, Tracked sw.1.env c.In S win) (hvv : v.Viewed D)
    (hvs : ValsG D c S' vs ws si sw) :
    ValsG D c (S ++ S') (v :: vs) (w :: ws) si sw := by
  refine ⟨mapWindowsValues_cons.2 ⟨v, vs, hv.1, hvs.1, rfl⟩, fun win hwin => ?_, fun u hu => ?_⟩
  · simp only [windowsOfValues, List.mem_append] at hwin
    rcases hwin with hwin | hwin
    · exact ⟨hv.2 win hwin, (ht win hwin).sub fun s hs => List.mem_append_left _ hs⟩
    · obtain ⟨h₁, h₂⟩ := hvs.2.1 win hwin
      exact ⟨h₁, h₂.sub fun s hs => List.mem_append_right _ hs⟩
  · rcases List.mem_cons.1 hu with rfl | hu
    · exact hvv
    · exact hvs.2.2 u hu

theorem Ctx.with_R_R (c : Ctx) (X Y : List Shape) : { { c with R := X } with R := Y } = { c with R := Y } :=
  rfl

theorem Ctx.with_R_self (c : Ctx) : { c with R := c.R } = c := rfl

/-- The operands of a list, evaluated in turn. -/
theorem SimP.list {run : Expr → Eval IState Value} {run' : Expr → Eval WState Value} :
    ∀ {es₀ es : List Expr}, ExprsInst D es₀ es → ∀ (c : Ctx) (pend : List (Window × Value)),
      (∀ e₀ e, e₀ ∈ es₀ → Expr.Inst D e₀ e → RunsIn D c run run' e₀ e) →
      exprsViewsRead D c.Γ c.R es₀ = true → exprsContained D c.Γ c.P es₀ = true →
      SimP D c pend (fun _ _ => True) (ValsG D c (exprsSources D c.Γ es₀)) (Eval.list run es)
        (Eval.list run' es)
  | _, _, .nil, c, pend, _, _, _ => SimP.pure fun si sw _ _ => ValsG.nil c _ si sw
  | _, _, .cons (e := e₀) (e' := e) (es := es₀) (es' := es) hi his, c, pend, ih, hr, hc => by
    simp only [exprsViewsRead, Bool.and_eq_true] at hr
    simp only [exprsContained, Bool.and_eq_true] at hc
    show SimP D c pend _ _ (do let v ← run e; let vs ← Eval.list run es; Pure.pure (v :: vs))
      (do let v ← run' e; let vs ← Eval.list run' es; Pure.pure (v :: vs))
    refine SimP.bind (ih e₀ e List.mem_cons_self hi c.R pend hr.1 hc.1) fun v w => ?_
    refine (SimP.after (X := e₀.sources D c.Γ) (Q := fun _ _ => True) fun si sw _ hvw _ => ?_).mono
      (fun _ _ h => ⟨h, trivial⟩) fun _ _ _ _ h => h
    have ih' : ∀ e₁ e', e₁ ∈ es₀ → Expr.Inst D e₁ e' →
        RunsIn D { c with R := e₀.sources D c.Γ ++ c.R } run run' e₁ e' :=
      fun e₁ e' hm hi' X pend' hrx hcx => ih e₁ e' (List.mem_cons_of_mem _ hm) hi' X pend' hrx hcx
    refine SimP.bindEnv ((SimP.list his _ _ ih' hr.2 hc.2).mono (fun _ _ _ => trivial)
      fun _ _ _ _ h => h) fun vs ws => ?_
    refine SimP.pure fun si₁ sw₁ hp₁ hq => ?_
    obtain ⟨hvs, si₀, sw₀, ⟨h₁, h₂⟩, he⟩ := hq
    subst h₁ h₂
    have hv₁ : VRel si₁.1.store sw₁.1.store w v := VRel.of_pins hvw.1 fun wd hwd => by
      have := hp₁.pend wd (List.mem_append_left _ hwd)
      exact ⟨this.1, this.2.1⟩
    exact ValsG.cons hv₁ (by rw [he]; exact hvw.2.1) hvw.2.2 hvs

end Windows

end Stilt
