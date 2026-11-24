import Stilt.Windows.Lists

/-!
# Fields, indexes and record literals

The fields of a record literal run in turn as the operands of a list do; a record is built from
fields read alike; and the indexes of a place give the same path in both models, an index read
through a window being no integer in either.
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls}

/-- Fields evaluated in turn, read alike one by one, their windows tracked by the sources `S`. -/
def FieldsG (D : Decls) (c : Ctx) (S : List Shape) (vs ws : List (Name × Value)) (si : IState)
    (sw : WState) : Prop :=
  mapWindowsFields (partIn si.1.store) ws = .ok vs ∧
    (∀ win ∈ windowsOfFields ws, Holds sw.1.store si.1.store win ∧ Tracked sw.1.env c.In S win) ∧
      ∀ fv ∈ vs, fv.2.Viewed D

/-- The fields of a record literal, evaluated in turn. -/
theorem SimP.fields {run : Expr → Eval IState Value} {run' : Expr → Eval WState Value} :
    ∀ {fs₀ fs : List (Name × Expr)}, FieldsInst D fs₀ fs → ∀ (c : Ctx) (pend : List (Window × Value)),
      (∀ f e₀ e, (f, e₀) ∈ fs₀ → Expr.Inst D e₀ e → RunsIn D c run run' e₀ e) →
      fieldsViewsRead D c.Γ c.R fs₀ = true → fieldsContained D c.Γ c.P fs₀ = true →
      SimP D c pend (fun _ _ => True)
        (FieldsG D c (fs₀.flatMap fun fe => fe.2.sources D c.Γ)) (Eval.fields run fs)
        (Eval.fields run' fs)
  | _, _, .nil, c, pend, _, _, _ => SimP.pure fun _ _ _ _ =>
    ⟨rfl, fun _ h => by simp [windowsOfFields] at h, fun _ h => by cases h⟩
  | _, _, .cons f (e := e₀) (e' := e) (fs := fs₀) (fs' := fs) hi his, c, pend, ih, hr, hc => by
    simp only [fieldsViewsRead, Bool.and_eq_true] at hr
    simp only [fieldsContained, Bool.and_eq_true] at hc
    show SimP D c pend _ _ (do let v ← run e; let vs ← Eval.fields run fs; Pure.pure ((f, v) :: vs))
      (do let v ← run' e; let vs ← Eval.fields run' fs; Pure.pure ((f, v) :: vs))
    refine SimP.bind (ih f e₀ e List.mem_cons_self hi c.R pend hr.1 hc.1) fun v w => ?_
    refine (SimP.after (X := e₀.sources D c.Γ) (Q := fun _ _ => True) fun si sw _ hvw _ => ?_).mono
      (fun _ _ h => ⟨h, trivial⟩) fun _ _ _ _ h => h
    have ih' : ∀ f' e₁ e', (f', e₁) ∈ fs₀ → Expr.Inst D e₁ e' →
        RunsIn D { c with R := e₀.sources D c.Γ ++ c.R } run run' e₁ e' :=
      fun f' e₁ e' hm hi' X pend' hrx hcx => ih f' e₁ e' (List.mem_cons_of_mem _ hm) hi' X pend' hrx hcx
    refine SimP.bindEnv ((SimP.fields his _ _ ih' hr.2 hc.2).mono (fun _ _ _ => trivial)
      fun _ _ _ _ h => h) fun vs ws => ?_
    refine SimP.pure fun si₁ sw₁ hp₁ hq => ?_
    obtain ⟨hvs, si₀, sw₀, ⟨h₁, h₂⟩, he⟩ := hq
    subst h₁ h₂
    have hv₁ : VRel si₁.1.store sw₁.1.store w v := VRel.of_pins hvw.1 fun wd hwd => by
      have := hp₁.pend wd (List.mem_append_left _ hwd)
      exact ⟨this.1, this.2.1⟩
    refine ⟨mapWindowsFields_cons.2 ⟨v, vs, hv₁.1, hvs.1, rfl⟩, fun win hwin => ?_,
      fun fv hfv => ?_⟩
    · simp only [windowsOfFields, List.mem_append] at hwin
      rcases hwin with hwin | hwin
      · refine ⟨hv₁.2 win hwin, ?_⟩
        rw [he]
        exact (hvw.2.1 win hwin).sub fun s hs => by simp [List.flatMap_cons, hs]
      · obtain ⟨h₁, h₂⟩ := hvs.2.1 win hwin
        exact ⟨h₁, h₂.sub fun s hs => by simp only [List.flatMap_cons, List.mem_append]; exact .inr hs⟩
    · rcases List.mem_cons.1 hfv with rfl | hfv
      · exact hvw.2.2
      · exact hvs.2.2 fv hfv

/-- Declaring a record of fields read alike: failing alike, or giving related records. -/
theorem declare_rel {c : Ctx} {S : List Shape} {vs ws : List (Name × Value)} {si : IState}
    {sw : WState} (h : FieldsG D c S vs ws si sw) (R : Name) :
    ∀ (fds : List (Name × Ty)),
      (fds.mapM (fun (f, _) => (vs.lookup f).map (f, ·)) = none ∧
        fds.mapM (fun (f, _) => (ws.lookup f).map (f, ·)) = none) ∨
      ∃ gs gs', fds.mapM (fun (f, _) => (vs.lookup f).map (f, ·)) = some gs ∧
        fds.mapM (fun (f, _) => (ws.lookup f).map (f, ·)) = some gs' ∧
        FieldsG D c S gs gs' si sw
  | [] => .inr ⟨[], [], rfl, rfl, rfl, fun _ h => by simp [windowsOfFields] at h,
      fun _ h => by cases h⟩
  | (f, τ) :: fds => by
    rcases mapWindowsFields_lookup h.1 f with ⟨h₂, h₁⟩ | ⟨w, v, h₂, h₁, h₃⟩
    · exact .inl ⟨by simp [List.mapM_cons, h₁], by simp [List.mapM_cons, h₂]⟩
    · rcases declare_rel h R fds with ⟨h₄, h₅⟩ | ⟨gs, gs', h₄, h₅, h₆⟩
      · exact .inl ⟨by simp [List.mapM_cons, h₁, h₄], by simp [List.mapM_cons, h₂, h₅]⟩
      · refine .inr ⟨(f, v) :: gs, (f, w) :: gs', by simp [List.mapM_cons, h₁, h₄],
          by simp [List.mapM_cons, h₂, h₅], mapWindowsFields_cons.2 ⟨v, gs, h₃, h₆.1, rfl⟩,
          fun win hwin => ?_, fun fv hfv => ?_⟩
        · simp only [windowsOfFields, List.mem_append] at hwin
          rcases hwin with hwin | hwin
          · exact h.2.1 win (windowsOf_lookup h₂ hwin)
          · exact h₆.2.1 win hwin
        · rcases List.mem_cons.1 hfv with rfl | hfv
          · exact h.2.2 _ (mem_of_lookup h₁)
          · exact h₆.2.2 fv hfv

end Windows

end Stilt
