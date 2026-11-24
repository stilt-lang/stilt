import Stilt.Windows.Lists
import Stilt.Windows.Scalars

/-!
# The indexes of a place

A place's indexes run in turn, each read as an integer alike, so both models give the same path,
whose fields are the place's (`Path.Resolves`).
-/

namespace Stilt

namespace Windows

variable {D : Decls}

/-- The indexes of a place, run in turn: the same path in both models. -/
theorem SimP.path {run : Expr → Eval IState Value} {run' : Expr → Eval WState Value} :
    ∀ {ps₀ ps : List Projection}, PathInst D ps₀ ps → ∀ (c : Ctx) (pend : List (Window × Value)),
      (∀ i₀ i, Expr.Inst D i₀ i → RunsIn D c run run' i₀ i) →
      pathViewsRead D c.Γ c.R ps₀ = true → pathContained D c.Γ c.P ps₀ = true →
      SimP D c pend (fun _ _ => True) (fun p p' _ _ => p' = p ∧ p.Resolves ps₀)
        (Eval.path run ps) (Eval.path run' ps)
  | _, _, .nil, _, _, _, _, _ => SimP.pure fun _ _ _ _ => ⟨rfl, trivial⟩
  | _, _, .field f hps, c, pend, ih, hr, hc => by
    simp only [pathViewsRead] at hr
    simp only [pathContained] at hc
    refine SimP.bind (SimP.path hps c pend ih hr hc) fun p p' => ?_
    exact SimP.pure fun _ _ _ ⟨he, hres⟩ => ⟨by rw [he], rfl, hres⟩
  | _, _, .index (i := i₀) (i' := i) (ps := ps₀) (ps' := ps) hi hps, c, pend, ih, hr, hc => by
    simp only [pathViewsRead, Bool.and_eq_true] at hr
    simp only [pathContained, Bool.and_eq_true] at hc
    show SimP D c pend _ _
      ((run i >>= Eval.asInt) >>= fun k => Eval.path run ps >>= fun p => Pure.pure (Step.index k :: p))
      ((run' i >>= Eval.asInt) >>= fun k => Eval.path run' ps >>= fun p =>
        Pure.pure (Step.index k :: p))
    refine SimP.bind (SimP.bind (ih i₀ i hi c.R pend hr.1 hc.1) fun v w =>
      SimP.asInt fun _ _ h => h.1) fun k k' => ?_
    by_cases hk : k = k'
    · subst hk
      refine SimP.bind ((SimP.path hps c pend ih hr.2 hc.2).mono (fun _ _ _ => trivial)
        fun _ _ _ _ h => h) fun p p' => ?_
      exact SimP.pure fun _ _ _ ⟨he, hres⟩ => ⟨by rw [he], hres⟩
    · exact fun _ _ _ _ hq => absurd hq hk

end Windows

end Stilt
