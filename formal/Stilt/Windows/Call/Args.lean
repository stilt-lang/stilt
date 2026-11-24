import Stilt.Windows.Path

/-!
# The arguments of a call

A call's arguments run from left to right (values.left-to-right): a value argument's value
waits while those after it run, its sources being read (`argsViewsRead`), and an `inout`
argument's indexes give the same path in both models (values.index-reads). Both models end
alike, with arguments of the same shapes: values read alike, the in-place ones values the checks
accept, each window tracked by its argument's sources; and the same places.
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls}

/-- The arguments of a call once evaluated, against the arguments the checks read: a value
argument passes values read alike, the in-place one a value the checks accept, the windows of
the other tracked by the argument's sources; an `inout` argument passes the same place, whose
path resolves the argument's projections. -/
inductive ArgsRel (D : Decls) (Γ : ViewScope) (In : List (Name × Value)) (si : IState)
    (sw : WState) : List Arg → List Passed → List Passed → Prop
  | nil : ArgsRel D Γ In si sw [] [] []
  | value {e₀ : Expr} (e : Expr) {v w : Value} {args₀ : List Arg} {ps ps' : List Passed} :
      VRel si.1.store sw.1.store w v → v.Viewed D →
      (∀ win ∈ windowsOf w, Tracked sw.1.env In (e₀.sources D Γ) win) →
      ArgsRel D Γ In si sw args₀ ps ps' →
      ArgsRel D Γ In si sw (.value e₀ :: args₀) (Passed.ofArg e v :: ps) (Passed.ofArg e w :: ps')
  | inout (x : Name) {ps₀ : List Projection} {p : Path} {args₀ : List Arg}
      {ps ps' : List Passed} :
      p.Resolves ps₀ → ArgsRel D Γ In si sw args₀ ps ps' →
      ArgsRel D Γ In si sw (.inout ⟨x, ps₀⟩ :: args₀) (.place x p :: ps) (.place x p :: ps')

/-- The arguments of a call, evaluated in turn. -/
theorem SimP.args {run : Expr → Eval IState Value} {run' : Expr → Eval WState Value} :
    ∀ {args₀ args : List Arg}, ArgsInst D args₀ args → ∀ (c : Ctx) (pend : List (Window × Value)),
      (∀ e₀ e, Expr.Inst D e₀ e → RunsIn D c run run' e₀ e) →
      argsViewsRead D c.Γ c.R args₀ = true → argsContained D c.Γ c.P args₀ = true →
      SimP D c pend (fun _ _ => True) (fun ps ps' si sw => ArgsRel D c.Γ c.In si sw args₀ ps ps')
        (Eval.args run args) (Eval.args run' args)
  | _, _, .nil, _, _, _, _, _ => SimP.pure fun _ _ _ _ => .nil
  | _, _, .value (e := e₀) (e' := e) (as := args₀) (as' := args) hi has, c, pend, ih, hr, hc => by
    simp only [argsViewsRead, Bool.and_eq_true] at hr
    simp only [argsContained, Bool.and_eq_true] at hc
    show SimP D c pend _ _
      (do let v ← run e; let vs ← Eval.args run args; Pure.pure (Passed.ofArg e v :: vs))
      (do let v ← run' e; let vs ← Eval.args run' args; Pure.pure (Passed.ofArg e v :: vs))
    refine SimP.bind (ih e₀ e hi c.R pend hr.1 hc.1) fun v w => ?_
    refine (SimP.after (X := e₀.sources D c.Γ) (Q := fun _ _ => True)
      fun si sw _ hvw _ => ?_).mono (fun _ _ h => ⟨h, trivial⟩) fun _ _ _ _ h => h
    have ih' : ∀ e₁ e', Expr.Inst D e₁ e' →
        RunsIn D { c with R := e₀.sources D c.Γ ++ c.R } run run' e₁ e' :=
      fun e₁ e' hi' X pend' hrx hcx => ih e₁ e' hi' X pend' hrx hcx
    refine SimP.bindEnv ((SimP.args has _ _ ih' hr.2 hc.2).mono (fun _ _ _ => trivial)
      fun _ _ _ _ h => h) fun vs ws => ?_
    refine SimP.pure fun si₁ sw₁ hp₁ hq => ?_
    obtain ⟨hvs, si₀, sw₀, ⟨h₁, h₂⟩, he⟩ := hq
    subst h₁ h₂
    have hv₁ : VRel si₁.1.store sw₁.1.store w v := VRel.of_pins hvw.1 fun wd hwd => by
      have := hp₁.pend wd (List.mem_append_left _ hwd)
      exact ⟨this.1, this.2.1⟩
    exact .value e hv₁ hvw.2.2 (by rw [he]; exact hvw.2.1) hvs
  | _, _, .inout x (ps := ps₀) (ps' := ps) (as := args₀) (as' := args) hps has, c, pend, ih, hr,
      hc => by
    simp only [argsViewsRead, Bool.and_eq_true] at hr
    simp only [argsContained, Bool.and_eq_true] at hc
    show SimP D c pend _ _
      (do let p ← Eval.path run ps; let vs ← Eval.args run args; Pure.pure (Passed.place x p :: vs))
      (do
        let p ← Eval.path run' ps
        let vs ← Eval.args run' args
        Pure.pure (Passed.place x p :: vs))
    refine SimP.bind (SimP.path hps c pend ih hr.1 hc.1) fun p p' => ?_
    intro si sw hp hg ⟨he, hres⟩
    subst he
    refine SimP.bind (Q := fun _ _ => True) ((SimP.args has c pend ih hr.2 hc.2).mono
      (fun _ _ _ => trivial)
      fun _ _ _ _ h => h) (fun vs ws => SimP.pure fun _ _ _ h => .inout x hres h) si sw hp hg
      trivial

theorem ofArg_ne_place (e : Expr) (v : Value) (x : Name) (p : Path) :
    Passed.ofArg e v ≠ .place x p := by
  unfold Passed.ofArg
  split <;> simp

theorem value?_ofArg (e : Expr) (v : Value) : (Passed.ofArg e v).value? = some v := by
  unfold Passed.ofArg
  split <;> rfl

namespace ArgsRel

variable {Γ : ViewScope} {In : List (Name × Value)} {si : IState} {sw : WState}

/-- Each place an `inout` argument passes resolves the projections of one whose shape the reads
`R` don't overlap, when the checks give that of every `inout` argument (E0423). -/
theorem places {R : List Shape} : ∀ {args₀ : List Arg} {ps ps' : List Passed},
    ArgsRel D Γ In si sw args₀ ps ps' → (inoutShapes args₀).all (unread R) = true →
      ∀ x p, Passed.place x p ∈ ps' →
        ∃ ps₀ : List Projection, p.Resolves ps₀ ∧ unread R (Place.mk x ps₀).shape = true
  | _, _, _, .nil, _, _, _, hm => nomatch hm
  | _, _, _, .value e _ _ _ h, hu, x, p, hm => by
    rcases List.mem_cons.1 hm with he | hm
    · exact absurd he.symm (ofArg_ne_place e _ x p)
    · exact places h (by simpa only [inoutShapes] using hu) x p hm
  | _, _, _, .inout y hres h, hu, x, p, hm => by
    simp only [inoutShapes, List.all_cons, Bool.and_eq_true] at hu
    rcases List.mem_cons.1 hm with he | hm
    · injection he with h₁ h₂
      subst h₁ h₂
      exact ⟨_, hres, hu.1⟩
    · exact places h hu.2 x p hm

/-- The windows a value argument passes are tracked by the sources of the views the call's
value arguments pass (`argViews`). -/
theorem tracked : ∀ {args₀ : List Arg} {ps ps' : List Passed},
    ArgsRel D Γ In si sw args₀ ps ps' → ∀ a ∈ ps', ∀ w, a.value? = some w →
      ∀ win ∈ windowsOf w, Tracked sw.1.env In (argViews D Γ args₀) win
  | _, _, _, .nil, _, ha, _, _, _, _ => nomatch ha
  | _, _, _, .value (e₀ := e₀) e _ _ ht h, a, ha, w, hw, win, hwin => by
    simp only [argViews]
    rcases List.mem_cons.1 ha with rfl | ha
    · rw [value?_ofArg, Option.some.injEq] at hw
      subst hw
      exact (ht win hwin).sub fun s hs => List.mem_append_left _ hs
    · exact (tracked h a ha w hw win hwin).sub fun s hs => List.mem_append_right _ hs
  | _, _, _, .inout y _ h, a, ha, w, hw, win, hwin => by
    simp only [argViews]
    rcases List.mem_cons.1 ha with rfl | ha
    · cases hw
    · exact tracked h a ha w hw win hwin

end ArgsRel

end Windows

end Stilt
