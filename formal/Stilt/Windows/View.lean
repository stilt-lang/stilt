import Stilt.Windows.View.Sources

/-!
# Making a view

`View.of(source, …)` and `View.all(source)` on the relation of windows (views.making-view): the
source evaluated in both models; in the model of windows, a window on the place it names when
that takes no index (`viewOf`), the window the place holds, or the value read; that value
waiting, its sources read, while the offsets run (views.reads-that-last); then narrowed as
`View.of` slices the in-place value (`narrow`). The view's windows are tracked by the source
operand's sources (`headSources`), in a scope whose bindings of the body's own of a type that
holds no view keep no sources (`ScopeKeeps`), as every scope the checks build.
-/

namespace Stilt

open InPlace (Ref)

/-- The steps after a step after an outcome are the steps after it of the two in turn. -/
theorem Outcome.bind_bind {σ α β γ : Type} (o : Outcome σ α) (f : α → σ → Outcome σ β)
    (g : β → σ → Outcome σ γ) : (o.bind f).bind g = o.bind fun a s => (f a s).bind g := by
  induction o with
  | performed op v s k ih =>
    simp only [Outcome.bind]
    congr 1
    funext w x
    exact ih w x
  | _ => rfl

theorem Eval.bind_bind {σ α β γ : Type} (m : Eval σ α) (f : α → Eval σ β) (g : β → Eval σ γ) :
    (m >>= f >>= g) = m >>= fun a => f a >>= g := by
  funext s
  exact Outcome.bind_bind (m s) _ _

namespace Windows

variable {α β : Type} {D : Decls} {c : Ctx} {pend : List (Window × Value)}

/-- The in-place model makes a view by evaluating its source, then its offsets. -/
theorem eval_view_inPlace (n : Nat) (src : Expr) (offs : List Expr) :
    Stilt.eval D InPlace.memory (n + 1) (.view (src :: offs)) =
      Stilt.eval D InPlace.memory n src >>= fun v =>
        Eval.list (Stilt.eval D InPlace.memory n) offs >>= fun vs =>
          Eval.ofExcept (Op.view.apply (v :: vs)) := by
  show (Eval.list (Stilt.eval D InPlace.memory n) (src :: offs) >>= fun vs =>
    Eval.ofExcept (Op.view.apply vs)) = _
  show ((Stilt.eval D InPlace.memory n src >>= fun v =>
    Eval.list (Stilt.eval D InPlace.memory n) offs >>= fun vs => Pure.pure (v :: vs)) >>= _) = _
  rw [Eval.bind_bind]
  congr 1
  funext v
  rw [Eval.bind_bind]
  rfl

/-- Reading the states alike, with the results read. -/
theorem SimP.inspect_ok {Q : IState → WState → Prop} {G : α → β → IState → WState → Prop}
    {f : IState → Except Fault α} {f' : WState → Except Fault β}
    (h : SimP D c pend Q G (Eval.inspect f) (Eval.inspect f')) :
    SimP D c pend Q (fun a b si sw => G a b si sw ∧ f si = .ok a ∧ f' sw = .ok b)
      (Eval.inspect f) (Eval.inspect f') := by
  intro si sw hp hg hq
  have h₀ := h si sw hp hg hq
  change (Eval.ofExcept (f si) si).Rel _ (Eval.ofExcept (f' sw) sw) at h₀
  show (Eval.ofExcept (f si) si).Rel _ (Eval.ofExcept (f' sw) sw)
  cases hf : f si with
  | error e =>
    rw [hf] at h₀
    cases hf' : f' sw with
    | error e' => rw [hf'] at h₀; cases e <;> cases e' <;> exact h₀
    | ok b => rw [hf'] at h₀; cases e <;> exact h₀.elim
  | ok a =>
    rw [hf] at h₀
    cases hf' : f' sw with
    | error e' => rw [hf'] at h₀; cases e' <;> exact h₀.elim
    | ok b =>
      rw [hf'] at h₀
      exact ⟨h₀.1, h₀.2.1, h₀.2.2, hf, hf'⟩

/-- A window tracked is tracked whatever its ranges. -/
theorem Tracked.region {env : List (Name × Ref)} {In : List (Name × Value)} {S : List Shape}
    {w w' : Window} (h : Tracked env In S w) (h₁ : w.1 = w'.1) (h₂ : w.2.1 = w'.2.1) :
    Tracked env In S w' := by
  obtain ⟨l, p, r⟩ := w
  obtain ⟨l', p', r'⟩ := w'
  simp only at h₁ h₂
  subst h₁ h₂
  exact h

/-- The offsets run while the view waits, its sources read; then the view is narrowed. -/
theorem SimP.narrowing {X : List Shape} {offs₀ offs : List Expr} {run : Expr → Eval IState Value}
    {run' : Expr → Eval WState Value} (his : ExprsInst D offs₀ offs)
    (ih : ∀ e₀ e, e₀ ∈ offs₀ → Expr.Inst D e₀ e → RunsIn D { c with R := X ++ c.R } run run' e₀ e)
    (hr : exprsViewsRead D c.Γ (X ++ c.R) offs₀ = true)
    (hc : exprsContained D c.Γ c.P offs₀ = true) {v w : Value} :
    SimP D c pend (ValG D c X v w) (ValG D c X)
      (Eval.list run offs >>= fun vs => Eval.ofExcept (Op.view.apply (v :: vs)))
      (Eval.list run' offs >>= fun ns => Eval.inspect fun s => narrow s.1.store w ns) := by
  refine (SimP.after (X := X) (Q := fun _ _ => True) fun si sw _ hvw _ => ?_).mono
    (fun _ _ h => ⟨h, trivial⟩) fun _ _ _ _ h => h
  refine SimP.bindEnv ((SimP.list his _ _ ih hr hc).mono (fun _ _ _ => trivial)
    fun _ _ _ _ h => h) fun vs ns => ?_
  refine SimP.inspect (f := fun _ => Op.view.apply (v :: vs)) fun si₁ sw₁ hp₁ _ hq => ?_
  obtain ⟨hvs, si₀, sw₀, ⟨h₁, h₂⟩, he⟩ := hq
  subst h₁ h₂
  have hv₁ : VRel si₁.1.store sw₁.1.store w v := VRel.of_pins hvw.1 fun wd hwd => by
    have := hp₁.pend wd (List.mem_append_left _ hwd)
    exact ⟨this.1, this.2.1⟩
  rcases narrow_rel hv₁ hvs.1 fun win h => (hvs.2.1 win h).1 with
    ⟨f, h₁, h₂⟩ | ⟨y', y, h₁, h₂, h₃, h₄⟩
  · exact .inl ⟨f, h₁, h₂⟩
  · refine .inr ⟨y', y, h₁, h₂, h₃, fun win hw => ?_, ?_⟩
    · obtain ⟨win', hw', e₁, e₂⟩ := h₄ win hw
      rw [he]
      exact (hvw.2.1 win' hw').region e₁ e₂
    · refine Op.apply_hereditary (Value.Viewed.hereditary D) (fun u hu => ?_) h₁
      rcases List.mem_cons.1 hu with rfl | hu
      · exact hvw.2.2
      · exact hvs.2.2 u hu

/-- The source run, then the view before its offsets, related as the sources `X` track it,
then the rest. -/
theorem SimP.viewHead {X : List Shape} {src : Expr} {G₁ : Value → Value → IState → WState → Prop}
    {H : Value → Value → IState → WState → Prop} {m : Eval IState Value} {m' : Eval WState Value}
    {restI : Value → Eval IState Value} {restW : Value → Eval WState Value}
    (hm : SimP D c pend (fun _ _ => True) G₁ m m')
    (hhead : ∀ v v' si sw, Pre D c pend si sw → G₁ v v' si sw →
      ValG D c X v (viewOf sw.1 src v') si sw)
    (hrest : ∀ v w, SimP D c pend (ValG D c X v w) H (restI v) (restW w)) :
    SimP D c pend (fun _ _ => True) H (m >>= restI)
      (m' >>= fun v' => Eval.inspect (fun s => .ok (viewOf s.1 src v')) >>= restW) := by
  refine SimP.bind hm fun v v' => ?_
  show SimP D c pend (G₁ v v') H (Pure.pure v >>= restI) _
  exact SimP.bind (G := ValG D c X) (SimP.inspect (f := fun _ => .ok v)
    (f' := fun s => .ok (viewOf s.1 src v')) fun si sw hp _ hq =>
      .inr ⟨v, _, rfl, rfl, hhead v v' si sw hp hq⟩) fun a w => hrest a w

/-- The view of a place that takes no index: both models read the state alone for the
source, once they have the fuel. -/
theorem SimP.viewPlace (n : Nat) (hΓ : ScopeKeeps D c.Γ) {src : Expr} {x : Name}
    {ps : List Projection} {path : Path} (hplace : src.place? = some ⟨x, ps⟩)
    (hfp : fieldPath ps = some path)
    (hsrc : Sim D c pend (src.sources D c.Γ) (Stilt.eval D InPlace.memory n src)
      (Windows.eval D n src))
    {H : Value → Value → IState → WState → Prop} {restI : Value → Eval IState Value}
    {restW : Value → Eval WState Value}
    (hrest : ∀ v w, SimP D c pend (ValG D c (headSources D c.Γ [src]) v w) H (restI v)
      (restW w)) :
    SimP D c pend (fun _ _ => True) H (Stilt.eval D InPlace.memory n src >>= restI)
      (Windows.eval D n src >>= fun v' =>
        Eval.inspect (fun s => .ok (viewOf s.1 src v')) >>= restW) := by
  rcases eval_place n hplace hfp with ⟨h₁, h₂⟩ | ⟨h₁, g, h₂, hg0, hgf⟩
  · rw [h₁, h₂]
    exact SimP.outOfFuel
  · rw [h₁, h₂] at hsrc ⊢
    refine SimP.viewHead (SimP.inspect_ok hsrc) (fun v v' si sw hp hq => ?_) hrest
    obtain ⟨hv, hr, hg⟩ := hq
    refine viewOf_place_rel hp hΓ hplace hfp hv hr (fun h0 => ?_) fun h0 => hgf h0 sw v' hg
    rw [hg0 h0] at hg
    exact hg

/-- The view of any other operand: the value it reads, its sources its own. -/
theorem SimP.viewOther {src₀ src : Expr} {m : Eval IState Value} {m' : Eval WState Value}
    (hsrc : Sim D c pend (src₀.sources D c.Γ) m m')
    (hno₀ : ∀ x ps path, src₀.place? = some ⟨x, ps⟩ → fieldPath ps = some path → False)
    (hno : ∀ x ps path, src.place? = some ⟨x, ps⟩ → fieldPath ps = some path → False)
    {H : Value → Value → IState → WState → Prop} {restI : Value → Eval IState Value}
    {restW : Value → Eval WState Value}
    (hrest : ∀ v w, SimP D c pend (ValG D c (headSources D c.Γ [src₀]) v w) H (restI v)
      (restW w)) :
    SimP D c pend (fun _ _ => True) H (m >>= restI)
      (m' >>= fun v' => Eval.inspect (fun s => .ok (viewOf s.1 src v')) >>= restW) :=
  SimP.viewHead hsrc (fun _ _ _ _ _ hv => by
    rw [viewOf_other hno]
    exact ⟨hv.1, fun win hw => (hv.2.1 win hw).sub (sources_sub_head_other hno₀), hv.2.2⟩)
    hrest

/-- Making a view: its source evaluated, then a window on the place it names when that takes
no index (`viewOf`), held while the offsets run, then narrowed (views.making-view). -/
theorem SimP.view (n : Nat) (hΓ : ScopeKeeps D c.Γ) {src₀ src : Expr} {offs₀ offs : List Expr}
    (hi : Expr.Inst D src₀ src) (his : ExprsInst D offs₀ offs)
    (ih : ∀ c' : Ctx, ScopeKeeps D c'.Γ → ∀ e₀ e, Expr.Inst D e₀ e →
      RunsIn D c' (Stilt.eval D InPlace.memory n) (Windows.eval D n) e₀ e)
    (hr : (Expr.view (src₀ :: offs₀)).viewsRead D c.Γ c.R = true)
    (hc : (Expr.view (src₀ :: offs₀)).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.view (src₀ :: offs₀)).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.view (src :: offs)))
      (Windows.eval D (n + 1) (.view (src :: offs))) := by
  simp only [Expr.viewsRead, Bool.and_eq_true] at hr
  simp only [Expr.contained, exprsContained, Bool.and_eq_true] at hc
  have hsrc : Sim D c pend (src₀.sources D c.Γ) (Stilt.eval D InPlace.memory n src)
      (Windows.eval D n src) := ih c hΓ src₀ src hi c.R pend hr.1 hc.1
  have hrest := fun v w => SimP.narrowing (c := c) (pend := pend) (v := v) (w := w) his
    (fun e₀ e _ hi' => ih _ hΓ e₀ e hi') hr.2 hc.2
  show SimP D c pend _ (ValG D c (headSources D c.Γ [src₀])) _ _
  rw [eval_view_inPlace]
  show SimP D c pend _ _ _ (Windows.eval D n src >>= fun v' =>
    Eval.inspect (fun s => .ok (viewOf s.1 src v')) >>= fun w =>
      Eval.list (Windows.eval D n) offs >>= fun ns => Eval.inspect fun s => narrow s.1.store w ns)
  by_cases hyes : ∃ x ps path, src.place? = some ⟨x, ps⟩ ∧ fieldPath ps = some path
  · obtain ⟨x, ps, path, hplace, hfp⟩ := hyes
    obtain rfl := inst_eq_of_place _ rfl hi hplace hfp
    exact SimP.viewPlace n hΓ hplace hfp hsrc hrest
  · refine SimP.viewOther hsrc (fun x ps path h₁ h₂ => ?_)
      (fun x ps path h₁ h₂ => hyes ⟨x, ps, path, h₁, h₂⟩) hrest
    obtain rfl := inst_eq_of_place₀ _ rfl hi h₁ h₂
    exact hyes ⟨x, ps, path, h₁, h₂⟩

end Windows

end Stilt
