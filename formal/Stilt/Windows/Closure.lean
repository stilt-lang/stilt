import Stilt.Windows.Values

/-!
# A closure literal

A closure captures what its variables hold, and the model of windows what their windows read
(expressions.capture): both models capture the same values, which the checks accept, or fail
alike, so both make the same closure, one the checks of its literal accept (views.fixed).
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls} {c : Ctx} {pend : List (Window × Value)}

/-- Steps on each element that fail alike or give the same value, of which `P` holds: so do
their maps. -/
theorem mapM_same {α β : Type} {P : β → Prop} {f g : α → Except Fault β} :
    ∀ {l : List α}, (∀ a ∈ l, (∃ e, f a = .error e ∧ g a = .error e) ∨
      ∃ b, f a = .ok b ∧ g a = .ok b ∧ P b) →
      (∃ e, l.mapM f = .error e ∧ l.mapM g = .error e) ∨
        ∃ bs, l.mapM f = .ok bs ∧ l.mapM g = .ok bs ∧ ∀ b ∈ bs, P b
  | [], _ => .inr ⟨[], rfl, rfl, fun _ h => by cases h⟩
  | a :: l, h => by
    rcases h a List.mem_cons_self with ⟨e, h₁, h₂⟩ | ⟨b, h₁, h₂, h₃⟩
    · exact .inl ⟨e, by rw [List.mapM_cons, h₁]; rfl, by rw [List.mapM_cons, h₂]; rfl⟩
    · rcases mapM_same (l := l) fun a ha => h a (List.mem_cons_of_mem _ ha) with
        ⟨e, h₄, h₅⟩ | ⟨bs, h₄, h₅, h₆⟩
      · exact .inl ⟨e, by rw [List.mapM_cons, h₁, h₄]; rfl, by rw [List.mapM_cons, h₂, h₅]; rfl⟩
      · refine .inr ⟨b :: bs, by rw [List.mapM_cons, h₁, h₄]; rfl,
          by rw [List.mapM_cons, h₂, h₅]; rfl,
          fun b' hb' => ?_⟩
        rcases List.mem_cons.1 hb' with rfl | hb'
        · exact h₃
        · exact h₆ b' hb'

/-- Every variable's location is live in the store of windows. -/
theorem Fits.cell {sw : List (Option Value)} {env₀ : List (Name × Ref)} {In : List (Name × Value)}
    {L : Nat} : ∀ {Γ : ViewScope} {env : List (Name × Ref)},
      Fits (TopHolds sw env₀ In L) (BaseHolds sw) Γ env →
        ∀ xr ∈ env, ∃ y, cell sw xr.2.loc = .ok y
  | _, _, .base _ henv, xr, hxr => by
    obtain ⟨y, hy, -⟩ := henv xr hxr
    exact ⟨y, hy⟩
  | _, _, .cons _ htop hrest, xr, hxr => by
    rcases List.mem_cons.1 hxr with rfl | hxr
    · obtain ⟨y, hy, -⟩ := htop
      exact ⟨y, hy⟩
    · exact Fits.cell hrest xr hxr

/-- A variable captured in both models: the same value, which the checks accept, or the same
fault. -/
theorem capture_one {si : IState} {sw : WState} (hp : Pre D c pend si sw) {xr : Name × Ref}
    (hxr : xr ∈ sw.1.env) :
    (∃ e, ((xr.1, ·) <$> InPlace.deref si.1 xr.2 [] : Except Fault (Name × Value)) = .error e ∧
        ((xr.1, ·) <$> (deref sw.1 xr.2 [] >>= resolve sw.1.store)) = .error e) ∨
      ∃ b : Name × Value, (xr.1, ·) <$> InPlace.deref si.1 xr.2 [] = .ok b ∧
        (xr.1, ·) <$> (deref sw.1 xr.2 [] >>= resolve sw.1.store) = .ok b ∧ b.2.Viewed D := by
  obtain ⟨y, hy⟩ := Fits.cell hp.fits xr hxr
  obtain ⟨u, hu, hyu⟩ := hp.agree.live xr.2.loc y (cell_eq_ok hy)
  have hi : InPlace.deref si.1 xr.2 [] = u.get xr.2.path := by
    simp only [InPlace.deref, hu, List.append_nil]
  have hw : deref sw.1 xr.2 [] = getW sw.1.store y xr.2.path := by
    simp only [deref, hy, List.append_nil]
    rfl
  rw [hi, hw]
  rcases getW_rel hyu.1 hyu.readAlike xr.2.path with ⟨f, h₁, h₂⟩ | ⟨z, z', h₁, h₂, h₃, h₄⟩
  · exact .inl ⟨f, by rw [h₂]; rfl, by rw [h₁]; rfl⟩
  · have hz : resolve sw.1.store z = .ok z' := by
      rw [resolve_eq_resolveIn fun w hw => hyu.readAlike w (h₄ w hw), h₃]
    refine .inr ⟨(xr.1, z'), ?_, ?_, ?_⟩
    · rw [h₂]; rfl
    · rw [h₁]
      show (xr.1, ·) <$> resolve sw.1.store z = _
      rw [hz]; rfl
    · exact (hp.agree.viewed u (List.mem_of_getElem? hu)).get h₂

/-- Both models capture the same values, which the checks accept, or fail alike. -/
theorem capture_rel {si : IState} {sw : WState} (hp : Pre D c pend si sw) :
    (∃ e, InPlace.memory.capture si = .error e ∧ memory.capture sw = .error e) ∨
      ∃ cs, InPlace.memory.capture si = .ok cs ∧ memory.capture sw = .ok cs ∧
        ∀ xv ∈ cs, xv.2.Viewed D := by
  show (∃ e, si.1.env.mapM (fun (x, r) => (x, ·) <$> InPlace.deref si.1 r []) = .error e ∧
      sw.1.env.mapM (fun (x, r) => (x, ·) <$> (deref sw.1 r [] >>= resolve sw.1.store)) =
        .error e) ∨
      ∃ cs, si.1.env.mapM (fun (x, r) => (x, ·) <$> InPlace.deref si.1 r []) = .ok cs ∧
      sw.1.env.mapM (fun (x, r) => (x, ·) <$> (deref sw.1 r [] >>= resolve sw.1.store)) = .ok cs ∧
        ∀ xv ∈ cs, xv.2.Viewed D
  rw [← hp.agree.env]
  exact mapM_same fun xr hxr => capture_one hp hxr

/-- A closure literal: the same closure on both sides, which the checks of its literal
accept. -/
theorem SimP.closure (n : Nat) (hΓ : ScopeKeeps D c.Γ) {ps₀ ps : List Param} {r₀ r : Ty} {ρ₀ ρ : Row} {b₀ b : Expr}
    (hi : Expr.Inst D (.closure ps₀ r₀ ρ₀ b₀) (.closure ps r ρ b))
    (hr : (Expr.closure ps₀ r₀ ρ₀ b₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.closure ps₀ r₀ ρ₀ b₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.closure ps₀ r₀ ρ₀ b₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.closure ps r ρ b))
      (Windows.eval D (n + 1) (.closure ps r ρ b)) := by
  cases hi with
  | closure _ _ hnd hps _ hb =>
  simp only [Expr.viewsRead] at hr
  simp only [Expr.contained, Bool.and_eq_true] at hc
  have hck : ClosureChecked D ps b := ⟨c.Γ, ps₀, r₀, b₀, hΓ, hnd, hps, hb, hr, hc.1,
    hc.2⟩
  refine SimP.bind (G := fun cs cs' _ _ => cs' = cs ∧ ∀ xv ∈ cs, xv.2.Viewed D)
    (SimP.inspect fun si sw hp _ _ => (capture_rel hp).imp_right fun ⟨cs, h₁, h₂, h₃⟩ =>
      ⟨cs, cs, h₁, h₂, rfl, h₃⟩) fun cs cs' => ?_
  refine SimP.pure fun _ _ _ ⟨he, hv⟩ => ?_
  rw [he]
  exact ⟨VRel.free rfl, fun w hw => (by simp [windowsOf] at hw),
    .closure (fun xv hxv => hv xv (List.mem_filter.1 hxv).1) hck⟩

end Windows

end Stilt
