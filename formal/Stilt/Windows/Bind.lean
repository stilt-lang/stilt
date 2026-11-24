import Stilt.Windows.Kept

/-!
# Binding a variable

A variable of the body bound at a new location, the one past the store's end, with what the
checks know of it: the states keep the simulation in the scope of the binding, whose reads hide
the variable's name and hold its sources (views.reads-that-last).
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls}

/-- The context of the scope of `x`, bound as `b` says, with the reads `R` and the result's
parameters `P`. -/
def Ctx.scope (c : Ctx) (x : Name) (b : ViewBinding) (R : List Shape) (P : List Name) : Ctx :=
  { c with Γ := (x, b) :: c.Γ, R := R, P := P }

/-- What the checks give of the scope of a binding: a variable of the body's own, reads that
keep the shapes of other variables, hide `x`'s and, for a binding with a written type, hold its
sources, and result's parameters of the body that no longer name `x`. -/
structure ScopeOk (c : Ctx) (x : Name) (b : ViewBinding) (R : List Shape) (P : List Name) :
    Prop where
  param : b.param = false
  keeps : ∀ t ∈ c.R, t.root ≠ x → t ∈ R
  hides : ∀ t ∈ R, t.root ≠ x
  holds : b.type.isSome = true → ∀ s ∈ b.sources, s.root ≠ x → s ∈ R
  sub : ∀ y ∈ P, y ∈ c.P
  erased : x ∉ P

/-- What a new variable's location holds: a value related to the in-place one, whose windows
the binding's sources track if it has a written type, and none otherwise. -/
def BindsAs (D : Decls) (c : Ctx) (b : ViewBinding) (v w : Value) (si : IState) (sw : WState) :
    Prop :=
  VRel si.1.store sw.1.store w v ∧ v.Viewed D ∧
    if b.type.isSome then ∀ win ∈ windowsOf w, Tracked sw.1.env c.In b.sources win else Free w

theorem env_pairwise {si : IState} {sw : WState} (h : Agree D si sw) :
    sw.1.env.Pairwise fun a b => a.2.Disjoint b.2 := by
  rw [h.env]; exact h.disjoint

theorem env_lt {si : IState} {sw : WState} (h : Agree D si sw) :
    ∀ xr ∈ sw.1.env, xr.2.loc < sw.1.store.length := by
  rw [h.env, h.length]; exact h.valid

theorem cell_windows_lt {si : IState} {sw : WState} (h : Agree D si sw) {ℓ : Nat} {y : Value}
    (hy : cell sw.1.store ℓ = .ok y) : ∀ w ∈ windowsOf y, w.1 < sw.1.store.length := by
  obtain ⟨u, -, hr⟩ := h.live ℓ y (cell_eq_ok hy)
  exact fun w hw => (hr.2 w hw).lt

theorem getElem?_bind_lt {st : List (Option Value)} {w : Value} {ℓ : Nat} (h : ℓ < st.length) :
    (st ++ [some w])[ℓ]? = st[ℓ]? :=
  List.getElem?_append_left h

/-- The variables after a binding fit the scope with it: the new one at the new location, the
others as they were. -/
theorem Pre.fits_bind {c : Ctx} {pend : List (Window × Value)} {si : IState} {sw : WState}
    (hp : Pre D c pend si sw) {x : Name} {b : ViewBinding} (hb : b.param = false) {v w : Value}
    (hv : BindsAs D c b v w si sw) :
    Fits (TopHolds (sw.1.store ++ [some w]) ((x, ⟨sw.1.store.length, []⟩) :: sw.1.env) c.In c.L)
      (BaseHolds (sw.1.store ++ [some w])) ((x, b) :: c.Γ)
      ((x, ⟨sw.1.store.length, []⟩) :: sw.1.env) := by
  have hag := hp.agree
  have hlt := env_lt hag
  have hsub : ∀ xr ∈ sw.1.env, xr ∈ (x, (⟨sw.1.store.length, []⟩ : Ref)) :: sw.1.env :=
    fun xr h => List.mem_cons_of_mem _ h
  have hkept : ∀ ℓ, ℓ < sw.1.store.length → Kept sw.1.store (sw.1.store ++ [some w]) ℓ :=
    fun ℓ h => getElem?_bind_lt h
  refine .cons rfl ⟨w, ?_, ?_⟩ (Fits.mono_mem hp.fits (fun xb xr older hs h => ?_) fun xr hxr h => ?_)
  · show cell (sw.1.store ++ [some w]) sw.1.store.length = .ok w
    simp only [cell, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    refine ⟨trivial, hp.start, fun yr hyr => hlt yr hyr, ?_⟩
    obtain ⟨-, -, ht⟩ := hv
    split
    · rename_i hs
      simp only [hs, ↓reduceIte] at ht
      exact fun win hw => (ht win hw).env_mono hsub
    · rename_i hs
      simpa [hs] using ht
  · have hxr : xr ∈ sw.1.env := hs.subset List.mem_cons_self
    exact h.transport (hkept _ (hlt xr hxr))
      (fun y hy w' hw' => regionW_kept (hkept _ (cell_windows_lt hag hy w' hw')))
      (fun _ _ _ _ _ ht => ht.env_mono hsub) fun _ h => h
  · exact h.transport (hkept _ (hlt xr hxr))

theorem regionW_lt_of_pend {c : Ctx} {pend : List (Window × Value)} {si : IState} {sw : WState}
    (hp : Pre D c pend si sw) : ∀ wd ∈ pend, wd.1.1 < sw.1.store.length :=
  fun wd hwd => regionW_lt (hp.pend wd hwd).1

/-- Binding a variable at the new location keeps the simulation, in the binding's scope. -/
theorem Pre.bind {c : Ctx} {pend : List (Window × Value)} {si : IState} {sw : WState}
    (hp : Pre D c pend si sw) {x : Name} {b : ViewBinding} {R : List Shape} {P : List Name}
    (hb : b.param = false) {v w : Value} (hv : BindsAs D c b v w si sw) :
    Pre D (c.scope x b R P) pend (InPlace.bind si.1 x v, si.2) (Windows.bind sw.1 x w, sw.2) := by
  have hag := hp.agree
  have hlen := hag.length
  have hwlt : ∀ win ∈ windowsOf w, win.1 < sw.1.store.length :=
    fun win hm => (hv.1.2 win hm).lt
  refine ⟨hag.bind x hv.1 hv.2.1, hp.fits_bind hb hv, fun ℓ y hl hy => ?_, fun ℓ y hl hy => ?_,
    fun wd hwd => ?_, ?_, fun ℓ y hl hy => ?_⟩
  · have hn : ℓ < sw.1.store.length := Nat.lt_of_lt_of_le hl hp.start
    rw [show (Windows.bind sw.1 x w, sw.2).1.store = sw.1.store ++ [some w] from rfl,
      getElem?_bind_lt hn] at hy
    exact hp.outer ℓ y hl hy
  · simp only [Windows.bind] at hy ⊢
    by_cases hn : ℓ < sw.1.store.length
    · rw [getElem?_bind_lt hn] at hy
      obtain ⟨⟨xr, hxr, he⟩, hw⟩ := hp.owned ℓ y hl hy
      exact ⟨⟨xr, List.mem_cons_of_mem _ hxr, he⟩, hw⟩
    · rw [List.getElem?_append_right (by omega)] at hy
      by_cases he : ℓ = sw.1.store.length
      · subst he
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hy
        subst hy
        exact ⟨⟨_, List.mem_cons_self, rfl⟩, hwlt⟩
      · rw [List.getElem?_eq_none (by simp; omega)] at hy
        cases hy
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := hp.pend wd hwd
    have hl := regionW_lt h₁
    refine ⟨?_, ?_, h₃, h₄⟩
    · show regionW (sw.1.store ++ [some w]) wd.1 = _
      rw [regionW_append _ hl, h₁]
    · show regionI (si.1.store ++ [v]) wd.1 = _
      rw [regionI_append _ (hlen ▸ hl), h₂]
  · show c.L ≤ (sw.1.store ++ [some w]).length
    simp only [List.length_append, List.length_singleton]
    exact Nat.le_succ_of_le hp.start
  · have hn : ℓ < sw.1.store.length := Nat.lt_of_lt_of_le hl hp.start
    obtain ⟨z, hz⟩ := hp.alive ℓ y hl hy
    exact ⟨z, by show (sw.1.store ++ [some w])[ℓ]? = _; rw [getElem?_bind_lt hn, hz]⟩

theorem mem_hide {R : List Shape} {x : Name} {t : Shape} : t ∈ hide R x ↔ t ∈ R ∧ t.root ≠ x := by
  simp [hide]

/-- The reads in a binding's scope guard what they guarded, and what the binding's sources
track. -/
theorem Guards.bind {c : Ctx} {pend : List (Window × Value)} {si : IState} {sw : WState}
    (hp : Pre D c pend si sw) (hg : Guards D c pend sw.1.env) {x : Name} {b : ViewBinding}
    {R : List Shape} {P : List Name} (hok : ScopeOk c x b R P) :
    Guards D (c.scope x b R P) pend ((x, ⟨sw.1.store.length, []⟩) :: sw.1.env) := by
  have hag := hp.agree
  have hlt := env_lt hag
  have hn : c.L ≤ sw.1.store.length := hp.start
  have hd : ((x, (⟨sw.1.store.length, []⟩ : Ref)) :: sw.1.env).Pairwise fun a b => a.2.Disjoint b.2 :=
    List.Pairwise.cons (fun xr hxr => .inl (by have := hlt xr hxr; simp; omega)) (env_pairwise hag)
  have hbr : ∀ xv ∈ c.In, ∀ w ∈ windowsOf xv.2, w.1 < c.L ∧
      Unreached ((x, (⟨sw.1.store.length, []⟩ : Ref)) :: sw.1.env) w := fun xv hxv w hw =>
    ⟨(hg.brought xv hxv w hw).1, (hg.brought xv hxv w hw).2.bind x (by
      have := (hg.brought xv hxv w hw).1; omega)⟩
  refine ⟨.cons rfl (fun hpar hty w hw ht => ?_) (Fits.mono_mem hg.fenced
      (fun xb xr older hs h hpar hty w hw ht => ?_) fun _ _ _ => trivial),
    hbr, fun ℓ hl w hw => ⟨(hg.old ℓ hl w hw).1, (hg.old ℓ hl w hw).2.bind x (by
      have := (hg.old ℓ hl w hw).1; have := hn; simp only [Ctx.scope] at *; omega)⟩,
    fun wd hwd => ?_, fun xr hxr hl y hy => ?_⟩
  · refine guarded_of_tracked hd (fun xv hxv w' hw' => (hbr xv hxv w' hw').2) (fun s hs => ?_) ht
    by_cases hx : s.root = x
    · refine .inr fun r hr => ?_
      rw [hx] at hr
      simp only [List.lookup_cons_self, Option.some.injEq] at hr
      subst hr
      exact disjoint_fresh hw
    · exact .inl (hok.holds hty s hs hx)
  · have hxr : xr ∈ sw.1.env := hs.subset List.mem_cons_self
    have hw' : w.1 ≠ sw.1.store.length := by have := hlt xr hxr; omega
    exact Guarded.bind_hide (h hpar hty w hw (ht.pop hw')) x (by have := hlt xr hxr; omega) hok.keeps
  · exact Guarded.bind_hide (hg.pend wd hwd) x (regionW_lt_of_pend hp wd hwd) hok.keeps
  · rcases List.mem_cons.1 hxr with rfl | hxr
    · simp only [Ctx.scope] at hl; omega
    · exact hg.start xr hxr hl y hy

end Windows

end Stilt
