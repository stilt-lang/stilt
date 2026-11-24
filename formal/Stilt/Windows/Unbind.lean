import Stilt.Windows.Bind

/-!
# Ending a binding

When the scope of a variable of the body ends, its location is freed. No live window reads it:
a location of the callers holds windows before the body's locations, one of the body's own
holds windows on older locations, a waiting window is guarded by reads that hide the variable,
and the value the scope gives reads no source of the variable's name (views.escaping, E0422).
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls}

theorem Shape.root_of_overlaps {s t : Shape} (h : s.overlaps t = true) : s.root = t.root := by
  simp only [Shape.overlaps, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- A region the reads of a scope guard is not the location of its variable, as they hide it. -/
theorem Guarded.ne_fresh {R : List Shape} {env : List (Name × Ref)} {x : Name} {n : Nat}
    {w : Window} (h : InPlace.Guarded R ((x, ⟨n, []⟩) :: env) w.ref.toPath)
    (hR : ∀ t ∈ R, t.root ≠ x) : w.1 ≠ n := by
  intro hw
  have := h x ⟨n, []⟩ List.lookup_cons_self [] (by
    simp only [InPlace.Ref.toPath, List.append_nil, Window.ref, hw]
    exact not_disjoint_of_prefix (List.prefix_cons_inj _ |>.2 (List.nil_prefix)))
  obtain ⟨t, ht, ho⟩ := InPlace.unread_eq_false.1 this
  exact hR t ht (Shape.root_of_overlaps ho).symm

/-- The facts of the end of a scope: the states after its body, from states with the variable
at the location `n` past the end of the store it started with. -/
structure Ending (D : Decls) (c : Ctx) (x : Name) (b : ViewBinding) (R : List Shape)
    (P : List Name) (pend : List (Window × Value)) (env : List (Name × Ref)) (n : Nat)
    (si : IState) (sw : WState) : Prop where
  pre : Pre D (c.scope x b R P) pend si sw
  vars : sw.1.env = (x, ⟨n, []⟩) :: env
  guards : Guards D (c.scope x b R P) pend ((x, ⟨n, []⟩) :: env)
  older : ∀ xr ∈ env, xr.2.loc < n
  past : c.L ≤ n

theorem kept_set {st : List (Option Value)} {n ℓ : Nat} (hl : ℓ ≠ n) : Kept st (st.set n none) ℓ :=
  List.getElem?_set_ne (Ne.symm hl)

namespace Ending

variable {c : Ctx} {x : Name} {b : ViewBinding} {R : List Shape} {P : List Name}
  {pend : List (Window × Value)} {env : List (Name × Ref)} {n : Nat} {si : IState} {sw : WState}

/-- No live window but the variable's own location's reads it. -/
theorem free (h : Ending D c x b R P pend env n si sw) :
    ∀ (ℓ : Nat) y, sw.1.store[ℓ]? = some (some y) → ℓ ≠ n → ∀ w ∈ windowsOf y, w.1 ≠ n := by
  intro ℓ y hy hl w hw
  by_cases hL : ℓ < c.L
  · have := (h.guards.old ℓ hL w ((h.pre.outer ℓ y hL hy).1 w hw)).1
    have := h.past
    omega
  · obtain ⟨⟨xr, hxr, he⟩, hlt⟩ := h.pre.owned ℓ y (by simp [Ctx.scope]; omega) hy
    have hw' := hlt w hw
    rw [h.vars] at hxr
    rcases List.mem_cons.1 hxr with rfl | hxr
    · simp at he; omega
    · have := h.older xr hxr
      rw [he] at this
      simp at this
      omega

theorem pend_ne (h : Ending D c x b R P pend env n si sw) (hok : ScopeOk c x b R P) :
    ∀ wd ∈ pend, wd.1.1 ≠ n :=
  fun wd hwd => Guarded.ne_fresh (h.guards.pend wd hwd) hok.hides

/-- A window that the variables of the scope track through sources of other names lies before
the variable's location, and the variables without it track it. -/
theorem tracked {S : List Shape} (h : Ending D c x b R P pend env n si sw)
    (hS : ∀ s ∈ S, s.root ≠ x) {w : Window} (ht : Tracked sw.1.env c.In S w) :
    w.1 ≠ n ∧ Tracked env c.In S w := by
  obtain ⟨s, hs, ⟨r, hr, q, hq, hpre⟩ | hb⟩ := ht
  · rw [h.vars] at hr
    rcases List.mem_cons.1 hr with he | hr
    · cases he
      exact absurd rfl (hS s hs)
    · have hloc := Window.loc_of_toPath hq
      have := h.older _ hr
      simp only at this
      exact ⟨by omega, s, hs, .inl ⟨r, hr, q, hq, hpre⟩⟩
  · obtain ⟨v, hv, w', hw', h1, -⟩ := id hb
    have := (h.guards.brought (s.root, v) hv w' hw').1
    have := h.past
    exact ⟨by simp only [Ctx.scope] at *; omega, s, hs, .inr hb⟩

theorem unbind_eq (h : Ending D c x b R P pend env n si sw) :
    Windows.unbind sw.1 = ⟨env, sw.1.store.set n none⟩ := by
  simp only [Windows.unbind, h.vars]


/-- The states after the scope, its variable unbound, keep the simulation in the context around
it. -/
theorem unbound (h : Ending D c x b R P pend env n si sw) (hok : ScopeOk c x b R P) :
    Pre D c pend (InPlace.memory.unbind si) (memory.unbind sw) := by
  obtain ⟨st, wo⟩ := si
  obtain ⟨sv, wv⟩ := sw
  have hp := h.pre
  have hsi : st.env = (x, ⟨n, []⟩) :: env := hp.agree.env.symm.trans h.vars
  have hu : (memory.unbind (sv, wv)) = (⟨env, sv.store.set n none⟩, wv) := by
    show (Windows.unbind sv, wv) = _
    rw [h.unbind_eq]
  have hiu : InPlace.memory.unbind (st, wo) = ({ st with env := env }, wo) := by
    show ({ st with env := st.env.tail }, wo) = _
    rw [hsi]; rfl
  rw [hu, hiu]
  have hfree := h.free
  have hag := hp.agree.unbind hsi (fun ℓ y hy hl w hw => hfree ℓ y hy hl w hw)
  rw [h.unbind_eq] at hag
  have hfits := hp.fits
  simp only [Ctx.scope] at hfits
  rw [h.vars] at hfits
  cases hfits with
  | base hΓ _ => exact absurd (hΓ _ List.mem_cons_self) (by simp [hok.param])
  | cons _ _ hrest =>
  refine ⟨hag, Fits.mono_mem hrest (fun xb xr older hs ht => ?_) (fun xr hxr hb => ?_),
    fun ℓ y hl hy => ?_, fun ℓ y hl hy => ?_, fun wd hwd => ?_, ?_, fun ℓ y hl hy => ?_⟩
  · have hxr : xr ∈ env := hs.subset List.mem_cons_self
    have hne : xr.2.loc ≠ n := by have := h.older xr hxr; omega
    refine ht.transport (kept_set hne) (fun y hy w hw => regionW_kept (kept_set (hfree _ y (cell_eq_ok hy) hne w hw)))
      (fun S w y hy hw htr => htr.pop (hfree _ y (cell_eq_ok hy) hne w hw)) fun _ h => h
  · have hne : xr.2.loc ≠ n := by have := h.older xr hxr; omega
    exact hb.transport (kept_set hne)
  · have hne : ℓ ≠ n := by have := h.past; omega
    simp only at hy
    rw [kept_set hne] at hy
    exact hp.outer ℓ y hl hy
  · have hne : ℓ ≠ n := fun he => by
      rw [he] at hy
      simp only at hy
      by_cases hlt : n < sv.store.length
      · simp [List.getElem?_set_self hlt] at hy
      · rw [List.getElem?_eq_none (by simp; omega)] at hy; cases hy
    simp only at hy
    rw [kept_set hne] at hy
    obtain ⟨⟨xr, hxr, he⟩, hw⟩ := hp.owned ℓ y hl hy
    rw [h.vars] at hxr
    rcases List.mem_cons.1 hxr with rfl | hxr
    · simp at he; omega
    · exact ⟨⟨xr, hxr, he⟩, hw⟩
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := hp.pend wd hwd
    exact ⟨by rw [show (⟨env, sv.store.set n none⟩ : State).store = sv.store.set n none from rfl,
      regionW_set_ne _ (Ne.symm (h.pend_ne hok wd hwd))]; exact h₁, h₂, h₃, h₄⟩
  · simpa [Ctx.scope] using hp.start
  · have hne : ℓ ≠ n := by have := h.past; omega
    obtain ⟨z, hz⟩ := hp.alive ℓ y hl hy
    exact ⟨z, by show (sv.store.set n none)[ℓ]? = _; rw [kept_set hne, hz]⟩

end Ending

end Windows

end Stilt
