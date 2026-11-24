import Stilt.Windows.Store

/-!
# States that agree, through the changes of a body

Binding a variable keeps two states that agree; so does ending a binding whose location no
window reads, freeing locations that no window on a location before them reads, and changing
both worlds alike.
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls}

theorem getElem?_append_one {β : Type} (l : List β) (b : β) (ℓ : Nat) :
    (l ++ [b])[ℓ]? = if ℓ < l.length then l[ℓ]? else if ℓ = l.length then some b else none := by
  by_cases h : ℓ < l.length
  · simp [h, List.getElem?_append_left h]
  · simp only [h, ↓reduceIte]
    rw [List.getElem?_append_right (by omega)]
    by_cases h' : ℓ = l.length
    · subst h'; simp
    · simp only [h', ↓reduceIte]; simp; omega

theorem Agree.bind {si : InPlace.State × World} {sw : State × World} (h : Agree D si sw)
    (x : Name) {w v : Value} (hv : VRel si.1.store sw.1.store w v) (hvv : v.Viewed D) :
    Agree D (InPlace.bind si.1 x v, si.2) (Windows.bind sw.1 x w, sw.2) := by
  have hlen := h.length
  have hw : ∀ win ∈ windowsOf w, win.1 < si.1.store.length := fun win hm => (hv.2 win hm).ltI
  refine ⟨by simp [InPlace.bind, Windows.bind, h.env, hlen], h.world,
    by simp [InPlace.bind, Windows.bind, hlen], fun u hu => ?_, h.cells, ?_, ?_, ?_⟩
  · simp only [InPlace.bind, List.mem_append, List.mem_singleton] at hu
    rcases hu with hu | rfl
    · exact h.viewed u hu
    · exact hvv
  · refine List.Pairwise.cons (fun xr hxr => ?_) h.disjoint
    have := h.valid xr hxr
    exact .inl (by simp; omega)
  · intro xr hxr
    simp only [InPlace.bind, List.mem_cons, List.length_append, List.length_singleton] at hxr ⊢
    rcases hxr with rfl | hxr
    · simp
    · have := h.valid xr hxr
      omega
  · intro ℓ y hy
    simp only [Windows.bind, getElem?_append_one, hlen] at hy
    simp only [InPlace.bind, getElem?_append_one]
    by_cases hl : ℓ < si.1.store.length
    · simp only [hl, ↓reduceIte] at hy
      simp only [hl, ↓reduceIte]
      obtain ⟨u, hu, hr⟩ := h.live ℓ y (by rw [← hlen] at hl; simpa [hlen] using hy)
      refine ⟨u, hu, hr.region (fun win hm => regionW_append _ ?_) (fun win hm => regionI_append _ ?_)⟩
      · rw [hlen]; exact (hr.2 win hm).ltI
      · exact (hr.2 win hm).ltI
    · simp only [hl, ↓reduceIte] at hy ⊢
      by_cases he : ℓ = si.1.store.length
      · simp only [he, ↓reduceIte] at hy ⊢
        cases hy
        refine ⟨v, rfl, hv.region (fun win hm => regionW_append _ ?_)
          (fun win hm => regionI_append _ (hw win hm))⟩
        rw [hlen]; exact hw win hm
      · simp only [he, ↓reduceIte] at hy; cases hy

theorem Agree.unbind {si : InPlace.State × World} {sw : State × World} (h : Agree D si sw)
    {y : Name} {r : Ref} {env : List (Name × Ref)} (henv : si.1.env = (y, r) :: env)
    (hfree : ∀ (ℓ : Nat) x, sw.1.store[ℓ]? = some (some x) → ℓ ≠ r.loc →
      ∀ w ∈ windowsOf x, w.1 ≠ r.loc) :
    Agree D ({ si.1 with env := env }, si.2) (Windows.unbind sw.1, sw.2) := by
  have hsw : sw.1.env = (y, r) :: env := h.env.trans henv
  have hu : Windows.unbind sw.1 = ⟨env, sw.1.store.set r.loc none⟩ := by
    simp only [Windows.unbind, hsw]
  rw [hu]
  refine ⟨rfl, h.world, by simp [h.length], h.viewed, h.cells, ?_, ?_, ?_⟩
  · have := h.disjoint
    rw [henv] at this
    exact this.of_cons
  · intro xr hxr
    exact h.valid xr (by rw [henv]; exact List.mem_cons_of_mem _ hxr)
  · intro ℓ x hx
    by_cases hl : ℓ = r.loc
    · subst hl
      by_cases hlt : r.loc < sw.1.store.length
      · simp [List.getElem?_set_self hlt] at hx
      · rw [List.getElem?_eq_none (by simp; omega)] at hx
        cases hx
    · rw [List.getElem?_set_ne (Ne.symm hl)] at hx
      obtain ⟨u, hu, hr⟩ := h.live ℓ x hx
      exact ⟨u, hu, hr.region (fun win hm => regionW_set_ne _ (Ne.symm (hfree ℓ x hx hl win hm)))
        fun _ _ => rfl⟩

theorem Agree.free {si : InPlace.State × World} {sw : State × World} (h : Agree D si sw) (n : Nat)
    (hlt : ∀ (ℓ : Nat) x, ℓ < n → sw.1.store[ℓ]? = some (some x) → ∀ w ∈ windowsOf x, w.1 < n) :
    Agree D si (freeFrom n sw) := by
  refine ⟨h.env, h.world, by rw [freeFrom_store, freeStore_length]; exact h.length, h.viewed,
    h.cells, h.disjoint, h.valid, ?_⟩
  intro ℓ x hx
  rw [freeFrom_store] at hx
  by_cases hl : ℓ < n
  · rw [freeStore_getElem?_lt _ hl] at hx
    obtain ⟨u, hu, hr⟩ := h.live ℓ x hx
    exact ⟨u, hu, hr.region (fun win hm => regionW_freeStore (hlt ℓ x hl hx win hm)) fun _ _ => rfl⟩
  · exact absurd hx (freeStore_getElem?_ge _ (by omega))

theorem Agree.setWorld {si : InPlace.State × World} {sw : State × World} (h : Agree D si sw)
    {x : World} (hx : x.All (Value.Viewed D)) : Agree D (si.1, x) (sw.1, x) :=
  ⟨h.env, rfl, h.length, h.viewed, hx, h.disjoint, h.valid, h.live⟩

end Windows

end Stilt
