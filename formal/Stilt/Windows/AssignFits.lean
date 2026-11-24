import Stilt.Windows.AssignStore

/-!
# The variable an assignment writes

A variable that an assignment of a view writes is one of the body's own with a written type, so
it is one of the newest variables, and every variable that a source of the view names, which the
checks know to outlive it, is older (`Fits.named`). Rebuilding what the simulation knows of the
variables after a write knows which entry is the written variable's (`Fits.mono_at`).
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

theorem lookup_of_findIdx {x : Name} :
    ∀ {Γ : ViewScope} {i : Nat}, Γ.findIdx? (·.1 == x) = some i → ∃ b, Γ.lookup x = some b
  | [], _, h => by simp at h
  | (z, bz) :: Γ, i, h => by
    by_cases hz : x = z
    · subst hz
      exact ⟨bz, List.lookup_cons_self⟩
    · rw [lookup_cons_ne hz]
      rw [List.findIdx?_cons] at h
      have hzx : (z == x) = false := by simp [Ne.symm hz]
      simp only [hzx, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨j, hj, -⟩ := h
      exact lookup_of_findIdx hj

/-- A variable that another outlives is in scope. -/
theorem outlives_lookup {Γ : ViewScope} {y x : Name} (h : Γ.outlives y x = true) :
    ∃ b, Γ.lookup x = some b := by
  unfold ViewScope.outlives at h
  split at h
  · rename_i i j hi _
    exact lookup_of_findIdx hi
  · cases h

/-- Outliving past a binding of neither name. -/
theorem outlives_cons {xb : Name × ViewBinding} {Γ : ViewScope} {y x : Name}
    (h : ViewScope.outlives (xb :: Γ) y x = true) (hx : xb.1 ≠ x) :
    xb.1 ≠ y ∧ Γ.outlives y x = true := by
  unfold ViewScope.outlives at h ⊢
  have hxb : (xb.1 == x) = false := by simp [hx]
  simp only [List.findIdx?_cons, hxb, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hy : xb.1 = y
  · have hyb : (xb.1 == y) = true := by simp [hy]
    simp only [hyb, ↓reduceIte] at h
    split at h
    · rename_i i j hi hj
      cases hj
      simp only [Option.map_eq_some_iff] at hi
      obtain ⟨k, -, rfl⟩ := hi
      simp at h
    · cases h
  · have hyb : (xb.1 == y) = false := by simp [hy]
    simp only [hyb, Bool.false_eq_true, ↓reduceIte] at h
    refine ⟨hy, ?_⟩
    split at h
    · rename_i i j hi hj
      simp only [Option.map_eq_some_iff] at hi hj
      obtain ⟨i', hi', rfl⟩ := hi
      obtain ⟨j', hj', rfl⟩ := hj
      simp only [hi', hj', decide_eq_true_eq] at h ⊢
      simp at h
      omega
    · cases h

/-- A variable whose binding is no parameter is one of the newest, and every variable named by
a name the checks know outlives it is older. -/
theorem Fits.named {top : Name × ViewBinding → Name × Ref → List (Name × Ref) → Prop}
    {base : Name × Ref → Prop} {x : Name} {b : ViewBinding} :
    ∀ {Γ : ViewScope} {env : List (Name × Ref)}, Fits top base Γ env → Γ.lookup x = some b →
      b.param = false → ∃ r older, env.lookup x = some r ∧ top (x, b) (x, r) older ∧
        ∀ y, Γ.outlives y x = true → y ≠ x → ∀ r', (y, r') ∈ env → (y, r') ∈ older
  | _, _, .base hΓ _, hl, hp => by
    have := hΓ _ (mem_of_lookup hl)
    simp [hp] at this
  | _, _, .cons (xb := ⟨z, bz⟩) (xr := ⟨z', rz⟩) (Γ := Γ) (env := env) hx htop hrest, hl, hp => by
    simp only at hx
    subst hx
    by_cases hz : x = z
    · subst hz
      simp only [List.lookup_cons_self, Option.some.injEq] at hl
      subst hl
      refine ⟨rz, env, List.lookup_cons_self, htop, fun y _ hy r' hm => ?_⟩
      rcases List.mem_cons.1 hm with he | hm
      · cases he
        exact absurd rfl hy
      · exact hm
    · rw [lookup_cons_ne hz] at hl
      obtain ⟨r, older, hr, ht, hold⟩ := Fits.named hrest hl hp
      refine ⟨r, older, by rw [lookup_cons_ne hz]; exact hr, ht, fun y hyo hy r' hm => ?_⟩
      obtain ⟨hzy, hyo'⟩ := outlives_cons (xb := (z, bz)) hyo (Ne.symm hz)
      rcases List.mem_cons.1 hm with he | hm
      · cases he
        exact absurd rfl hzy
      · exact hold y hyo' hy r' hm

/-- With no repeated variable, the first one of a name is not the head when it is further on. -/
theorem head_ne {xr₀ : Name × Ref} {env : List (Name × Ref)} {x : Name} {r : Ref}
    (hnd : (xr₀ :: env).Nodup) (hl : (x, r) ∈ xr₀ :: env → (xr₀ :: env).lookup x = some r)
    (hm : (x, r) ∈ env) : xr₀.1 ≠ x := by
  intro he
  obtain ⟨z, rz⟩ := xr₀
  simp only at he
  subst he
  have := hl (List.mem_cons_of_mem _ hm)
  simp only [List.lookup_cons_self, Option.some.injEq] at this
  subst this
  exact (List.nodup_cons.1 hnd).1 hm

theorem lookup_tail {xr₀ : Name × Ref} {env : List (Name × Ref)} {x : Name} {r : Ref}
    (hnd : (xr₀ :: env).Nodup) (hl : (x, r) ∈ xr₀ :: env → (xr₀ :: env).lookup x = some r) :
    (x, r) ∈ env → env.lookup x = some r := fun hm => by
  have hne := head_ne hnd hl hm
  have := hl (List.mem_cons_of_mem _ hm)
  obtain ⟨z, rz⟩ := xr₀
  rwa [lookup_cons_ne (Ne.symm hne)] at this

/-- `Fits.mono`, knowing of the entry of `x` that it is the binding the scope gives `x`, and of
the rest of the variables, if `x` is one of them, that the scope gives `x` a parameter. -/
theorem Fits.mono_at {top top' : Name × ViewBinding → Name × Ref → List (Name × Ref) → Prop}
    {base base' : Name × Ref → Prop} {x : Name} {r : Ref} :
    ∀ {Γ : ViewScope} {env : List (Name × Ref)}, Fits top base Γ env → env.Nodup →
      ((x, r) ∈ env → env.lookup x = some r) →
      (∀ xb xr older, xr :: older <:+ env → (xr = (x, r) → Γ.lookup x = some xb.2) →
        top xb xr older → top' xb xr older) →
      (∀ xr ∈ env, (xr = (x, r) → ∀ b, Γ.lookup x = some b → b.param = true) → base xr →
        base' xr) → Fits top' base' Γ env
  | _, _, .base hΓ henv, _, _, _, hb =>
    .base hΓ fun xr hxr => hb xr hxr (fun _ _ hl => hΓ _ (mem_of_lookup hl)) (henv xr hxr)
  | _, _, .cons (xb := ⟨z, bz⟩) (xr := xr₀) (Γ := Γ) (env := env) hx htop hrest, hnd, hl, ht,
    hb => by
    have hne : (x, r) ∈ env → z ≠ x := fun hm h => by
      have hx' : z = xr₀.1 := hx
      exact head_ne hnd hl hm (hx' ▸ h)
    refine .cons hx (ht _ _ _ (List.suffix_refl _) (fun he => ?_) htop)
      (Fits.mono_at hrest (List.nodup_cons.1 hnd).2 (lookup_tail hnd hl) (fun xb xr older hs hxr h =>
        ht xb xr older (hs.trans (List.suffix_cons _ _)) (fun he => ?_) h) fun xr hxr hxr' h =>
        hb xr (List.mem_cons_of_mem _ hxr) (fun he b hl' => ?_) h)
    · subst he
      simp only at hx
      subst hx
      exact List.lookup_cons_self
    · subst he
      rw [lookup_cons_ne (Ne.symm (hne (hs.subset List.mem_cons_self)))]
      exact hxr rfl
    · subst he
      rw [lookup_cons_ne (Ne.symm (hne hxr))] at hl'
      exact hxr' rfl b hl'

end Windows

end Stilt
