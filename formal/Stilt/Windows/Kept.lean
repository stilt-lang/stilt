import Stilt.Windows.Read

/-!
# Locations a change keeps

A change of the store of windows that keeps a location's cell keeps what a window on it reads,
and what is read along a path through windows whose regions it keeps (`getW_congr`). What the
simulation knows of a variable holds across a change that keeps its location and the locations
its windows read.
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

/-- A change keeps the cell at a location. -/
def Kept (sw sw' : List (Option Value)) (ℓ : Nat) : Prop := sw'[ℓ]? = sw[ℓ]?

variable {sw sw' : List (Option Value)}

theorem cell_kept {ℓ : Nat} (h : Kept sw sw' ℓ) : cell sw' ℓ = cell sw ℓ := by
  unfold cell Kept at *
  rw [h]

theorem regionW_kept {w : Window} (h : Kept sw sw' w.1) : regionW sw' w = regionW sw w := by
  simp only [regionW, cell_kept h]

theorem part_kept {w : Window} (h : Kept sw sw' w.1) :
    part sw' w.1 w.2.1 w.2.2 = part sw w.1 w.2.1 w.2.2 := by
  rw [part_eq_region, part_eq_region, regionW_kept h]

/-- Reading along a path through windows whose regions a change keeps reads the same. -/
theorem getW_congr : ∀ (y : Value) (p : Path), (∀ w ∈ windowsOf y, regionW sw' w = regionW sw w) →
    getW sw' y p = getW sw y p
  | _, [], _ => by cases ‹Value› <;> rfl
  | .window loc path ranges, s :: p, h => by
    have := h (loc, path, ranges) (by simp [windowsOf])
    have hp : part sw' loc path ranges = part sw loc path ranges := by
      rw [part_eq_region sw' (loc, path, ranges), part_eq_region sw (loc, path, ranges), this]
    simp only [getW]
    rw [hp]
  | .record R fs, .field f :: p, h => by
    simp only [getW]
    split
    · rename_i v hv
      exact getW_congr v p fun w hw => h w (by simp only [windowsOf]; exact windowsOf_lookup hv hw)
    · rfl
  | .list vs, .index i :: p, h => by
    simp only [getW]
    split
    · rename_i v hv
      exact getW_congr v p fun w hw => h w (by simp only [windowsOf]; exact windowsOf_elemAt? hv hw)
    · rfl
  | .record _ _, .index _ :: _, _ | .list _, .field _ :: _, _ | .int _, _ :: _, _
  | .float _, _ :: _, _ | .bool _, _ :: _, _ | .str _, _ :: _, _ | .unit, _ :: _, _
  | .variant .., _ :: _, _ | .closure .., _ :: _, _ | .function .., _ :: _, _
  | .handle .., _ :: _, _ => rfl

/-- What a variable of the body holds is as the simulation knows it across a change that keeps
its location and the locations of the windows there, and variables that track those windows. -/
theorem TopHolds.transport {env env' : List (Name × Ref)} {In : List (Name × Value)} {L : Nat}
    {xb : Name × ViewBinding} {xr : Name × Ref} {older older' : List (Name × Ref)}
    (h : TopHolds sw env In L xb xr older) (hk : Kept sw sw' xr.2.loc)
    (hw : ∀ y, cell sw xr.2.loc = .ok y → ∀ w ∈ windowsOf y, regionW sw' w = regionW sw w)
    (ht : ∀ S w y, cell sw xr.2.loc = .ok y → w ∈ windowsOf y → Tracked env In S w →
      Tracked env' In S w)
    (ho : ∀ yr ∈ older', yr ∈ older) : TopHolds sw' env' In L xb xr older' := by
  obtain ⟨y, hy, hrest⟩ := h
  refine ⟨y, by rw [cell_kept hk, hy], ?_⟩
  split
  · rename_i hpar
    simp only [hpar, ↓reduceIte] at hrest
    intro x hx
    rw [getW_congr y _ (hw y hy)] at hx
    exact hrest x hx
  · rename_i hpar
    simp only [hpar, Bool.false_eq_true, ↓reduceIte] at hrest
    obtain ⟨hpath, hL, hold, hty⟩ := hrest
    refine ⟨hpath, hL, fun yr hyr => hold yr (ho yr hyr), ?_⟩
    split
    · rename_i hs
      simp only [hs, ↓reduceIte] at hty
      exact fun w hwin => ht _ w y hy hwin (hty w hwin)
    · rename_i hs
      simpa [hs] using hty

theorem BaseHolds.transport {xr : Name × Ref} (h : BaseHolds sw xr) (hk : Kept sw sw' xr.2.loc) :
    BaseHolds sw' xr := by
  obtain ⟨y, hy, hpath, hfree⟩ := h
  exact ⟨y, by rw [cell_kept hk, hy], hpath, hfree⟩

/-- `Fits.mono`, knowing each variable is one of them. -/
theorem Fits.mono_mem {top top' : Name × ViewBinding → Name × Ref → List (Name × Ref) → Prop}
    {base base' : Name × Ref → Prop} :
    ∀ {Γ : ViewScope} {env : List (Name × Ref)}, Fits top base Γ env →
      (∀ xb xr older, xr :: older <:+ env → top xb xr older → top' xb xr older) →
      (∀ xr ∈ env, base xr → base' xr) → Fits top' base' Γ env
  | _, _, .base hΓ henv, _, hb => .base hΓ fun xr hxr => hb xr hxr (henv xr hxr)
  | _, _, .cons (xr := xr) (env := env) hx htop hrest, ht, hb =>
    .cons hx (ht _ _ _ (List.suffix_refl _) htop)
      (Fits.mono_mem hrest (fun xb yr older hs h => ht xb yr older (hs.trans (List.suffix_cons _ _)) h)
        fun yr hyr h => hb yr (List.mem_cons_of_mem _ hyr) h)

end Windows

end Stilt
