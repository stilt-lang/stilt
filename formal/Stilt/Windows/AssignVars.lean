import Stilt.Windows.AssignWrite

/-!
# The variables after a write

What the simulation knows of each variable holds after a write that the checks of views accept.
The written variable's location holds what it held with the value written in: a variable of the
body's own holds windows its sources track, the value's among them; a parameter, at its place,
windows its value brought in, as before, the value holding none. Another variable on the same
location is an `inout` parameter on a disjoint part, which the write leaves; a variable on
another location keeps its cell, and the windows there read alike.
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls} {c : Ctx} {pend : List (Window × Value)}

theorem VRel.partsFree {si : List Value} {sw : List (Option Value)} {y u : Value}
    (h : VRel si sw y u) : PartsFree sw y := fun win hw d hd => by
  obtain ⟨heq, hfree⟩ := (h.2 win hw).readAlike
  exact hfree d (heq ▸ hd)

theorem cell_set_self {st : List (Option Value)} {ℓ : Nat} (h : ℓ < st.length) (y : Value) :
    cell (st.set ℓ (some y)) ℓ = .ok y := by
  simp [cell, List.getElem?_set_self h]

theorem eq_of_cell {st : List (Option Value)} {ℓ : Nat} {y y₀ : Value}
    (h : st[ℓ]? = some (some y)) (h₀ : cell st ℓ = .ok y₀) : y₀ = y := by
  have := cell_eq_ok h₀
  rw [h] at this
  simpa using this.symm

namespace Write

variable {si : IState} {sw : WState} {r : Ref} {p : Path} {w v y u y' u' : Value}

/-- What the written location holds at a place below the written variable's: the part there
before the write, with the value written in. -/
theorem getW_written (h : Write si sw pend r p w v y u y' u') (hag : Agree D si sw) {x' : Value}
    (hx : getW h.storeW y' r.path = .ok x') :
    ∃ z, getW sw.1.store y r.path = .ok z ∧ ∀ win ∈ windowsOf x', win ∈ windowsOf z ∨
      win ∈ windowsOf w := by
  rw [getW_congr y' _ fun win hw => (h.new_region hag hw).2.1,
    getW_setW_prefix h.rel.partsFree h.setW] at hx
  cases hz : getW sw.1.store y r.path with
  | error e => rw [hz] at hx; cases hx
  | ok z =>
    rw [hz] at hx
    change Windows.setW sw.1.store z p w = .ok x' at hx
    rcases getW_rel h.rel.1 h.rel.readAlike r.path with ⟨f, h₁, -⟩ | ⟨z₁, z', h₁, -, h₃, h₄⟩
    · rw [hz] at h₁; cases h₁
    · rw [hz] at h₁
      cases h₁
      rcases setW_rel h₃ (fun win hw => h.rel.readAlike win (h₄ win hw)) h.val.1 p with
        ⟨f, h₅, -⟩ | ⟨x'', u'', h₅, -, -, h₆⟩
      · rw [hx] at h₅; cases h₅
      · rw [hx] at h₅
        cases h₅
        exact ⟨z, rfl, h₆⟩

/-- The written variable, after the write. -/
theorem top_written (h : Write si sw pend r p w v y u y' u') (hag : Agree D si sw) {x : Name}
    {xb : Name × ViewBinding} {older : List (Name × Ref)}
    (hwv : ∀ win ∈ windowsOf w, xb.2.param = false ∧ xb.2.type.isSome = true ∧
      Tracked sw.1.env c.In xb.2.sources win)
    (htop : TopHolds sw.1.store sw.1.env c.In c.L xb (x, r) older) :
    TopHolds h.storeW sw.1.env c.In c.L xb (x, r) older := by
  obtain ⟨y₀, hy₀, hrest⟩ := htop
  have hy := eq_of_cell h.cellW hy₀
  subst hy
  refine ⟨y', cell_set_self h.lt y', ?_⟩
  split
  · rename_i hpar
    simp only [hpar, ↓reduceIte] at hrest
    intro x' hx win hwin
    obtain ⟨z, hz, hsub⟩ := h.getW_written hag hx
    rcases hsub win hwin with hw | hw
    · exact hrest z hz win hw
    · simp [(hwv win hw).1] at hpar
  · rename_i hpar
    simp only [hpar, Bool.false_eq_true, ↓reduceIte] at hrest
    obtain ⟨hpath, hL, hold, hty⟩ := hrest
    refine ⟨hpath, hL, hold, ?_⟩
    split
    · rename_i hs
      simp only [hs, ↓reduceIte] at hty
      intro win hwin
      rcases h.sub win hwin with hw | hw
      · exact hty win hw
      · exact (hwv win hw).2.2
    · rename_i hs
      simp only [hs, Bool.false_eq_true, ↓reduceIte] at hty
      refine List.eq_nil_iff_forall_not_mem.2 fun win hwin => ?_
      rcases h.sub win hwin with hw | hw
      · rw [hty] at hw; cases hw
      · simp [(hwv win hw).2.1] at hs

/-- A parameter on a part of the written location disjoint from the write's, after it. -/
theorem top_shared (h : Write si sw pend r p w v y u y' u') (hag : Agree D si sw)
    {xb : Name × ViewBinding} {xr : Name × Ref} {older : List (Name × Ref)} (hloc : xr.2.loc = r.loc)
    (hd : xr.2.path.Disjoint r.path)
    (htop : TopHolds sw.1.store sw.1.env c.In c.L xb xr older) :
    TopHolds h.storeW sw.1.env c.In c.L xb xr older := by
  obtain ⟨y₀, hy₀, hrest⟩ := htop
  rw [hloc] at hy₀
  have hy := eq_of_cell h.cellW hy₀
  subst hy
  refine ⟨y', by rw [hloc]; exact cell_set_self h.lt y', ?_⟩
  split
  · rename_i hpar
    simp only [hpar, ↓reduceIte] at hrest
    intro x' hx
    rw [getW_congr y' _ fun win hw => (h.new_region hag hw).2.1,
      getW_setW_disjoint h.rel.partsFree (by simpa using hd.symm.append p []) h.setW] at hx
    exact hrest x' hx
  · rename_i hpar
    simp only [hpar, Bool.false_eq_true, ↓reduceIte] at hrest
    rw [hrest.1] at hd
    simp [Path.Disjoint] at hd

/-- A variable on another location, after the write. -/
theorem top_other (h : Write si sw pend r p w v y u y' u') (hag : Agree D si sw)
    {xb : Name × ViewBinding} {xr : Name × Ref} {older : List (Name × Ref)} (hloc : xr.2.loc ≠ r.loc)
    (htop : TopHolds sw.1.store sw.1.env c.In c.L xb xr older) :
    TopHolds h.storeW sw.1.env c.In c.L xb xr older :=
  htop.transport (by simp [Kept, List.getElem?_set_ne (Ne.symm hloc)])
    (fun y₀ hy₀ win hw => (h.live_region hag (.inl ⟨_, y₀, cell_eq_ok hy₀, hw⟩)).2.1)
    (fun _ _ _ _ _ ht => ht) fun _ h => h

end Write

end Windows

end Stilt
