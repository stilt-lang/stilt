import Stilt.Windows.Kept

/-!
# Every live window is watched

Each window the store of windows holds, and each waiting window, either lies where no variable
reaches, or is guarded by the reads around (views.reads-that-last). So a write to a place whose
shape the reads don't overlap misses the region of every live window (views.change-while-viewed,
E0423), and the windows read what they read before.
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls}

/-- Two fits of the same variables, the second one's own holding of every parameter: both hold
of each of the newest variables. -/
theorem Fits.zip {t₁ t₂ : Name × ViewBinding → Name × Ref → List (Name × Ref) → Prop}
    {b₁ : Name × Ref → Prop} (ht : ∀ xb xr older, xb.2.param = true → t₂ xb xr older) :
    ∀ {Γ : ViewScope} {env : List (Name × Ref)}, Fits t₁ b₁ Γ env → Fits t₂ (fun _ => True) Γ env →
      Fits (fun xb xr older => t₁ xb xr older ∧ t₂ xb xr older) b₁ Γ env
  | _, _, .base hΓ henv, _ => .base hΓ henv
  | _, _, .cons hx h₁ hrest₁, .cons _ h₂ hrest₂ => .cons hx ⟨h₁, h₂⟩ (Fits.zip ht hrest₁ hrest₂)
  | _, _, .cons hx h₁ hrest₁, .base hΓ _ =>
    .cons hx ⟨h₁, ht _ _ _ (hΓ _ List.mem_cons_self)⟩
      (Fits.zip ht hrest₁ (.base (fun xb h => hΓ xb (List.mem_cons_of_mem _ h)) fun _ _ => trivial))

/-- A variable fits as one of the newest, or as one of the rest. -/
theorem Fits.mem {top : Name × ViewBinding → Name × Ref → List (Name × Ref) → Prop}
    {base : Name × Ref → Prop} :
    ∀ {Γ : ViewScope} {env : List (Name × Ref)}, Fits top base Γ env → ∀ xr ∈ env,
      (∃ xb older, top xb xr older) ∨ base xr
  | _, _, .base _ henv, xr, h => .inr (henv xr h)
  | _, _, .cons _ htop hrest, xr, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact .inl ⟨_, _, htop⟩
    · exact Fits.mem hrest xr h

/-- What a window is: one no variable reaches, or one the reads guard. -/
def Watched (R : List Shape) (env : List (Name × Ref)) (w : Window) : Prop :=
  Unreached env w ∨ InPlace.Guarded R env w.ref.toPath

/-- Each window the store of windows holds is watched. -/
theorem Pre.watched {c : Ctx} {pend : List (Window × Value)} {si : IState} {sw : WState}
    (hp : Pre D c pend si sw) (hg : Guards D c pend sw.1.env) :
    ∀ (ℓ : Nat) y, sw.1.store[ℓ]? = some (some y) → ∀ w ∈ windowsOf y, Watched c.R sw.1.env w := by
  intro ℓ y hy w hw
  by_cases hl : ℓ < c.L
  · exact .inl (hg.old ℓ hl w ((hp.outer ℓ y hl hy).1 w hw)).2
  · obtain ⟨⟨xr, hxr, he⟩, hlt⟩ := hp.owned ℓ y (by omega) hy
    have hz := Fits.zip (fun xb xr older hpar hpar' => by simp [hpar] at hpar') hp.fits hg.fenced
    have hcell : cell sw.1.store xr.2.loc = .ok y := by
      rw [he]; simp [cell, hy]
    have hpath : xr.2.path = [] := by rw [he]
    have hgy : getW sw.1.store y [] = .ok y := by cases y <;> rfl
    rcases Fits.mem hz xr hxr with ⟨xb, older, ⟨y', hy', ht⟩, hf⟩ | ⟨y', hy', -, hfree⟩
    · rw [hcell] at hy'
      cases hy'
      split at ht
      · obtain ⟨⟨v, hv, w', hw', h1, h2⟩, -⟩ := ht y (by rw [hpath]; exact hgy) w hw
        refine .inl fun zr hzr => ?_
        have := (hg.brought (xr.1, v) hv w' hw').2 zr hzr
        simpa [Window.ref, h1, h2] using this
      · rename_i hpar
        obtain ⟨-, -, -, hty⟩ := ht
        split at hty
        · rename_i hs
          refine .inr (hf (by simpa using hpar) hs w (by rw [he]; exact hlt w hw) (hty w hw))
        · rw [hty] at hw; cases hw
    · rw [hcell] at hy'
      cases hy'
      rw [hfree] at hw; cases hw

/-- A write to a place whose shape the reads don't overlap misses a watched window's region. -/
theorem Watched.avoids {R : List Shape} {env : List (Name × Ref)} {w : Window}
    (h : Watched R env w) {x : Name} {r : Ref} (hl : env.lookup x = some r) {p : Path}
    {ps : List Projection} (hp : p.Resolves ps) (hu : unread R (Place.mk x ps).shape = true) :
    (r.toPath ++ p).Disjoint w.ref.toPath := by
  rcases h with h | h
  · exact disjoint_append_left (h (x, r) (mem_of_lookup hl)) p
  · refine Classical.byContradiction fun hd => ?_
    obtain ⟨t, ht, ho⟩ := InPlace.unread_eq_false.1 (h x r hl p hd)
    rw [Path.fieldNames_of_resolves hp] at ho
    rw [unread_iff] at hu
    exact absurd (hu t ht) (by simp [Place.shape, ho])

end Windows

end Stilt
