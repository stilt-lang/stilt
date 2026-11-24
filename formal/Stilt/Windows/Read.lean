import Stilt.Windows.Fields

/-!
# Reading a variable

A variable names the same location in both models, which holds related values: read along the
same path, they give related values, or fail alike (`getW_rel`). The windows of what a variable
holds are tracked by its sources (`TopHolds`), or it holds none (`BaseHolds`).
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls}

theorem cell_eq_ok {st : List (Option Value)} {ℓ : Nat} {y : Value} (h : cell st ℓ = .ok y) :
    st[ℓ]? = some (some y) := by
  unfold cell at h
  split at h
  · cases h; assumption
  · cases h

/-- A variable's binding in the variables and in the scope: one of the newest, as `top` says, or
one of the rest, as `base` says. -/
theorem Fits.lookup {top : Name × ViewBinding → Name × Ref → List (Name × Ref) → Prop}
    {base : Name × Ref → Prop} {x : Name} {r : Ref} :
    ∀ {Γ : ViewScope} {env : List (Name × Ref)}, Fits top base Γ env → env.lookup x = some r →
      (∃ b older, Γ.lookup x = some b ∧ top (x, b) (x, r) older) ∨ base (x, r)
  | _, _, .base _ henv, hl => .inr (henv _ (mem_of_lookup hl))
  | _, _, .cons (xb := ⟨y, b⟩) (xr := ⟨y', r'⟩) hx htop hrest, hl => by
    simp only at hx
    subst hx
    by_cases hy : x = y
    · subst hy
      simp only [List.lookup_cons_self, Option.some.injEq] at hl
      subst hl
      exact .inl ⟨b, _, List.lookup_cons_self, htop⟩
    · rw [lookup_cons_ne hy] at hl
      rcases Fits.lookup hrest hl with ⟨b', older, hb, ht⟩ | hb
      · exact .inl ⟨b', older, by rw [lookup_cons_ne hy]; exact hb, ht⟩
      · exact .inr hb

/-- What a variable holds is read alike in both stores, its windows tracked by its sources. -/
theorem Pre.var {c : Ctx} {pend : List (Window × Value)} {si : IState} {sw : WState}
    (hp : Pre D c pend si sw) (x : Name) :
    (∃ f, InPlace.read si.1 x [] = .error f ∧ readWindows sw.1 x [] = .error f) ∨
      ∃ v w, InPlace.read si.1 x [] = .ok v ∧ readWindows sw.1 x [] = .ok w ∧
        ValG D c (((c.Γ.lookup x).map (·.sources)).getD []) v w si sw := by
  have hag := hp.agree
  cases hl : sw.1.env.lookup x with
  | none =>
    refine .inl ⟨.stuck, ?_, ?_⟩
    · simp only [InPlace.read, ← hag.env, hl]
    · simp only [readWindows, hl]
  | some r =>
    have hlive : ∃ y, cell sw.1.store r.loc = .ok y ∧ ∀ z, getW sw.1.store y r.path = .ok z →
        ((∃ b, c.Γ.lookup x = some b ∧ ∀ win ∈ windowsOf z, Tracked sw.1.env c.In b.sources win) ∨
          Free z) := by
      have hget : ∀ y z, r.path = [] → getW sw.1.store y r.path = .ok z → z = y := by
        intro y z hp hz
        rw [hp] at hz
        have : getW sw.1.store y [] = .ok y := by cases y <;> rfl
        rw [this] at hz; cases hz; rfl
      rcases Fits.lookup hp.fits hl with ⟨b, older, hb, y, hy, ht⟩ | ⟨y, hy, hpath, hfree⟩
      · refine ⟨y, hy, fun z hz => ?_⟩
        split at ht
        · exact .inl ⟨b, hb, fun win hw => ⟨⟨x, []⟩, (ht z hz win hw).2, .inr (ht z hz win hw).1⟩⟩
        · obtain ⟨hpath, -, -, ht⟩ := ht
          have := hget y z hpath hz
          subst this
          split at ht
          · exact .inl ⟨b, hb, ht⟩
          · exact .inr ht
      · exact ⟨y, hy, fun z hz => .inr (by rw [hget y z hpath hz]; exact hfree)⟩
    obtain ⟨y, hy, htr⟩ := hlive
    obtain ⟨u, hu, hyu⟩ := hag.live r.loc y (cell_eq_ok hy)
    have hri : InPlace.read si.1 x [] = u.get r.path := by
      simp only [InPlace.read, ← hag.env, hl, InPlace.deref, hu, List.append_nil]
    have hrw : readWindows sw.1 x [] = getW sw.1.store y r.path := by
      simp only [readWindows, hl, deref, hy, List.append_nil]
      rfl
    rw [hri, hrw]
    rcases getW_rel hyu.1 hyu.readAlike r.path with ⟨f, h₁, h₂⟩ | ⟨z', u', h₁, h₂, h₃, h₄⟩
    · exact .inl ⟨f, h₂, h₁⟩
    · refine .inr ⟨u', z', h₂, h₁, ⟨h₃, fun win hw => hyu.2 win (h₄ win hw)⟩, fun win hw => ?_,
        (hag.viewed u (List.mem_of_getElem? hu)).get h₂⟩
      rcases htr z' h₁ with ⟨b, hb, ht⟩ | hfree
      · rw [hb]
        exact ht win hw
      · rw [hfree] at hw
        cases hw

end Windows

end Stilt
