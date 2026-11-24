import Stilt.Windows.View.Place

/-!
# The sources of a view's source

The sources the checks give a view's source operand (`headSources`) track every window the
model of windows gives the view before its offsets narrow it: the window the place holds,
tracked as the variable's sources or brought in by a parameter, a window made on the place,
which the place's own shape covers, or the value the operand read (views.making-view). That
holds in a scope where a binding of the body's own whose written type may hold no view has no
sources, as every scope the checks build (`ScopeKeeps`).
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls}

theorem ScopeKeeps.binders {Γ : ViewScope} (h : ScopeKeeps D Γ) (scrutinee : List Shape) :
    ∀ xs : List Name, ScopeKeeps D (Γ.binders xs scrutinee) := by
  intro xs
  induction xs generalizing Γ with
  | nil => exact h
  | cons x xs ih =>
    refine ih (Γ := (x, ⟨none, scrutinee, false⟩) :: Γ)
      ⟨fun xb hxb hp σ hσ hv => ?_, fun xb hxb hp σ hσ hv => ?_⟩
    · rcases List.mem_cons.1 hxb with rfl | hxb
      · cases hσ
      · exact h.own xb hxb hp σ hσ hv
    · rcases List.mem_cons.1 hxb with rfl | hxb
      · cases hσ
      · exact h.given xb hxb hp σ hσ hv

theorem ScopeKeeps.holding {Γ : ViewScope} (h : ScopeKeeps D Γ) :
    ∀ names : List (Name × Ty), ScopeKeeps D (Γ.holding D names) := by
  intro names
  induction names generalizing Γ with
  | nil => exact h
  | cons p names ih => exact ih (h.bind p.1 p.2 [])

theorem ScopeKeeps.params {Γ : ViewScope} (h : ScopeKeeps D Γ) :
    ∀ ps : List Param, ScopeKeeps D (Γ.params D ps) := by
  intro ps
  induction ps generalizing Γ with
  | nil => exact h
  | cons p ps ih =>
    refine ih ⟨fun xb hxb hp σ hσ hv => ?_, fun xb hxb hp σ hσ hv => ?_⟩
    · rcases List.mem_cons.1 hxb with rfl | hxb
      · cases hp
      · exact h.own xb hxb hp σ hσ hv
    · rcases List.mem_cons.1 hxb with rfl | hxb
      · simp only [Option.some.injEq] at hσ
        subst hσ
        simp [hv]
      · exact h.given xb hxb hp σ hσ hv

/-- Entering a closure's body: the bindings around it seen as parameters, then its own. -/
theorem ScopeKeeps.enter {Γ : ViewScope} (h : ScopeKeeps D Γ) (ps : List Param) :
    ScopeKeeps D (Γ.enter D ps) := by
  refine ScopeKeeps.params ⟨fun xb hxb hp _ _ _ => ?_, fun xb hxb _ σ hσ hv => ?_⟩ ps
  · obtain ⟨_, -, rfl⟩ := List.mem_map.1 hxb
    cases hp
  · obtain ⟨yb, hyb, rfl⟩ := List.mem_map.1 hxb
    cases hpar : yb.2.param
    · exact h.own yb hyb hpar σ hσ hv
    · exact h.given yb hyb hpar σ hσ hv

/-- The scope a function's body starts in. -/
theorem ScopeKeeps.fn (d : FnDecl) : ScopeKeeps D (d.viewScope D) :=
  (ScopeKeeps.nil D).params d.params

/-! ## The sources of a place -/

/-- A type that may hold a view has no part at a projection. -/
theorem along_holdsView {τ : Ty} (h : τ.holdsView D = true) (q : Projection)
    (qs : List Projection) :
    Ty.along D τ (q :: qs) = none := by
  cases τ <;> cases q <;> simp_all [Ty.holdsView, Ty.isView, Ty.along]

/-- The sources of a binding with no written type, or one that may hold a view, are among
those of each of its places. -/
theorem sources_sub_place {Γ : ViewScope} {x : Name} {b : ViewBinding}
    (hb : Γ.lookup x = some b) (ht : b.type = none ∨ ∃ τ, b.type = some τ ∧ τ.holdsView D = true)
    (ps : List Projection) : ∀ s ∈ b.sources, s ∈ Γ.placeSources D ⟨x, ps⟩ := by
  intro s hs
  obtain ⟨ty, srcs, prm⟩ := b
  simp only at ht hs
  rcases ht with rfl | ⟨τ, rfl, hτ⟩
  · simp only [ViewScope.placeSources, hb]
    exact List.mem_cons_of_mem _ hs
  · simp only [ViewScope.placeSources, hb]
    have hal : ∀ σ, τ.along D ps = some σ → σ = τ := by
      intro σ h
      cases ps with
      | nil => simp only [Ty.along, Option.some.injEq] at h; exact h.symm
      | cons q qs => rw [along_holdsView hτ] at h; cases h
    split
    · exact List.mem_cons_of_mem _ hs
    · exact List.mem_cons_of_mem _ hs
    · rename_i σ _ hσ
      rw [hal σ hσ]
      simp only [hτ, ↓reduceIte]
      exact hs

/-- What a variable's location holds, read along its path, holds only windows that the
sources of each of its places track, with its shape. -/
theorem lookup_tracked {c : Ctx} {pend : List (Window × Value)} {si : IState} {sw : WState}
    (hp : Pre D c pend si sw) (hΓ : ScopeKeeps D c.Γ) {x : Name} {r : Ref}
    (hl : sw.1.env.lookup x = some r) (ps : List Projection) :
    ∃ y, cell sw.1.store r.loc = .ok y ∧ ∀ z, getW sw.1.store y r.path = .ok z →
      ∀ win ∈ windowsOf z,
        Tracked sw.1.env c.In ((⟨x, ps⟩ : Place).shape :: c.Γ.placeSources D ⟨x, ps⟩) win := by
  have hget : ∀ y z, r.path = [] → getW sw.1.store y r.path = .ok z → z = y := by
    intro y z hp hz
    rw [hp] at hz
    have : getW sw.1.store y [] = .ok y := by cases y <;> rfl
    rw [this] at hz; cases hz; rfl
  rcases Fits.lookup hp.fits hl with ⟨b, older, hb, y, hy, ht⟩ | ⟨y, hy, hpath, hfree⟩
  · refine ⟨y, hy, fun z hz win hw => ?_⟩
    split at ht
    · exact ⟨_, List.mem_cons_self, .inr (ht z hz win hw).1⟩
    · rename_i hpar
      obtain ⟨hpath, -, -, ht⟩ := ht
      obtain rfl := hget y z hpath hz
      split at ht
      · rename_i hty
        obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.1 hty
        cases hv : τ.holdsView D
        · rw [hΓ.own (x, b) (mem_of_lookup hb) (by simpa using hpar) τ hτ hv] at ht
          obtain ⟨s, hs, -⟩ := ht win hw
          cases hs
        · exact (ht win hw).sub fun s hs =>
            List.mem_cons_of_mem _ (sources_sub_place hb (.inr ⟨τ, hτ, hv⟩) ps s hs)
      · rw [ht] at hw; cases hw
  · refine ⟨y, hy, fun z hz win hw => ?_⟩
    rw [hget y z hpath hz, hfree] at hw
    cases hw

/-! ## The view before its offsets -/

/-- The value a view's operand read, kept as it is: tracked by the sources of its place when
it is the variable's value, and holding no window when it takes a field. -/
theorem fallback_rel {c : Ctx} {pend : List (Window × Value)} {si : IState} {sw : WState}
    (hp : Pre D c pend si sw) (hΓ : ScopeKeeps D c.Γ) {x : Name} {ps : List Projection}
    {S : List Shape} {v v' : Value} (hv : ValG D c S v v' si sw)
    (hg0 : ps = [] → readWindows sw.1 x [] = .ok v') (hfree : ps ≠ [] → Free v') :
    ValG D c ((⟨x, ps⟩ : Place).shape :: c.Γ.placeSources D ⟨x, ps⟩) v v' si sw := by
  refine ⟨hv.1, fun win hw => ?_, hv.2.2⟩
  by_cases h0 : ps = []
  · have hr := hg0 h0
    cases hl : sw.1.env.lookup x with
    | none => simp [readWindows, hl] at hr
    | some r =>
      obtain ⟨y, hy, htr⟩ := lookup_tracked hp hΓ hl ps
      have hrw : readWindows sw.1 x [] = getW sw.1.store y r.path := by
        simp only [readWindows, hl, deref, hy, List.append_nil]
        rfl
      exact htr v' (hrw ▸ hr) win hw
  · rw [hfree h0] at hw; cases hw

/-- The window a place holds, as the view of the place. -/
theorem held_rel {c : Ctx} {si : IState} {sw : WState}
    {S : List Shape} {r : Ref} {path : Path} {y u v : Value} {l : Nat} {q : Path}
    {rr : List (Int × Int)} (hyu : VRel si.1.store sw.1.store y u)
    (hP : u.get (r.path ++ path) = .ok v) (hvv : v.Viewed D)
    (htr : ∀ z, getW sw.1.store y r.path = .ok z → ∀ win ∈ windowsOf z, Tracked sw.1.env c.In S win)
    (hraw : y.get (r.path ++ path) = .ok (.window l q rr)) :
    ValG D c S v (.window l q rr) si sw := by
  rcases getW_rel hyu.1 hyu.readAlike (r.path ++ path) with ⟨f, h₁, -⟩ | ⟨z, z', h₁, h₂, h₃, h₄⟩
  · rw [getW_of_get _ _ hraw] at h₁; cases h₁
  rw [getW_of_get _ _ hraw] at h₁
  cases h₁
  obtain rfl : z' = v := by rw [hP] at h₂; exact (Except.ok.inj h₂).symm
  refine ⟨⟨h₃, fun win hw => hyu.2 win (h₄ win hw)⟩, fun win hw => ?_, hvv⟩
  rw [Value.get_append] at hraw
  cases hz₀ : y.get r.path with
  | error _ => rw [hz₀] at hraw; cases hraw
  | ok z₀ =>
    rw [hz₀] at hraw
    exact htr z₀ (getW_of_get _ _ hz₀) win (windowsOf_get z₀ path hraw win hw)

/-- A window made on a place that holds no window and can be viewed. -/
theorem made_rel {c : Ctx} {si : IState} {sw : WState}
    {x : Name} {ps : List Projection} {path : Path} (hfp : fieldPath ps = some path) {r : Ref}
    (hl : sw.1.env.lookup x = some r) {y u v z : Value} {S : List Shape}
    (hy : cell sw.1.store r.loc = .ok y) (hu : si.1.store[r.loc]? = some u)
    (hyu : VRel si.1.store sw.1.store y u) (hP : u.get (r.path ++ path) = .ok v)
    (hvv : v.Viewed D) (hraw : y.get (r.path ++ path) = .ok z) (hzf : Free z)
    (hzv : viewable z = true) :
    ValG D c ((⟨x, ps⟩ : Place).shape :: S) v (.window r.loc (r.path ++ path) []) si sw := by
  rcases getW_rel hyu.1 hyu.readAlike (r.path ++ path) with ⟨f, h₁, -⟩ | ⟨z₁, z', h₁, h₂, h₃, -⟩
  · rw [getW_of_get _ _ hraw] at h₁; cases h₁
  rw [getW_of_get _ _ hraw] at h₁
  cases h₁
  rw [resolveIn_free si.1.store hzf] at h₃
  cases h₃
  obtain rfl : z = v := by rw [hP] at h₂; exact (Except.ok.inj h₂).symm
  have hpart : partIn si.1.store r.loc (r.path ++ path) [] = .ok z := by
    simp only [partIn, hu]
    show (u.get (r.path ++ path) >>= fun v => List.foldlM _ v []) = _
    rw [hP]
    rfl
  refine ⟨⟨hpart, fun win hw => ?_⟩, fun win hw => ?_, hvv⟩
  · simp only [windowsOf, List.mem_singleton] at hw
    subst hw
    refine ⟨z, ?_, ?_, hzf, hzv⟩
    · show cell sw.1.store r.loc >>= (·.get (r.path ++ path)) = _
      rw [hy]; exact hraw
    · show cellIn si.1.store r.loc >>= (·.get (r.path ++ path)) = _
      simp only [cellIn, hu]; exact hP
  · simp only [windowsOf, List.mem_singleton] at hw
    subst hw
    refine ⟨_, List.mem_cons_self, .inl ⟨r, mem_of_lookup hl, path, ?_, ?_⟩⟩
    · simp [Window.ref, InPlace.Ref.toPath]
    · rw [fieldNames_of_fieldPath hfp]
      exact List.prefix_refl _

/-- The view of a place that takes no index, before its offsets, related to the part the
in-place model reads there and tracked by the sources of the place and its shape. -/
theorem viewOf_place_rel {c : Ctx} {pend : List (Window × Value)} {si : IState} {sw : WState}
    (hp : Pre D c pend si sw) (hΓ : ScopeKeeps D c.Γ) {src : Expr} {x : Name}
    {ps : List Projection} {path : Path} (hplace : src.place? = some ⟨x, ps⟩)
    (hfp : fieldPath ps = some path) {S : List Shape} {v v' : Value} (hv : ValG D c S v v' si sw)
    (hread : (InPlace.read si.1 x [] >>= (·.get path)) = .ok v)
    (hg0 : ps = [] → readWindows sw.1 x [] = .ok v') (hfree : ps ≠ [] → Free v') :
    ValG D c (headSources D c.Γ [src]) v (viewOf sw.1 src v') si sw := by
  have hhead : headSources D c.Γ [src] =
      (⟨x, ps⟩ : Place).shape :: c.Γ.placeSources D ⟨x, ps⟩ := by
    simp only [headSources, hplace]
  have hvo : viewOf sw.1 src v' = windowAt sw.1 x path v' := by simp only [viewOf, hplace, hfp]
  rw [hhead, hvo]
  have hfb := fallback_rel hp hΓ hv hg0 hfree
  cases hl : sw.1.env.lookup x with
  | none => simp only [windowAt, hl]; exact hfb
  | some r =>
    obtain ⟨y, hy, htr⟩ := lookup_tracked hp hΓ hl ps
    obtain ⟨u, hu, hyu⟩ := hp.agree.live r.loc y (cell_eq_ok hy)
    have hri : InPlace.read si.1 x [] = u.get r.path := by
      simp only [InPlace.read, ← hp.agree.env, hl, InPlace.deref, hu, List.append_nil]
    rw [hri] at hread
    have hP : u.get (r.path ++ path) = .ok v := by rw [Value.get_append]; exact hread
    unfold windowAt
    simp only [hl, hy]
    split
    · rename_i l q rr hraw
      exact held_rel hyu hP hv.2.2 htr hraw
    · rename_i z _ hraw
      split
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        exact made_rel hfp hl hy hu hyu hP hv.2.2 hraw (mapWindows_stuck_isOk.1 hc.1) hc.2
      · exact hfb
    · exact hfb

/-- An operand that names no place without an index is viewed as the value it reads. -/
theorem viewOf_other {s : State} {e : Expr} {v : Value}
    (h : ∀ x ps path, e.place? = some ⟨x, ps⟩ → fieldPath ps = some path → False) :
    viewOf s e v = v := by
  unfold viewOf
  cases hpl : e.place? with
  | none => rfl
  | some p =>
    obtain ⟨x, ps⟩ := p
    cases hf : fieldPath ps with
    | none => simp [hf]
    | some path => exact (h x ps path hpl hf).elim

/-- Its sources are its own, or none. -/
theorem sources_sub_head_other {Γ : ViewScope} {e : Expr}
    (h : ∀ x ps path, e.place? = some ⟨x, ps⟩ → fieldPath ps = some path → False) :
    ∀ s ∈ e.sources D Γ, s ∈ headSources D Γ [e] := by
  intro s hs
  cases hpl : e.place? with
  | none => simpa [headSources, hpl] using hs
  | some p =>
    obtain ⟨x, ps⟩ := p
    rcases place_cases hpl with ⟨rfl, rfl | rfl⟩ | ⟨e', f, ps', rfl, -, -⟩ | ⟨e', i, ps', rfl, -, -⟩
    · exact (h x [] [] hpl rfl).elim
    · exact (h x [] [] hpl rfl).elim
    · cases hs
    · cases hs

end Windows

end Stilt
