import Stilt.Windows.AssignFits

/-!
# A write that the checks of views accept

An assignment `x.ps = e`, run in both models, writes the value of `e` into `x`'s location at the
same path. What the checks give: the shape written is read by none of the reads around it
(E0423), so every live window and every waiting one misses the write (`Pre.watched`,
`Watched.avoids`); and a value that holds views goes only to a variable of the body's own with a
written type, whose sources hold the value's, each of which names an older variable (E0422), so
the value's windows lie before the written location (`value_windows`). Then the store after the
write agrees as before (`Write.agree`).
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls} {c : Ctx} {pend : List (Window × Value)}

/-- What the checks know of the sources `V` of a value assigned to `x`: each is a source of
`x`'s binding, which is no parameter and has a written type, and names another variable, which
outlives `x`. -/
def AssignSources (c : Ctx) (x : Name) (V : List Shape) : Prop :=
  ∀ s ∈ V, ∃ b, c.Γ.lookup x = some b ∧ s ∈ b.sources ∧ b.param = false ∧
    b.type.isSome = true ∧ s.root ≠ x ∧ c.Γ.outlives s.root x = true

theorem assignSources_of_checks {c : Ctx} {x : Name} {V : List Shape}
    (hr : V.all (fun s => (c.Γ.lookup x).any (·.sources.contains s)) = true)
    (hc : V.all (fun s => s.root != x && c.Γ.outlives s.root x &&
      (c.Γ.lookup x).all fun b => !b.param && b.type.isSome) = true) :
    AssignSources c x V := by
  intro s hs
  have h₁ := List.all_eq_true.1 hr s hs
  have h₂ := List.all_eq_true.1 hc s hs
  cases hb : c.Γ.lookup x with
  | none => simp [hb] at h₁
  | some b =>
    simp only [hb, Option.any_some, List.contains_iff_mem] at h₁
    simp only [hb, Option.all_some, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq]
      at h₂
    exact ⟨b, rfl, h₁, h₂.2.1, h₂.2.2, h₂.1.1, h₂.1.2⟩

/-- A window of the value assigned to `x` lies before `x`'s location, which is the body's own,
and the sources of `x`'s binding, no parameter's, with a written type, track it. -/
theorem value_windows {si : IState} {sw : WState} (hp : Pre D c pend si sw)
    (hg : Guards D c pend sw.1.env) {x : Name} {r : Ref} (hl : sw.1.env.lookup x = some r)
    {V : List Shape} (hV : AssignSources c x V) {win : Window}
    (ht : Tracked sw.1.env c.In V win) :
    ∃ b, c.Γ.lookup x = some b ∧ b.param = false ∧ b.type.isSome = true ∧
      Tracked sw.1.env c.In b.sources win ∧ win.1 < r.loc ∧ c.L ≤ r.loc := by
  obtain ⟨s, hs, hcov⟩ := ht
  obtain ⟨b, hb, hsb, hpar, hty, hroot, hout⟩ := hV s hs
  obtain ⟨r₁, older, hr₁, ⟨y, -, htop⟩, hold⟩ := Fits.named hp.fits hb hpar
  rw [hl, Option.some.injEq] at hr₁
  subst hr₁
  simp only [hpar, Bool.false_eq_true, ↓reduceIte] at htop
  obtain ⟨-, hL, hlt, -⟩ := htop
  refine ⟨b, hb, hpar, hty, ⟨s, hsb, hcov⟩, ?_, hL⟩
  rcases hcov with hcov | ⟨v, hv, w', hw', h1, -⟩
  · obtain ⟨r', hr', he⟩ := hcov.loc
    rw [he]
    exact hlt _ (hold _ hout hroot r' hr')
  · have := (hg.brought (s.root, v) hv w' hw').1
    omega

/-- A write of `w` (in place `v`) at the path `p` below `x`, at `r`, whose location holds `y`
(in place `u`), giving `y'` (in place `u'`), which every live and every waiting window misses. -/
structure Write (si : IState) (sw : WState) (pend : List (Window × Value)) (r : Ref) (p : Path)
    (w v y u y' u' : Value) : Prop where
  cellW : sw.1.store[r.loc]? = some (some y)
  cellI : si.1.store[r.loc]? = some u
  setW : setW sw.1.store y (r.path ++ p) w = .ok y'
  setI : u.set (r.path ++ p) v = .ok u'
  rel : VRel si.1.store sw.1.store y u
  val : VRel si.1.store sw.1.store w v
  sub : ∀ win ∈ windowsOf y', win ∈ windowsOf y ∨ win ∈ windowsOf w
  resolve : resolveIn si.1.store y' = .ok u'
  misses : ∀ (ℓ : Nat) z, sw.1.store[ℓ]? = some (some z) → ∀ win ∈ windowsOf z, Misses r p win
  missesW : ∀ win ∈ windowsOf w, Misses r p win
  missesP : ∀ wd ∈ pend, Misses r p wd.1

namespace Write

variable {si : IState} {sw : WState} {r : Ref} {p : Path} {w v y u y' u' : Value}

/-- The store of windows after the write. -/
abbrev storeW (_ : Write si sw pend r p w v y u y' u') : List (Option Value) :=
  sw.1.store.set r.loc (some y')

/-- The in-place store after the write. -/
abbrev storeI (_ : Write si sw pend r p w v y u y' u') : List Value :=
  si.1.store.set r.loc u'

theorem region (h : Write si sw pend r p w v y u y' u') {win : Window}
    (hh : Holds sw.1.store si.1.store win) (hm : Misses r p win) :
    regionW h.storeW win = regionW sw.1.store win ∧ regionI h.storeI win = regionI si.1.store win := by
  obtain ⟨d, h₁, -⟩ := hh
  exact ⟨(regionW_write h.cellW h.setW hm h₁).trans h₁.symm, regionI_write h.cellI h.setI hm⟩

/-- A window of a live cell, or of the value written, reads alike after the write. -/
theorem live_region (h : Write si sw pend r p w v y u y' u') (hag : Agree D si sw) {win : Window}
    (hw : (∃ (ℓ : Nat) (z : Value), sw.1.store[ℓ]? = some (some z) ∧ win ∈ windowsOf z) ∨
      win ∈ windowsOf w) :
    Holds sw.1.store si.1.store win ∧ regionW h.storeW win = regionW sw.1.store win ∧
      regionI h.storeI win = regionI si.1.store win := by
  rcases hw with ⟨ℓ, z, hz, hwin⟩ | hwin
  · obtain ⟨u₀, -, hr⟩ := hag.live ℓ z hz
    exact ⟨hr.2 win hwin, h.region (hr.2 win hwin) (h.misses ℓ z hz win hwin)⟩
  · exact ⟨h.val.2 win hwin, h.region (h.val.2 win hwin) (h.missesW win hwin)⟩

/-- A window of what the written location holds after the write reads alike after it. -/
theorem new_region (h : Write si sw pend r p w v y u y' u') (hag : Agree D si sw) {win : Window}
    (hw : win ∈ windowsOf y') :
    Holds sw.1.store si.1.store win ∧ regionW h.storeW win = regionW sw.1.store win ∧
      regionI h.storeI win = regionI si.1.store win :=
  h.live_region hag ((h.sub win hw).imp_left fun hy => ⟨r.loc, y, h.cellW, hy⟩)

theorem lt (h : Write si sw pend r p w v y u y' u') : r.loc < sw.1.store.length :=
  (List.getElem?_eq_some_iff.1 h.cellW).1

theorem vrel_new (h : Write si sw pend r p w v y u y' u') (hag : Agree D si sw) :
    VRel h.storeI h.storeW y' u' := by
  refine ⟨(resolveIn_congr fun win hw => (h.new_region hag hw).2.2).trans h.resolve,
    fun win hw => ?_⟩
  obtain ⟨hh, h₁, h₂⟩ := h.new_region hag hw
  exact hh.region h₁ h₂

theorem live (h : Write si sw pend r p w v y u y' u') (hag : Agree D si sw) :
    ∀ (ℓ : Nat) z, h.storeW[ℓ]? = some (some z) →
      ∃ u₀, h.storeI[ℓ]? = some u₀ ∧ VRel h.storeI h.storeW z u₀ := by
  intro ℓ z hz
  by_cases hl : ℓ = r.loc
  · subst hl
    have hlt := h.lt
    simp only [List.getElem?_set_self hlt, Option.some.injEq] at hz
    subst hz
    refine ⟨u', List.getElem?_set_self (by rw [← hag.length]; exact hlt), h.vrel_new hag⟩
  · rw [List.getElem?_set_ne (Ne.symm hl)] at hz
    obtain ⟨u₀, hu₀, hr⟩ := hag.live ℓ z hz
    refine ⟨u₀, by rw [List.getElem?_set_ne (Ne.symm hl)]; exact hu₀, ?_⟩
    exact hr.region (fun win hw => (h.live_region hag (.inl ⟨ℓ, z, hz, hw⟩)).2.1)
      fun win hw => (h.live_region hag (.inl ⟨ℓ, z, hz, hw⟩)).2.2

/-- The states after the write agree. -/
theorem agree (h : Write si sw pend r p w v y u y' u') (hag : Agree D si sw) (hvv : v.Viewed D) :
    Agree D ({ si.1 with store := h.storeI }, si.2) ({ sw.1 with store := h.storeW }, sw.2) := by
  refine ⟨hag.env, hag.world, by simp [hag.length], fun u₀ hu₀ => ?_, hag.cells, hag.disjoint,
    fun xr hxr => by simpa using hag.valid xr hxr, h.live hag⟩
  rcases List.mem_or_eq_of_mem_set hu₀ with hu₀ | rfl
  · exact hag.viewed u₀ hu₀
  · exact (hag.viewed u (List.mem_of_getElem? h.cellI)).set hvv h.setI

end Write

end Windows

end Stilt
