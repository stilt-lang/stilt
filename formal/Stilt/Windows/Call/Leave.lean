import Stilt.Windows.Call.Reads
import Stilt.Windows.Read
import Stilt.Windows.Bind

/-!
# Leaving a call

When a call ends, the caller goes on with its own variables, the store the callee left with
the callee's locations freed, and the world the callee left (values.inout-arguments,
views.across-calls). The callee's context started from the caller's store: each location live
then was live in it, as it was or read through its windows, and only those (`StartsFrom`). The
callee keeps each of them live, as it was then or with a value that holds no window, so the
caller's cells are as they were or hold no window, and the simulation the caller kept holds
again.
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls}

/-- What a callee's context knows of the store it started from: each location live then is one
the callee starts with, as it was or with a value that holds no window, and only those. -/
def StartsFrom (c' : Ctx) (st : List (Option Value)) : Prop :=
  ∀ ℓ < c'.L, (∀ o, st[ℓ]? = some (some o) → ∃ y, c'.Start ℓ = some y ∧ (y = o ∨ Free y)) ∧
    ∀ y, c'.Start ℓ = some y → ∃ o, st[ℓ]? = some (some o)

/-- The caller's state once a call ends, in place: its variables, the store and the world the
callee left. -/
def leftIn (si si' : IState) : IState := ({ si.1 with store := si'.1.store }, si'.2)

/-- The caller's state once a call ends, with windows: its variables, the store the callee
left with the callee's locations freed, and the world the callee left. -/
def leftW (sw sw' : WState) : WState :=
  freeFrom sw.1.store.length ({ sw.1 with store := sw'.1.store }, sw'.2)

theorem cell_of_getElem? {st : List (Option Value)} {ℓ : Nat} {y : Value}
    (h : st[ℓ]? = some (some y)) : cell st ℓ = .ok y := by
  simp [cell, h]

theorem leftW_getElem? {sw sw' : WState} {ℓ : Nat} (h : ℓ < sw.1.store.length) :
    (leftW sw sw').1.store[ℓ]? = sw'.1.store[ℓ]? :=
  freeStore_getElem?_lt _ h

variable {c c' : Ctx} {pend pend' : List (Window × Value)} {si si' : IState} {sw sw' : WState}

/-- A caller's location after the call: live if it was live before, and then as it was or
holding no window. -/
theorem cell_after (hp' : Pre D c' pend' si' sw') (hS : StartsFrom c' sw.1.store) {ℓ : Nat}
    (hl : ℓ < c'.L) :
    (∀ x, sw'.1.store[ℓ]? = some (some x) →
      ∃ o, sw.1.store[ℓ]? = some (some o) ∧ (x = o ∨ Free x)) ∧
    ∀ o, sw.1.store[ℓ]? = some (some o) → ∃ x, sw'.1.store[ℓ]? = some (some x) := by
  refine ⟨fun x hx => ?_, fun o ho => ?_⟩
  · obtain ⟨-, y, hy, hxy⟩ := hp'.outer ℓ x hl hx
    obtain ⟨o, ho⟩ := (hS ℓ hl).2 y hy
    obtain ⟨y', hy', hyo⟩ := (hS ℓ hl).1 o ho
    rw [hy] at hy'
    cases hy'
    refine ⟨o, ho, ?_⟩
    rcases hxy with rfl | hx
    · rcases hyo with rfl | hy
      · exact .inl rfl
      · exact .inr hy
    · exact .inr hx
  · obtain ⟨y, hy, -⟩ := (hS ℓ hl).1 o ho
    exact hp'.alive ℓ y hl hy

/-- The states once a call ends agree. -/
theorem agree_left (hp : Pre D c pend si sw) (hp' : Pre D c' pend' si' sw')
    (hn : c'.L = sw.1.store.length) (hold : ∀ ℓ < c'.L, ∀ w ∈ c'.Old ℓ, w.1 < ℓ) :
    Agree D (leftIn si si') (leftW sw sw') := by
  have hv : ∀ xr ∈ si.1.env, xr.2.loc < si'.1.store.length := fun xr hxr => by
    have h₁ := hp.agree.valid xr hxr
    have h₂ := hp'.start
    rw [← hp'.agree.length]
    rw [← hp.agree.length] at h₁
    omega
  have hag : Agree D (leftIn si si') ({ sw.1 with store := sw'.1.store }, sw'.2) :=
    ⟨hp.agree.env, hp'.agree.world, hp'.agree.length, hp'.agree.viewed, hp'.agree.cells,
      hp.agree.disjoint, hv, hp'.agree.live⟩
  refine hag.free _ fun ℓ x hl hx w hw => ?_
  have := hold ℓ (hn ▸ hl) w ((hp'.outer ℓ x (hn ▸ hl) hx).1 w hw)
  omega

/-- Every window of a live cell of the caller's state after a call reads a part that holds no
window. -/
theorem holds_left (hag : Agree D (leftIn si si') (leftW sw sw')) {ℓ : Nat} {x : Value}
    (hx : (leftW sw sw').1.store[ℓ]? = some (some x)) :
    ∀ w ∈ windowsOf x, ∃ d, regionW (leftW sw sw').1.store w = .ok d ∧ Free d := by
  intro w hw
  obtain ⟨u, -, hr⟩ := hag.live ℓ x hx
  obtain ⟨d, h₁, -, h₃, -⟩ := hr.2 w hw
  exact ⟨d, h₁, h₃⟩

theorem not_mem_of_free {v : Value} (h : Free v) {w : Window} : w ∉ windowsOf v := by
  simp [show windowsOf v = [] from h]

/-- A caller's variable fits as it did once the call ends. -/
theorem topHolds_left (hp' : Pre D c' pend' si' sw') (hS : StartsFrom c' sw.1.store)
    (hn : c'.L = sw.1.store.length) (hag : Agree D (leftIn si si') (leftW sw sw'))
    {xb : Name × ViewBinding} {xr : Name × Ref} {older : List (Name × Ref)}
    (hxr : xr.2.loc < sw.1.store.length) (h : TopHolds sw.1.store sw.1.env c.In c.L xb xr older) :
    TopHolds (leftW sw sw').1.store sw.1.env c.In c.L xb xr older := by
  obtain ⟨o, hc, hif⟩ := h
  obtain ⟨x, hx⟩ := (cell_after hp' hS (hn ▸ hxr)).2 o (cell_eq_ok hc)
  obtain ⟨o', ho', hxo⟩ := (cell_after hp' hS (hn ▸ hxr)).1 x hx
  rw [cell_eq_ok hc] at ho'
  cases ho'
  have hx' : (leftW sw sw').1.store[xr.2.loc]? = some (some x) := by
    rw [leftW_getElem? hxr]; exact hx
  refine ⟨x, cell_of_getElem? hx', ?_⟩
  split
  · rename_i hpar
    simp only [hpar, ↓reduceIte] at hif
    intro z hz w hw
    rcases hxo with rfl | hfx
    · rcases getW_static _ _ (holds_left hag hx') hz with hfz | hall
      · exact absurd hw (not_mem_of_free hfz)
      · exact hif z (hall _) w hw
    · exact absurd hw (not_mem_of_free (getW_free _ _ hfx hz))
  · rename_i hpar
    simp only [hpar] at hif
    rcases hxo with rfl | hfx
    · exact hif
    · refine ⟨hif.1, hif.2.1, hif.2.2.1, ?_⟩
      split
      · exact fun w hw => absurd hw (not_mem_of_free hfx)
      · exact hfx

/-- A closure's captured variable fits as it did once the call ends. -/
theorem baseHolds_left (hp' : Pre D c' pend' si' sw') (hS : StartsFrom c' sw.1.store)
    (hn : c'.L = sw.1.store.length) {xr : Name × Ref} (hxr : xr.2.loc < sw.1.store.length)
    (h : BaseHolds sw.1.store xr) : BaseHolds (leftW sw sw').1.store xr := by
  obtain ⟨o, hc, hpath, hfo⟩ := h
  obtain ⟨x, hx⟩ := (cell_after hp' hS (hn ▸ hxr)).2 o (cell_eq_ok hc)
  obtain ⟨o', ho', hxo⟩ := (cell_after hp' hS (hn ▸ hxr)).1 x hx
  rw [cell_eq_ok hc] at ho'
  cases ho'
  refine ⟨x, cell_of_getElem? (by rw [leftW_getElem? hxr]; exact hx), hpath, ?_⟩
  rcases hxo with rfl | hfx
  · exact hfo
  · exact hfx

theorem fits_left (hp : Pre D c pend si sw) (hp' : Pre D c' pend' si' sw')
    (hS : StartsFrom c' sw.1.store) (hn : c'.L = sw.1.store.length)
    (hag : Agree D (leftIn si si') (leftW sw sw')) :
    Fits (TopHolds (leftW sw sw').1.store sw.1.env c.In c.L) (BaseHolds (leftW sw sw').1.store)
      c.Γ sw.1.env :=
  Fits.mono_mem hp.fits
    (fun _ xr _ hs h => topHolds_left hp' hS hn hag
      (env_lt hp.agree xr (hs.subset List.mem_cons_self)) h)
    fun xr hxr h => baseHolds_left hp' hS hn (env_lt hp.agree xr hxr) h

/-- The caller's simulation once a call ends: the caller's variables, the store the callee left
with the callee's locations freed, from a callee that started from the caller's store and
whose waiting windows held the caller's. -/
theorem Pre.leave (hp : Pre D c pend si sw) (hp' : Pre D c' pend' si' sw')
    (hS : StartsFrom c' sw.1.store) (hn : c'.L = sw.1.store.length)
    (hold : ∀ ℓ < c'.L, ∀ w ∈ c'.Old ℓ, w.1 < ℓ) (hpend : ∀ wd ∈ pend, wd ∈ pend') :
    Pre D c pend (leftIn si si') (leftW sw sw') := by
  have hag := agree_left hp hp' hn hold
  have hlt : ∀ {ℓ}, ℓ < c.L → ℓ < sw.1.store.length := fun hl => Nat.lt_of_lt_of_le hl hp.start
  refine ⟨hag, fits_left hp hp' hS hn hag, fun ℓ x hl hx => ?_, fun ℓ x hl hx => ?_,
    fun wd hwd => ?_, ?_, fun ℓ y hl hy => ?_⟩
  · rw [leftW_getElem? (hlt hl)] at hx
    obtain ⟨o, ho, hxo⟩ := (cell_after hp' hS (hn ▸ hlt hl)).1 x hx
    obtain ⟨hw, y, hy, hoy⟩ := hp.outer ℓ o hl ho
    rcases hxo with rfl | hfx
    · exact ⟨hw, y, hy, hoy⟩
    · exact ⟨fun w hw' => absurd hw' (not_mem_of_free hfx), y, hy, .inr hfx⟩
  · by_cases hln : ℓ < sw.1.store.length
    · rw [leftW_getElem? hln] at hx
      obtain ⟨o, ho, hxo⟩ := (cell_after hp' hS (hn ▸ hln)).1 x hx
      obtain ⟨hex, hw⟩ := hp.owned ℓ o hl ho
      rcases hxo with rfl | hfx
      · exact ⟨hex, hw⟩
      · exact ⟨hex, fun w hw' => absurd hw' (not_mem_of_free hfx)⟩
    · exact absurd hx (freeStore_getElem?_ge _ (Nat.le_of_not_lt hln))
  · have h' := hp'.pend wd (hpend wd hwd)
    have hl := regionW_lt (hp.pend wd hwd).1
    refine ⟨?_, h'.2.1, h'.2.2⟩
    show regionW (freeStore _ sw'.1.store) wd.1 = _
    rw [regionW_freeStore hl]
    exact h'.1
  · show c.L ≤ (freeStore _ sw'.1.store).length
    rw [freeStore_length]
    have := hp'.start
    have := hp.start
    omega
  · obtain ⟨o, ho⟩ := hp.alive ℓ y hl hy
    obtain ⟨x, hx⟩ := (cell_after hp' hS (hn ▸ hlt hl)).2 o ho
    exact ⟨x, by rw [leftW_getElem? (hlt hl)]; exact hx⟩

end Windows

end Stilt
