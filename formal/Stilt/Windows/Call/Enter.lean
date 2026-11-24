import Stilt.Windows.Call.EnterFold

/-!
# A callee's start, on the relation of windows

Both models start a call alike (`enter_rel`): they fail alike, or give the callee's states, from
which its simulation runs in the callee's context (`Ctx.callee`): the scope of its parameters
over the captured variables, no read around it, the values its `let` parameters were bound to as
what they brought in, the caller's store length as the start of its own locations, the result's
parameters, and each caller location's cell at the start as what it held then. The callee's
variables are new locations or the places of its `inout` arguments, which miss every window
live, waiting or passed at the call (E0423), so no variable of the callee's reaches one; and the
caller's simulation holds again once the call ends (`Leaves`).
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls}

/-- The windows a location of a store holds. -/
def oldOf (st : List (Option Value)) (ℓ : Nat) : List Window :=
  match st[ℓ]? with
  | some (some y) => windowsOf y
  | _ => []

/-- What a location of a store holds. -/
def startOf (st : List (Option Value)) (ℓ : Nat) : Option Value :=
  match st[ℓ]? with
  | some (some y) => some y
  | _ => none

theorem startOf_eq {st : List (Option Value)} {ℓ : Nat} {y : Value} (h : startOf st ℓ = some y) :
    st[ℓ]? = some (some y) := by
  unfold startOf at h
  split at h
  · rename_i y' hy
    cases h
    exact hy
  · cases h

/-- The context a callee runs in, from the store it starts with. -/
def Ctx.callee (Γ : ViewScope) (In : List (Name × Value)) (L : Nat) (P : List Name)
    (st : List (Option Value)) : Ctx :=
  ⟨Γ, [], In, L, P, oldOf st, startOf st⟩

variable {c : Ctx} {pend : List (Window × Value)} {si : IState} {sw : WState}
  {In : List (Name × Value)} {Γ : ViewScope} {bound : List (Name × Passed)} {s : InPlace.State}
  {t : State}

theorem EntryOk.topHolds {st : List (Option Value)} {env : List (Name × Ref)} {L : Nat}
    {xb : Name × ViewBinding} {xr : Name × Ref} {older : List (Name × Ref)}
    (h : EntryOk st In L xb xr older) : TopHolds st env In L xb xr older := by
  obtain ⟨hpar, ⟨-, u, hu, hf⟩ | ⟨-, hpath, w, hw, hin, hs⟩⟩ := h
  · refine ⟨u, cell_of_getElem? hu, ?_⟩
    simp only [hpar, ↓reduceIte]
    intro x hx win hwin
    rw [getW_free _ u hf hx] at hwin
    cases hwin
  · refine ⟨w, cell_of_getElem? hw, ?_⟩
    simp only [hpar, ↓reduceIte]
    intro x hx win hwin
    rw [hpath, getW_nil, Except.ok.injEq] at hx
    subst hx
    exact ⟨⟨w, hin, win, hwin, rfl, rfl⟩, hs fun hf => by rw [hf] at hwin; cases hwin⟩

theorem BaseOk.baseHolds {st : List (Option Value)} {L : Nat} {xr : Name × Ref}
    (h : BaseOk st L xr) : BaseHolds st xr := by
  obtain ⟨-, hpath, v, hv, hf⟩ := h
  exact ⟨v, cell_of_getElem? hv, hpath, hf⟩

theorem regionI_entered (h : InPlace.Entry si.1 bound s) {win : Window}
    (hh : Holds sw.1.store si.1.store win) : regionI s.store win = regionI si.1.store win := by
  obtain ⟨F, hF⟩ := h.store
  rw [hF]
  exact regionI_append F hh.ltI

/-- The callee's states agree. -/
theorem Entering.agree (hp : Pre D c pend si sw) (h : Entering D In si.1 sw.1 Γ bound s t)
    (hcompat : (bound.map Prod.snd).Pairwise InPlace.Passed.Compat) : Agree D (s, si.2) (t, sw.2) where
  env := h.2.1.env
  world := hp.agree.world
  length := h.2.1.length
  viewed := h.2.1.viewed
  cells := hp.agree.cells
  disjoint := h.1.disjoint hp.agree.disjoint hcompat
  valid := h.1.valid
  live ℓ y hy := by
    obtain ⟨u, hu, hv⟩ := h.2.1.cells ℓ y hy
    exact ⟨u, hu, hv.region (fun win hw => h.2.1.regions win (hv.2 win hw))
      fun win hw => regionI_entered h.1 (hv.2 win hw)⟩

/-- The callee's simulation holds at its start. -/
theorem Entering.pre (hp : Pre D c pend si sw) (h : Entering D In si.1 sw.1 Γ bound s t)
    (hcompat : (bound.map Prod.snd).Pairwise InPlace.Passed.Compat) (P : List Name) :
    Pre D (Ctx.callee Γ In sw.1.store.length P t.store) pend (s, si.2) (t, sw.2) where
  agree := h.agree hp hcompat
  fits := Fits.mono (fun _ _ _ hx => hx.topHolds) (fun _ hx => hx.baseHolds) h.2.2
  outer ℓ x _ hx := ⟨fun w hw => by simp only [Ctx.callee, oldOf, hx]; exact hw, x,
    by simp [Ctx.callee, startOf, hx], .inl rfl⟩
  owned ℓ x hℓ hx := by
    refine ⟨h.2.1.owned ℓ x hℓ hx, fun w hw => ?_⟩
    obtain ⟨u, -, hv⟩ := h.2.1.cells ℓ x hx
    have := (hv.2 w hw).lt
    simp only [Ctx.callee] at hℓ
    omega
  pend wd hwd := by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hp.pend wd hwd
    have hh : Holds sw.1.store si.1.store wd.1 := ⟨wd.2, h₁, h₂, h₃, h₄⟩
    exact ⟨(h.2.1.regions _ hh).trans h₁, (regionI_entered h.1 hh).trans h₂, h₃, h₄⟩
  start := h.len hp.agree
  alive ℓ y _ hst := ⟨y, startOf_eq hst⟩

/-- No variable of the callee reaches a window before its locations that the reads around the
call watch: each is a new location or an `inout` argument's place, which misses it. -/
theorem unreached_callee (hp : Pre D c pend si sw) (h : Entering D In si.1 sw.1 Γ bound s t)
    {ps₀ : List Param} {bound' : List (Name × Passed)} (hB : BoundRel D c si sw ps₀ bound bound')
    {w : Window} (hlt : w.1 < sw.1.store.length) (hwat : Watched c.R sw.1.env w) :
    Unreached t.env w := by
  intro xr hxr
  rw [h.2.1.env] at hxr
  rcases h.1.refs xr hxr with hfresh | ⟨y, x, q, r, hm, hl, heq⟩
  · rw [← hp.agree.length] at hfresh
    exact .inl (by simp [Window.ref]; omega)
  · obtain ⟨⟨qs, hres, hu⟩, -⟩ := hB.places y x q hm
    have hl' : sw.1.env.lookup x = some r := by rw [hp.agree.env]; exact hl
    rw [heq]
    simpa [InPlace.placeRef, InPlace.Ref.toPath] using hwat.avoids hl' hres hu

/-- A window a caller location held at the callee's start lies before it, and the reads around
the call watch it. -/
theorem old_callee (hp : Pre D c pend si sw) (hg : Guards D c pend sw.1.env)
    (h : Entering D In si.1 sw.1 Γ bound s t) {ℓ : Nat} (hℓ : ℓ < sw.1.store.length) {w : Window}
    (hw : w ∈ oldOf t.store ℓ) : w.1 < ℓ ∧ Watched c.R sw.1.env w := by
  unfold oldOf at hw
  split at hw
  · rename_i y hy
    rcases h.2.1.caller ℓ hℓ with he | ⟨u, hu, hf, -⟩
    · rw [he] at hy
      refine ⟨?_, Pre.watched hp hg ℓ y hy w hw⟩
      by_cases hl : ℓ < c.L
      · exact (hg.old ℓ hl w ((hp.outer ℓ y hl hy).1 w hw)).1
      · exact (hp.owned ℓ y (by omega) hy).2 w hw
    · rw [hu, Option.some.injEq, Option.some.injEq] at hy
      subst hy
      rw [hf] at hw
      cases hw
  · cases hw

/-- What the callee's context guards at its start. -/
theorem Entering.guards (hp : Pre D c pend si sw) (hg : Guards D c pend sw.1.env)
    (h : Entering D In si.1 sw.1 Γ bound s t) {ps₀ : List Param} {bound' : List (Name × Passed)}
    (hB : BoundRel D c si sw ps₀ bound bound')
    (hIn : ∀ xv ∈ In, ∀ win ∈ windowsOf xv.2, Holds sw.1.store si.1.store win ∧
      Watched c.R sw.1.env win) (P : List Name) :
    Guards D (Ctx.callee Γ In sw.1.store.length P t.store) pend t.env where
  fenced := Fits.mono (fun _ _ _ hx hpar => by rw [hx.1] at hpar; cases hpar) (fun _ _ => trivial)
    h.2.2
  brought xv hxv w hw :=
    ⟨(hIn xv hxv w hw).1.lt, unreached_callee hp h hB (hIn xv hxv w hw).1.lt (hIn xv hxv w hw).2⟩
  old ℓ hℓ w hw := by
    obtain ⟨hlt, hwat⟩ := old_callee hp hg h hℓ hw
    exact ⟨hlt, unreached_callee hp h hB (by simp only [Ctx.callee] at hℓ; omega) hwat⟩
  pend wd hwd := by
    obtain ⟨h₁, -⟩ := hp.pend wd hwd
    exact guarded_of_unreached (unreached_callee hp h hB (regionW_lt h₁) (.inr (hg.pend wd hwd))) _
  start xr hxr hl y hst := by
    obtain ⟨⟨u, hu, hf⟩, -⟩ := h.2.1.inout xr hxr hl
    have := startOf_eq hst
    rw [hu, Option.some.injEq, Option.some.injEq] at this
    exact this ▸ hf

/-- Distinct names name distinct parameters. -/
theorem eq_of_name : ∀ {ps : List Param}, (ps.map Param.name).Nodup → ∀ {p q : Param}, p ∈ ps →
    q ∈ ps → p.name = q.name → p = q
  | [], _, _, _, hp, _, _ => nomatch hp
  | r :: ps, hnd, p, q, hp, hq, he => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hn := hnd.1
    rcases List.mem_cons.1 hp with h₁ | hp' <;> rcases List.mem_cons.1 hq with h₂ | hq'
    · rw [h₁, h₂]
    · subst h₁
      exact absurd (List.mem_map.2 ⟨q, hq', he.symm⟩) hn
    · subst h₂
      exact absurd (List.mem_map.2 ⟨p, hp', he⟩) hn
    · exact eq_of_name hnd.2 hp' hq' he

/-- The caller's simulation holds again once the call ends: the callee started from the caller's
store, and each of the result's parameters is at a location of the callee's own. -/
theorem Entering.leaves (hp : Pre D c pend si sw) (hg : Guards D c pend sw.1.env)
    (h : Entering D In si.1 sw.1 Γ bound s t) {ps₀ : List Param} {bound' : List (Name × Passed)}
    (hB : BoundRel D c si sw ps₀ bound bound') (hnd : (ps₀.map Param.name).Nodup) (result₀ : Ty) :
    Leaves D c (Ctx.callee Γ In sw.1.store.length (resultParams D ps₀ result₀) t.store) pend pend
      si sw t.env where
  pre := hp
  length := rfl
  starts ℓ hℓ := by
    rcases h.2.1.caller ℓ hℓ with he | ⟨u, hu, hf, o', ho'⟩
    · refine ⟨fun o ho => ⟨o, by simp [Ctx.callee, startOf, he, ho], .inl rfl⟩, fun y hy => ?_⟩
      have := startOf_eq hy
      rw [he] at this
      exact ⟨y, this⟩
    · exact ⟨fun _ _ => ⟨u, by simp [Ctx.callee, startOf, hu], .inr hf⟩, fun _ _ => ⟨o', ho'⟩⟩
  old ℓ hℓ w hw := (old_callee hp hg h hℓ hw).1
  pend _ h := h
  params p hpm r hr := by
    refine Nat.le_of_not_lt fun hlt => ?_
    obtain ⟨-, x, q, hm⟩ := h.2.1.inout (p, r) hr hlt
    obtain ⟨-, p₀, hp₀, hn, hmode⟩ := hB.places p x q hm
    simp only [Ctx.callee, resultParams] at hpm
    split at hpm
    · obtain ⟨p₁, hp₁, hn₁⟩ := List.mem_map.1 hpm
      obtain ⟨hp₁m, hcond⟩ := List.mem_filter.1 hp₁
      have := eq_of_name hnd hp₀ hp₁m (hn.trans hn₁.symm)
      subst this
      simp [hmode] at hcond
    · cases hpm

/-- A call's start, in both models: failing alike, or giving the callee's states, from which its
simulation runs in the callee's context, and from whose end the caller's holds again. -/
theorem enter_rel (hp : Pre D c pend si sw) (hg : Guards D c pend sw.1.env)
    {params : List Param} {ps ps' : List Passed} (hrel : PassRel D c si sw ps ps')
    (hkept : KeptFor D params ps') (hcompat : ps.Pairwise InPlace.Passed.Compat)
    {bound bound' : List (Name × Passed)}
    (hb : bindArgs params ps = some bound) (hb' : bindArgs params ps' = some bound')
    {captured : List (Name × Value)} (hcap : ∀ xv ∈ captured, xv.2.Viewed D)
    {Γ₀ : ViewScope} (hΓ₀ : ∀ xb ∈ Γ₀, xb.2.param = true) {ps₀ : List Param}
    (hps : ParamsInst D ps₀ params) (hnd : (ps₀.map Param.name).Nodup) (result₀ : Ty) :
    (∃ e, InPlace.memory.enter si captured bound = .error e ∧
        memory.enter sw captured bound' = .error e) ∨
      ∃ (si' : IState) (sw' : WState) (c' : Ctx), InPlace.memory.enter si captured bound = .ok si' ∧
        memory.enter sw captured bound' = .ok sw' ∧
        c'.Γ = ViewScope.params D Γ₀ ps₀ ∧ c'.R = [] ∧ c'.P = resultParams D ps₀ result₀ ∧
        c'.In = inOf bound' ∧ Pre D c' pend si' sw' ∧ Guards D c' pend sw'.1.env ∧
        Leaves D c c' pend pend si sw sw'.1.env := by
  have hB := boundRel hrel hkept hps hb hb'
  have hcomp : (bound.map Prod.snd).Pairwise InPlace.Passed.Compat := by
    rw [(InPlace.bindArgs_spec hb).2]
    exact hcompat
  have hin : ∀ ya ∈ bound', ∀ w, ya.2.value? = some w → (ya.1, w) ∈ inOf bound' :=
    fun ya hya w hw => mem_inOf.2 ⟨ya.2, hya, hw⟩
  have hIn : ∀ xv ∈ inOf bound', ∀ win ∈ windowsOf xv.2, Holds sw.1.store si.1.store win ∧
      Watched c.R sw.1.env win := fun xv hxv win hwin => by
    obtain ⟨a, hm, hw⟩ := mem_inOf.1 hxv
    exact hB.values (xv.1, a) hm xv.2 hw win hwin
  have hI : InPlace.memory.enter si captured bound = (·, si.2) <$> bound.foldlM
      (InPlace.enterStep si.1) (captured.foldr (fun xv t => InPlace.bind t xv.1 xv.2)
        ⟨[], si.1.store⟩) := by
    rw [← InPlace.enter_eq]
    rfl
  have hW : memory.enter sw captured bound' = (·, sw.2) <$> bound'.foldlM (enterStepW sw.1)
      (captured.foldr (fun xv s => bind s xv.1 xv.2) ⟨[], sw.1.store⟩) := by
    rw [← enterW_eq]
    rfl
  rw [hI, hW]
  rcases enter_fold hp hB hin Γ₀ [] _ _ (entering_base hp.agree captured hcap hΓ₀) with
    ⟨f, h₁, h₂⟩ | ⟨s', t', h₁, h₂, hE⟩
  · rw [h₁, h₂]
    exact .inl ⟨f, rfl, rfl⟩
  · rw [h₁, h₂]
    rw [List.nil_append] at hE
    exact .inr ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl, hE.pre hp hcomp _, hE.guards hp hg hB hIn _,
      hE.leaves hp hg hB hnd result₀⟩

end Windows

end Stilt
