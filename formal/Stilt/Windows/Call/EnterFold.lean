import Stilt.Windows.Call.EnterStep

/-!
# Binding a callee's variables

Both models bind a call's parameters alike: a `let` parameter at a new location, an `inout` one
to its argument's place, which both read alike, failing alike (`place_step`). From the captured
values on (`entering_base`), binding every parameter keeps `Entered`, the variables fitting the
callee's scope (`enter_fold`).
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls} {c : Ctx} {pend : List (Window × Value)}

theorem enterStepW_place {caller t : State} {x y : Name} {q : Path} {r : Ref}
    (hl : caller.env.lookup x = some r) {y₀ u : Value} (hc : t.store[r.loc]? = some (some y₀))
    (hr : resolve t.store y₀ = .ok u) :
    enterStepW caller t (y, .place x q) = (getW t.store y₀ (r.path ++ q)).bind fun _ =>
      .ok ⟨(y, ⟨r.loc, r.path ++ q⟩) :: t.env, t.store.set r.loc (some u)⟩ := by
  have hcell : cell t.store r.loc = .ok y₀ := by simp [cell, hc]
  simp only [enterStepW, hl, deref, hcell]
  change (getW t.store y₀ (r.path ++ q) >>= fun _ => resolve t.store y₀ >>= fun c =>
    (Except.ok (State.mk ((y, ⟨r.loc, r.path ++ q⟩) :: t.env) (t.store.set r.loc (some c))) :
      Except Fault State)) = _
  rw [hr]
  rfl

theorem enterStep_place {caller s : InPlace.State} {x y : Name} {q : Path} {r : Ref}
    (hl : caller.env.lookup x = some r) {u : Value} (hu : caller.store[r.loc]? = some u) :
    InPlace.enterStep caller s (y, .place x q) = (u.get (r.path ++ q)).bind fun _ =>
      .ok { s with env := (y, InPlace.placeRef r q) :: s.env } := by
  simp only [InPlace.enterStep, hl, InPlace.deref, hu]
  cases u.get (r.path ++ q) <;> rfl

/-- The place a caller's variable reaches, read through windows in a state of `Entered`: its
location holds a value read as the in-place one is, and read through its windows it is that. -/
theorem Entered.reads {si : IState} {sw : WState} (hag : Agree D si sw)
    {pre : List (Name × Passed)} {s : InPlace.State} {t : State} (h : Entered D si.1 sw.1 pre s t)
    {ℓ : Nat} (hl : ℓ < sw.1.store.length) {o u : Value} (ho : sw.1.store[ℓ]? = some (some o))
    (hu : si.1.store[ℓ]? = some u) (hs : s.store[ℓ]? = some u) :
    ∃ y₀, t.store[ℓ]? = some (some y₀) ∧ resolve t.store y₀ = .ok u ∧ ∀ P : Path,
      (∃ f, getW t.store y₀ P = .error f ∧ u.get P = .error f) ∨
        ∃ a b, getW t.store y₀ P = .ok a ∧ u.get P = .ok b := by
  obtain ⟨u₁, hu₁, hvo⟩ := hag.live ℓ o ho
  rw [hu, Option.some.injEq] at hu₁
  subst hu₁
  rcases h.caller ℓ hl with he | ⟨u', hu', hf', -⟩
  · rw [ho] at he
    refine ⟨o, he, ?_, fun P => ?_⟩
    · have hra : ∀ win ∈ windowsOf o, ReadAlike t.store si.1.store win := fun win hw => by
        obtain ⟨h₁, h₂⟩ := (hvo.2 win hw).readAlike
        refine ⟨?_, h₂⟩
        rw [part_eq_region, h.regions win (hvo.2 win hw), ← part_eq_region]
        exact h₁
      exact (resolve_eq_resolveIn hra).trans hvo.1
    · rw [getW_congr o P fun win hw => h.regions win (hvo.2 win hw)]
      rcases getW_rel hvo.1 hvo.readAlike P with ⟨f, h₁, h₂⟩ | ⟨a, b, h₁, h₂, -⟩
      · exact .inl ⟨f, h₁, h₂⟩
      · exact .inr ⟨a, b, h₁, h₂⟩
  · obtain ⟨u₂, hu₂, hvr⟩ := h.cells ℓ u' hu'
    rw [hs, Option.some.injEq] at hu₂
    have he : u' = u := by
      have := hvr.1
      rw [resolveIn_free _ hf', Except.ok.injEq] at this
      exact this.trans hu₂.symm
    rw [he] at hu' hf'
    refine ⟨u, hu', (VRel.free hf' (si := si.1.store) (sw := t.store)).resolve, fun P => ?_⟩
    rw [getW_of_free u P hf']
    cases u.get P with
    | error f => exact .inl ⟨f, rfl, rfl⟩
    | ok a => exact .inr ⟨a, a, rfl, rfl⟩

/-- An `inout` parameter's step, in both models: failing alike, or binding it to its argument's
place, the model of windows setting the place's location to the in-place value there. -/
theorem place_step {si : IState} {sw : WState} (hp : Pre D c pend si sw)
    {pre : List (Name × Passed)} {s : InPlace.State} {t : State} (hent : InPlace.Entry si.1 pre s)
    (h : Entered D si.1 sw.1 pre s t) (y x : Name) (q : Path) :
    (∃ f, InPlace.enterStep si.1 s (y, .place x q) = .error f ∧
        enterStepW sw.1 t (y, .place x q) = .error f) ∨
      ∃ (r : Ref) (u : Value), InPlace.enterStep si.1 s (y, .place x q) =
          .ok { s with env := (y, InPlace.placeRef r q) :: s.env } ∧
        enterStepW sw.1 t (y, .place x q) =
          .ok ⟨(y, ⟨r.loc, r.path ++ q⟩) :: t.env, t.store.set r.loc (some u)⟩ ∧
        InPlace.Entry si.1 (pre ++ [(y, .place x q)])
          { s with env := (y, InPlace.placeRef r q) :: s.env } ∧
        Entered D si.1 sw.1 (pre ++ [(y, .place x q)])
          { s with env := (y, InPlace.placeRef r q) :: s.env }
          ⟨(y, ⟨r.loc, r.path ++ q⟩) :: t.env, t.store.set r.loc (some u)⟩ ∧
        r.loc < sw.1.store.length ∧ Free u := by
  have hag := hp.agree
  cases hl : sw.1.env.lookup x with
  | none =>
    have hli : si.1.env.lookup x = none := by rw [← hag.env]; exact hl
    exact .inl ⟨.stuck, by simp [InPlace.enterStep, hli], by simp [enterStepW, hl]⟩
  | some r =>
    have hli : si.1.env.lookup x = some r := by rw [← hag.env]; exact hl
    obtain ⟨o, ho⟩ : ∃ o, sw.1.store[r.loc]? = some (some o) := by
      rcases Fits.lookup hp.fits hl with ⟨-, -, -, y₀, hy, -⟩ | ⟨y₀, hy, -⟩
      · exact ⟨y₀, cell_eq_ok hy⟩
      · exact ⟨y₀, cell_eq_ok hy⟩
    have hrl : r.loc < sw.1.store.length := (List.getElem?_eq_some_iff.1 ho).1
    obtain ⟨u, hu, -⟩ := hag.live r.loc o ho
    have hs : s.store[r.loc]? = some u := by
      obtain ⟨F, hF⟩ := hent.store
      rw [hF, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hu).1]
      exact hu
    have hf : Free u := (hag.viewed u (List.mem_of_getElem? hu)).free
    obtain ⟨y₀, hy₀, hres, hread⟩ := h.reads hag hrl ho hu hs
    rw [enterStep_place hli hu, enterStepW_place hl hy₀ hres]
    rcases hread (r.path ++ q) with ⟨f, h₁, h₂⟩ | ⟨a, b, h₁, h₂⟩
    · rw [h₁, h₂]
      exact .inl ⟨f, rfl, rfl⟩
    · rw [h₁, h₂]
      refine .inr ⟨r, u, rfl, rfl, hent.place y x q hli (u := b) ?_,
        h.place hrl hu hs hf ⟨o, ho⟩ y x q, hrl, hf⟩
      simp [InPlace.deref, hu, h₂]

theorem enterStep_value {caller s : InPlace.State} {y : Name} {a : Passed} {v : Value}
    (h : a.value? = some v) : InPlace.enterStep caller s (y, a) = .ok (InPlace.bind s y v) := by
  cases a with
  | value v' => cases h; rfl
  | moved z v' => cases h; rfl
  | place _ _ => cases h

theorem enterStepW_value {caller t : State} {y : Name} {a : Passed} {w : Value}
    (h : a.value? = some w) : enterStepW caller t (y, a) = .ok (bind t y w) := by
  cases a with
  | value v' => cases h; rfl
  | moved z v' => cases h; rfl
  | place _ _ => cases h

/-- What both models keep while they bind a callee's variables: the in-place entry, `Entered`,
and the variables fitting the scope so far. -/
def Entering (D : Decls) (In : List (Name × Value)) (si₁ : InPlace.State) (sw₁ : State)
    (Γ : ViewScope) (pre : List (Name × Passed)) (s : InPlace.State) (t : State) : Prop :=
  InPlace.Entry si₁ pre s ∧ Entered D si₁ sw₁ pre s t ∧
    Fits (EntryOk t.store In sw₁.store.length) (BaseOk t.store sw₁.store.length) Γ t.env

theorem Entering.len {si : IState} {sw : WState} (hag : Agree D si sw) {In : List (Name × Value)}
    {Γ : ViewScope} {pre : List (Name × Passed)} {s : InPlace.State} {t : State}
    (h : Entering D In si.1 sw.1 Γ pre s t) : sw.1.store.length ≤ t.store.length := by
  obtain ⟨F, hF⟩ := h.1.store
  rw [h.2.1.length, hF, hag.length]
  simp

/-- Binding every parameter, in both models: failing alike, or keeping `Entering`, the scope
grown by the parameters' bindings. -/
theorem enter_fold {si : IState} {sw : WState} (hp : Pre D c pend si sw)
    {In : List (Name × Value)} : ∀ {ps₀ : List Param} {bs bs' : List (Name × Passed)},
      BoundRel D c si sw ps₀ bs bs' → (∀ ya ∈ bs', ∀ w, ya.2.value? = some w → (ya.1, w) ∈ In) →
      ∀ (Γ : ViewScope) (pre : List (Name × Passed)) (s : InPlace.State) (t : State),
      Entering D In si.1 sw.1 Γ pre s t →
      (∃ f, bs.foldlM (InPlace.enterStep si.1) s = .error f ∧
          bs'.foldlM (enterStepW sw.1) t = .error f) ∨
        ∃ s' t', bs.foldlM (InPlace.enterStep si.1) s = .ok s' ∧
          bs'.foldlM (enterStepW sw.1) t = .ok t' ∧
          Entering D In si.1 sw.1 (ViewScope.params D Γ ps₀) (pre ++ bs) s' t'
  | _, _, _, .nil, _, Γ, pre, s, t, h => .inr ⟨s, t, rfl, rfl, by simpa [ViewScope.params] using h⟩
  | _, _, _, .value (p₀ := p₀) (a := a) (v := v) (w := w) hv hw hvw hvv _ hsrc _ hrest, hin, Γ, pre,
      s, t, h => by
    have hlen := h.len hp.agree
    have h' : Entering D In si.1 sw.1 ((p₀.name, ⟨some p₀.type, paramSources D p₀, true⟩) :: Γ)
        (pre ++ [(p₀.name, a)]) (InPlace.bind s p₀.name v) (bind t p₀.name w) := by
      refine ⟨h.1.value _ _ v, h.2.1.bind hlen (fun z hz => List.mem_append_left _ hz) _ hvw hvv,
        .cons rfl ⟨rfl, .inr ⟨hlen, rfl, w, by simp [Windows.bind],
          hin _ List.mem_cons_self w hw, hsrc⟩⟩ (Fits.keeps (keeps_append _ _ _) h.2.2)⟩
    simp only [List.foldlM_cons, enterStep_value hv, enterStepW_value hw]
    have := enter_fold hp hrest (fun ya hya => hin ya (List.mem_cons_of_mem _ hya)) _ _ _ _ h'
    rw [List.append_assoc, List.singleton_append] at this
    exact this
  | _, _, _, .place (p₀ := p₀) x q _ hres hu _ hrest, hin, Γ, pre, s, t, h => by
    simp only [List.foldlM_cons]
    rcases place_step hp h.1 h.2.1 p₀.name x q with ⟨f, h₁, h₂⟩ |
      ⟨r, u, h₁, h₂, hent, hen, hrl, hf⟩
    · rw [h₁, h₂]
      exact .inl ⟨f, rfl, rfl⟩
    · rw [h₁, h₂]
      have hlt : r.loc < t.store.length := by have := h.len hp.agree; omega
      have h' : Entering D In si.1 sw.1 ((p₀.name, ⟨some p₀.type, paramSources D p₀, true⟩) :: Γ)
          (pre ++ [(p₀.name, .place x q)]) { s with env := (p₀.name, InPlace.placeRef r q) :: s.env }
          ⟨(p₀.name, ⟨r.loc, r.path ++ q⟩) :: t.env, t.store.set r.loc (some u)⟩ :=
        ⟨hent, hen, .cons rfl ⟨rfl, .inl ⟨hrl, u, List.getElem?_set_self hlt, hf⟩⟩
          (Fits.keeps (keeps_set hrl hf) h.2.2)⟩
      have := enter_fold hp hrest (fun ya hya => hin ya (List.mem_cons_of_mem _ hya)) _ _ _ _ h'
      rw [List.append_assoc, List.singleton_append] at this
      exact this

/-- Binding the captured values, in both models: new locations with no window, each a captured
variable. -/
theorem entered_base {si : IState} {sw : WState} (hag : Agree D si sw) :
    ∀ captured : List (Name × Value), (∀ xv ∈ captured, xv.2.Viewed D) →
      let T := captured.foldr (fun xv s => bind s xv.1 xv.2) ⟨[], sw.1.store⟩
      Entered D si.1 sw.1 []
          (captured.foldr (fun xv t => InPlace.bind t xv.1 xv.2) ⟨[], si.1.store⟩) T ∧
        (∀ xr ∈ T.env, BaseOk T.store sw.1.store.length xr) ∧ sw.1.store.length ≤ T.store.length
  | [], _ => ⟨Entered.start hag, fun _ h => by simp at h, Nat.le_refl _⟩
  | (x, v) :: captured, hcap => by
    obtain ⟨h, hb, hlen⟩ := entered_base hag captured fun xv h => hcap xv (List.mem_cons_of_mem _ h)
    have hv : v.Viewed D := hcap (x, v) List.mem_cons_self
    refine ⟨h.bind hlen (fun _ h => h) x (VRel.free hv.free) hv, fun xr hxr => ?_, ?_⟩
    · simp only [List.foldr_cons, Windows.bind, List.mem_cons] at hxr
      rcases hxr with rfl | hxr
      · exact ⟨hlen, rfl, v, by simp [Windows.bind], hv.free⟩
      · exact BaseOk.keeps (keeps_append _ _ _) (hb xr hxr)
    · show sw.1.store.length ≤ (Windows.bind (captured.foldr (fun xv s => bind s xv.1 xv.2)
        ⟨[], sw.1.store⟩) x v).store.length
      generalize captured.foldr (fun xv s => bind s xv.1 xv.2) ⟨[], sw.1.store⟩ = T at hlen ⊢
      simp only [Windows.bind, List.length_append]
      omega

theorem entering_base {si : IState} {sw : WState} (hag : Agree D si sw) {In : List (Name × Value)}
    (captured : List (Name × Value)) (hcap : ∀ xv ∈ captured, xv.2.Viewed D) {Γ₀ : ViewScope}
    (hΓ₀ : ∀ xb ∈ Γ₀, xb.2.param = true) :
    Entering D In si.1 sw.1 Γ₀ []
      (captured.foldr (fun xv t => InPlace.bind t xv.1 xv.2) ⟨[], si.1.store⟩)
      (captured.foldr (fun xv s => bind s xv.1 xv.2) ⟨[], sw.1.store⟩) := by
  obtain ⟨h, hb, -⟩ := entered_base hag captured hcap
  exact ⟨InPlace.entry_base si.1 captured, h, .base hΓ₀ hb⟩

end Windows

end Stilt
