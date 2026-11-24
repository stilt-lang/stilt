import Stilt.InPlace.Steps

/-!
# Entering a call

What the two models do when a call starts (values.inout-argument-order). Copy-in, copy-out
gives the callee a frame of copies; in place, the callee's variables are new
locations, except that each `inout` parameter refers to its argument's place
in the caller's store.

The law of exclusivity makes the places of one call's `inout` arguments
non-overlapping (modes.overlapping-inout), so the callee's references still reach
disjoint parts of the store, and the frame and the state agree. `Entered`
records what the end of the call needs: the callee's references are new
locations or the caller's places, and each `inout` parameter's name finds its
place.
-/

namespace Stilt.InPlace

/-! ## The places a call passes -/

/-- Two arguments of one call don't reach a common part of the caller's
variables: one isn't a place, or they have different roots, or disjoint
paths. -/
def Passed.Compat : Passed → Passed → Prop
  | .place x p, .place x' p' => x ≠ x' ∨ p.Disjoint p'
  | _, _ => True

theorem shape_of_resolved :
    ∀ {as : List Arg} {qs : List Passed}, Sim.ArgsResolved as qs → ∀ {x : Name} {p : Path},
      Passed.place x p ∈ qs → ∃ ps, p.Resolves ps ∧ (Place.mk x ps).shape ∈ inoutShapes as
  | [], [], _, _, _, hq => by simp at hq
  | .value _ :: as, .value _ :: qs, h, x, p, hq => by
    rcases List.mem_cons.1 hq with hq | hq
    · cases hq
    · simpa [inoutShapes] using shape_of_resolved (as := as) h hq
  | .value _ :: as, .moved _ _ :: qs, h, x, p, hq => by
    rcases List.mem_cons.1 hq with hq | hq
    · cases hq
    · simpa [inoutShapes] using shape_of_resolved (as := as) h hq
  | .inout ⟨y, ps⟩ :: as, .place _ r :: qs, ⟨rfl, hr, h⟩, x, p, hq => by
    rcases List.mem_cons.1 hq with hq | hq
    · cases hq
      exact ⟨ps, hr, List.mem_cons_self⟩
    · obtain ⟨ps', hr', hmem⟩ := shape_of_resolved h hq
      exact ⟨ps', hr', List.mem_cons_of_mem _ hmem⟩
  | [], _ :: _, h, _, _, _ => h.elim
  | .value _ :: _, [], h, _, _, _ => h.elim
  | .inout ⟨_, _⟩ :: _, [], h, _, _, _ => h.elim
  | .value _ :: _, .place _ _ :: _, h, _, _, _ => h.elim
  | .inout ⟨_, _⟩ :: _, .value _ :: _, h, _, _, _ => h.elim
  | .inout ⟨_, _⟩ :: _, .moved _ _ :: _, h, _, _, _ => h.elim

/-- The law of exclusivity, at run time: the places of one call's `inout`
arguments don't overlap (modes.overlapping-inout), whatever their indexes evaluate
to. -/
theorem compat_of_resolved :
    ∀ {as : List Arg} {qs : List Passed}, Sim.ArgsResolved as qs →
      (inoutShapes as).Pairwise (fun s t => s.overlaps t = false) → qs.Pairwise Passed.Compat
  | [], [], _, _ => .nil
  | .value _ :: as, .value _ :: qs, h, hd =>
    .cons (fun _ _ => trivial) (compat_of_resolved h (by simpa [inoutShapes] using hd))
  | .value _ :: as, .moved _ _ :: qs, h, hd =>
    .cons (fun _ _ => trivial) (compat_of_resolved h (by simpa [inoutShapes] using hd))
  | .inout ⟨x, ps⟩ :: as, .place _ p :: qs, ⟨rfl, hr, h⟩, hd => by
    simp only [inoutShapes, List.pairwise_cons] at hd
    refine .cons (fun q hq => ?_) (compat_of_resolved h hd.2)
    cases q with
    | value _ | moved _ _ => trivial
    | place x' p' =>
      obtain ⟨ps', hr', hmem⟩ := shape_of_resolved h hq
      by_cases hx : x = x'
      · subst hx
        exact .inr (Path.disjoint_of_not_overlaps (p := ⟨x, ps⟩) (q := ⟨x, ps'⟩) rfl
          (hd.1 _ hmem) hr hr')
      · exact .inl hx
  | [], _ :: _, h, _ => h.elim
  | .value _ :: _, [], h, _ => h.elim
  | .inout ⟨_, _⟩ :: _, [], h, _ => h.elim
  | .value _ :: _, .place _ _ :: _, h, _ => h.elim
  | .inout ⟨_, _⟩ :: _, .value _ :: _, h, _ => h.elim
  | .inout ⟨_, _⟩ :: _, .moved _ _ :: _, h, _ => h.elim

theorem bindArgs_spec :
    ∀ {params : List Param} {passed : List Passed} {bound : List (Name × Passed)},
      bindArgs params passed = some bound →
        bound.map Prod.fst = params.map Param.name ∧ bound.map Prod.snd = passed
  | [], [], _, h => by
    cases h
    exact ⟨rfl, rfl⟩
  | p :: ps, a :: args, bound, h => by
    unfold bindArgs at h
    split at h <;> first
      | (cases hb : bindArgs ps args with
          | none => simp [hb] at h
          | some b =>
            simp only [hb, Option.map_some, Option.some.injEq] at h
            subst h
            obtain ⟨h₁, h₂⟩ := bindArgs_spec hb
            exact ⟨by simp [h₁], by simp [h₂]⟩)
      | cases h
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h

/-! ## The callee's state -/

/-- The reference an `inout` parameter gets: its argument's place. -/
def placeRef (r : Ref) (p : Path) : Ref := ⟨r.loc, r.path ++ p⟩

theorem placeRef_disjoint {env : List (Name × Ref)}
    (hp : env.Pairwise fun a b => a.2.Disjoint b.2) {x x' : Name} {r r' : Ref} {p p' : Path}
    (hl : env.lookup x = some r) (hl' : env.lookup x' = some r')
    (hc : Passed.Compat (.place x p) (.place x' p')) :
    (placeRef r p).Disjoint (placeRef r' p') := by
  by_cases hx : x = x'
  · subst hx
    rw [hl] at hl'
    cases hl'
    rcases hc with hc | hc
    · exact absurd rfl hc
    · exact Path.Disjoint.prefix r.toPath hc
  · exact Path.Disjoint.append (lookup_disjoint hp hl hl' hx) p p'

/-- One step of `InPlace.enter`: binding one parameter. -/
def enterStep (caller s₀ : State) : Name × Passed → Except Fault State
  | (y, .value v) | (y, .moved _ v) => pure (InPlace.bind s₀ y v)
  | (y, .place x path) =>
    match caller.env.lookup x with
    | some r => (fun _ => { s₀ with env := (y, placeRef r path) :: s₀.env }) <$> deref caller r path
    | none => .error .stuck

/-- One step of `Copy.enter`: binding one parameter. -/
def copyEnterStep (caller fr₀ : Copy.Frame) : Name × Passed → Except Fault Copy.Frame
  | (y, .value v) | (y, .moved _ v) => pure ((y, v) :: fr₀)
  | (y, .place x path) => (fun v => (y, v) :: fr₀) <$> Copy.read caller x path

theorem enter_eq (caller : State) (captured : List (Name × Value)) (bound : List (Name × Passed)) :
    InPlace.frames.enter caller captured bound = bound.foldlM (enterStep caller)
      (captured.foldr (fun xv t => InPlace.bind t xv.1 xv.2) ⟨[], caller.store⟩) := by
  show InPlace.enter caller captured bound = _
  unfold InPlace.enter
  dsimp only
  congr 1
  all_goals first
    | rfl
    | (funext s₀ ya
       obtain ⟨y, a⟩ := ya
       cases a <;> rfl)

theorem copy_enter_eq (caller captured : Copy.Frame) (bound : List (Name × Passed)) :
    Copy.frames.enter caller captured bound = bound.foldlM (copyEnterStep caller) captured := by
  show Copy.enter caller captured bound = _
  unfold Copy.enter
  congr 1
  funext fr₀ ya
  obtain ⟨y, a⟩ := ya
  cases a <;> rfl

/-- What the start of a call gives, once the parameters `pre` are bound: the
frame and the callee's state agree, the callee's store extends the caller's,
each reference is a new location or the place of an `inout` argument, and
each `inout` parameter's name finds its place, which the caller can read. -/
structure Entered (s : State) (pre : List (Name × Passed)) (frc : Copy.Frame) (sc : State) :
    Prop where
  agrees : Agrees frc sc
  store : ∃ F, sc.store = s.store ++ F
  refs : ∀ xr ∈ sc.env, s.store.length ≤ xr.2.loc ∨
    ∃ y x p r, (y, Passed.place x p) ∈ pre ∧ s.env.lookup x = some r ∧ xr.2 = placeRef r p
  places : ∀ y x p, (y, Passed.place x p) ∈ pre →
    ∃ r, s.env.lookup x = some r ∧ sc.env.lookup y = some (placeRef r p) ∧
      ∃ u, deref s r p = .ok u

theorem entered_base (s : State) :
    ∀ {captured : List (Name × Value)}, (∀ xv ∈ captured, xv.2.Safe) →
      Entered s [] captured (captured.foldr (fun xv t => InPlace.bind t xv.1 xv.2) ⟨[], s.store⟩)
  | [], _ => ⟨⟨trivial, .nil, by simp⟩, ⟨[], by simp⟩, by simp, by simp⟩
  | (x, v) :: captured, h => by
    have ih := entered_base s fun xv hxv => h xv (List.mem_cons_of_mem _ hxv)
    obtain ⟨F, hF⟩ := ih.store
    refine ⟨ih.agrees.bind x (h (x, v) List.mem_cons_self), ⟨F ++ [v], ?_⟩, ?_, by simp⟩
    · show (List.foldr (β := State) _ _ captured).store ++ [v] = _
      rw [hF, List.append_assoc]
    · intro xr hxr
      rcases List.mem_cons.1 hxr with rfl | hxr
      · refine .inl ?_
        show s.store.length ≤ (List.foldr (β := State) _ _ captured).store.length
        rw [hF]
        simp
      · exact ih.refs xr hxr

namespace Entered

variable {s : State} {pre : List (Name × Passed)} {fr₀ : Copy.Frame} {s₀ : State}

theorem lookup_keep (_ : Entered s pre fr₀ s₀) {y : Name} (hy : y ∉ pre.map Prod.fst) {r r' : Ref}
    {y' x : Name} {p : Path} (hmem : (y', Passed.place x p) ∈ pre)
    (hl : s₀.env.lookup y' = some r) :
    List.lookup y' ((y, r') :: s₀.env) = some r := by
  have hne : y' ≠ y := fun he => hy (List.mem_map.2 ⟨_, hmem, he⟩)
  rw [lookup_cons_ne hne, hl]

/-- Binding a parameter that takes a value. -/
theorem value (h : Entered s pre fr₀ s₀) {y : Name} (hy : y ∉ pre.map Prod.fst) {a : Passed}
    {v : Value} (ha : a.value? = some v) (hv : v.Safe) :
    Entered s (pre ++ [(y, a)]) ((y, v) :: fr₀) (InPlace.bind s₀ y v) := by
  obtain ⟨F, hF⟩ := h.store
  refine ⟨h.agrees.bind y hv, ⟨F ++ [v], by simp [InPlace.bind, hF]⟩, ?_, ?_⟩
  · intro xr hxr
    rcases List.mem_cons.1 hxr with rfl | hxr
    · exact .inl (by simp [hF])
    · rcases h.refs xr hxr with hfresh | ⟨y', x, p, r, hmem, hl, heq⟩
      · exact .inl hfresh
      · exact .inr ⟨y', x, p, r, List.mem_append_left _ hmem, hl, heq⟩
  · intro y' x p hmem
    rcases List.mem_append.1 hmem with hmem | hmem
    · obtain ⟨r, hl, hly, hu⟩ := h.places y' x p hmem
      exact ⟨r, hl, h.lookup_keep hy hmem hly, hu⟩
    · simp only [List.mem_singleton, Prod.mk.injEq] at hmem
      obtain ⟨-, rfl⟩ := hmem
      cases ha

/-- Binding an `inout` parameter to its argument's place. -/
theorem place {fr : Copy.Frame} (h : Entered s pre fr₀ s₀) (hs : Agrees fr s) {y x : Name}
    {p : Path}
    (hy : y ∉ pre.map Prod.fst)
    (hc : ∀ y' x' p', (y', Passed.place x' p') ∈ pre → Passed.Compat (.place x' p') (.place x p))
    {r : Ref} (hl : s.env.lookup x = some r) {u : Value} (hu : deref s r p = .ok u)
    (hsafe : u.Safe) :
    Entered s (pre ++ [(y, .place x p)]) ((y, u) :: fr₀)
      { s₀ with env := (y, placeRef r p) :: s₀.env } := by
  obtain ⟨F, hF⟩ := h.store
  have hlt := lt_of_deref hu
  have hd : deref ⟨[], s₀.store⟩ (placeRef r p) [] = .ok u := by
    rw [hF, deref_store_append (r := placeRef r p) hlt]
    simpa [deref, placeRef] using hu
  refine ⟨⟨⟨rfl, hd, h.agrees.holds⟩, .cons (fun xr hxr => ?_) h.agrees.disjoint, ?_⟩,
    h.store, ?_, ?_⟩
  · rcases h.refs xr hxr with hfresh | ⟨y', x', p', r', hmem, hl', heq⟩
    · exact .inl (by simp [placeRef]; omega)
    · rw [heq]
      exact (placeRef_disjoint hs.disjoint hl' hl (hc y' x' p' hmem)).symm
  · intro xv hxv
    rcases List.mem_cons.1 hxv with rfl | hxv
    · exact hsafe
    · exact h.agrees.safe xv hxv
  · intro xr hxr
    rcases List.mem_cons.1 hxr with rfl | hxr
    · exact .inr ⟨y, x, p, r, by simp, hl, rfl⟩
    · rcases h.refs xr hxr with hfresh | ⟨y', x', p', r', hmem, hl', heq⟩
      · exact .inl hfresh
      · exact .inr ⟨y', x', p', r', List.mem_append_left _ hmem, hl', heq⟩
  · intro y' x' p' hmem
    rcases List.mem_append.1 hmem with hmem | hmem
    · obtain ⟨r', hl', hly, hu'⟩ := h.places y' x' p' hmem
      exact ⟨r', hl', h.lookup_keep hy hmem hly, hu'⟩
    · simp only [List.mem_singleton, Prod.mk.injEq, Passed.place.injEq] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      exact ⟨r, hl, List.lookup_cons_self, u, hu⟩

end Entered

/-- Binding the parameters `rest`, after `pre`, ends alike in both models. -/
theorem enter_fold {fr : Copy.Frame} {s : State} (hs : Agrees fr s) :
    ∀ (rest pre : List (Name × Passed)) (fr₀ : Copy.Frame) (s₀ : State), Entered s pre fr₀ s₀ →
      ((pre ++ rest).map Prod.fst).Nodup → ((pre ++ rest).map Prod.snd).Pairwise Passed.Compat →
      Sim.PassedSafe (rest.map Prod.snd) →
      (∃ f, rest.foldlM (copyEnterStep fr) fr₀ = .error f ∧
          rest.foldlM (enterStep s) s₀ = .error f) ∨
        ∃ frc sc, rest.foldlM (copyEnterStep fr) fr₀ = .ok frc ∧
          rest.foldlM (enterStep s) s₀ = .ok sc ∧ Entered s (pre ++ rest) frc sc
  | [], pre, fr₀, s₀, h, _, _, _ => .inr ⟨fr₀, s₀, rfl, rfl, by simpa using h⟩
  | (y, a) :: rest, pre, fr₀, s₀, h, hnd, hc, hsafe => by
    have hy : y ∉ pre.map Prod.fst := by
      intro hmem
      simp only [List.map_append, List.map_cons, List.nodup_append] at hnd
      exact hnd.2.2 y hmem y List.mem_cons_self rfl
    have hassoc : pre ++ (y, a) :: rest = (pre ++ [(y, a)]) ++ rest := by simp
    have hsafe' : Sim.PassedSafe (rest.map Prod.snd) :=
      fun q hq => hsafe q (List.mem_cons_of_mem _ hq)
    cases a with
    | value v =>
      have hv : v.Safe := hsafe _ List.mem_cons_self v rfl
      rw [hassoc] at hnd hc ⊢
      exact enter_fold hs rest _ _ _ (h.value hy rfl hv) hnd hc hsafe'
    | moved x v =>
      have hv : v.Safe := hsafe _ List.mem_cons_self v rfl
      rw [hassoc] at hnd hc ⊢
      exact enter_fold hs rest _ _ _ (h.value hy rfl hv) hnd hc hsafe'
    | place x p =>
      have hcp : ∀ y' x' p', (y', Passed.place x' p') ∈ pre →
          Passed.Compat (.place x' p') (.place x p) := fun y' x' p' hmem => by
        simp only [List.map_append, List.map_cons, List.pairwise_append] at hc
        exact hc.2.2 _ (List.mem_map.2 ⟨_, hmem, rfl⟩) _ List.mem_cons_self
      have hread := hs.read x p
      simp only [List.foldlM_cons, copyEnterStep, enterStep]
      cases hl : s.env.lookup x with
      | none =>
        simp only [InPlace.read, hl] at hread
        simp only [hread]
        exact .inl ⟨.stuck, rfl, rfl⟩
      | some r =>
        simp only [InPlace.read, hl] at hread
        simp only [hread]
        cases hu : deref s r p with
        | error f => exact .inl ⟨f, rfl, rfl⟩
        | ok u =>
          have hsu : u.Safe := hs.read_safe (hread.trans hu)
          rw [hassoc] at hnd hc ⊢
          exact enter_fold hs rest _ _ _ (h.place hs hy hcp hl hu hsu) hnd hc hsafe'

/-- Both models start a call alike. -/
theorem Agrees.enter {fr : Copy.Frame} {s : State} (hs : Agrees fr s)
    {captured : List (Name × Value)} (hc : ∀ xv ∈ captured, xv.2.Safe)
    {bound : List (Name × Passed)} (hnd : (bound.map Prod.fst).Nodup)
    (hcompat : (bound.map Prod.snd).Pairwise Passed.Compat)
    (hsafe : Sim.PassedSafe (bound.map Prod.snd)) :
    (∃ f, Copy.frames.enter fr captured bound = .error f ∧
        InPlace.frames.enter s captured bound = .error f) ∨
      ∃ frc sc, Copy.frames.enter fr captured bound = .ok frc ∧
        InPlace.frames.enter s captured bound = .ok sc ∧ Entered s bound frc sc := by
  rw [copy_enter_eq, enter_eq]
  exact enter_fold hs bound [] _ _ (entered_base s hc) (by simpa using hnd)
    (by simpa using hcompat) hsafe

end Stilt.InPlace
