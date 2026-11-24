import Stilt.Sharing.Roots
import Stilt.InPlace.Enter

/-!
# Entering a call with sharing

What sharing does when a call starts (values.inout-argument-order): the callee's captured
variables and value parameters get new homes, and each `inout` parameter's home is its
argument's place, below its root's home, which no other binding of the caller overlaps once
`unshareArgs` has run. The law of exclusivity makes the places of one call's `inout` arguments
apart (modes.overlapping-inout), so the callee's homes don't overlap, and the callee's state
agrees with the frame of copies that copy-in, copy-out gives it.
-/

namespace Stilt.Sharing

open InPlace (Ref Passed.Compat copyEnterStep copy_enter_eq)

/-! ## Places apart -/

theorem not_prefix_of_disjoint : ∀ {p q : Path}, p.Disjoint q → ¬ p <+: q
  | [], _, h => by simp [Path.Disjoint] at h
  | _ :: _, [], h => by simp [Path.Disjoint] at h
  | s :: p, t :: q, h => by
    rw [List.cons_prefix_cons]
    rintro ⟨rfl, hp⟩
    rcases h with h | h
    · exact h rfl
    · exact not_prefix_of_disjoint h hp

/-- Two disjoint paths below one part reach parts that don't overlap. -/
theorem overlaps_disjoint {r : Ref} {p q : Path} (h : p.Disjoint q) :
    overlaps (r.at p) (r.at q) = false := by
  have hn : ∀ {a b : Path}, a.Disjoint b → (r.path ++ a).isPrefixOf (r.path ++ b) = false :=
    fun hd => Bool.eq_false_iff.2 fun h' => not_prefix_of_disjoint hd
      ((List.prefix_append_right_inj _).1 (List.isPrefixOf_iff_prefix.1 h'))
  simp only [overlaps, InPlace.Ref.at, beq_self_eq_true, Bool.true_and, Bool.or_eq_false_iff]
  exact ⟨hn h, hn (Path.Disjoint.symm h)⟩

/-- Parts below two parts that don't overlap don't overlap. -/
theorem overlaps_at_both {a b : Ref} (h : overlaps a b = false) (p q : Path) :
    overlaps (a.at p) (b.at q) = false := by
  have h₁ := overlaps_at h p
  rw [overlaps_comm] at h₁ ⊢
  exact overlaps_at h₁ q

/-! ## The steps of the start of a call -/

/-- The binding an `inout` parameter gets when every binding is shared: its argument's place
`p` below the part `e` refers to, and no other. -/
def inoutEntry (e : Entry) (p : Path) : Entry := ⟨⟨e.ref.loc, e.ref.path ++ p⟩, none, false, true, true⟩

/-- One step of `Sharing.enter`: binding one parameter. -/
def enterStep (shared : Name → Bool) (caller s₀ : State) : Name × Passed → Except Fault State
  | (y, .value v) | (y, .moved _ v) => pure (bind s₀ y v)
  | (y, .place x path) =>
    match caller.env.lookup x with
    | some e => (fun _ => { s₀ with env := (y, ⟨⟨e.ref.loc, e.ref.path ++ path⟩, none, !shared y,
        true, true⟩) :: s₀.env }) <$> deref caller e.ref path
    | none => .error .stuck

theorem enter_eq (shared : Name → Bool) (caller : State) (captured : List (Name × Value))
    (bound : List (Name × Passed)) :
    (frames shared).enter caller captured bound = bound.foldlM (enterStep shared caller)
      (captured.foldr (fun xv t => bind t xv.1 xv.2) ⟨[], caller.store⟩) := by
  show Sharing.enter shared caller captured bound = _
  unfold Sharing.enter
  dsimp only
  congr 1
  all_goals first
    | rfl
    | (funext s₀ ya
       obtain ⟨y, a⟩ := ya
       cases a <;> rfl)

/-! ## What the start of a call gives -/

/-- What the start of a call gives, once the parameters `pre` are bound: the frame and the
callee's state agree with every binding shared, the callee's store extends the caller's, each
binding has a new home, or is an `inout` parameter whose home is its argument's place below a
root that refers to its home, and each `inout` parameter's name finds that binding. -/
structure Entered (s : State) (pre : List (Name × Passed)) (frc : Copy.Frame) (sc : State) :
    Prop where
  agrees : AgreesAll frc sc
  shared : AllShared sc
  grows : Grows s.store sc.store
  refs : ∀ ye ∈ sc.env, (s.store.size ≤ ye.2.home.loc ∧ ye.2.alias = none) ∨
    ∃ y x p e, (y, Passed.place x p) ∈ pre ∧ s.env.lookup x = some e ∧ e.alias = none ∧
      ye.2 = inoutEntry e p
  places : ∀ y x p, (y, Passed.place x p) ∈ pre →
    ∃ e, s.env.lookup x = some e ∧ sc.env.lookup y = some (inoutEntry e p) ∧
      ∃ u, deref s e.ref p = .ok u

theorem entered_base (s : State) :
    ∀ {captured : List (Name × Value)}, (∀ xv ∈ captured, xv.2.Safe) →
      Entered s [] captured (captured.foldr (fun xv t => bind t xv.1 xv.2) ⟨[], s.store⟩)
  | [], _ => ⟨⟨rfl, rfl, trivial, by simp, .nil, by simp⟩, ⟨by simp, by simp, by simp⟩,
      Grows.refl _, by simp, by simp⟩
  | (x, v) :: captured, h => by
    have ih := entered_base s fun xv hxv => h xv (List.mem_cons_of_mem _ hxv)
    refine ⟨ih.agrees.bindWith x (h (x, v) List.mem_cons_self) false false,
      ih.shared.cons rfl rfl rfl rfl, ih.grows.trans (Grows.push _ _), ?_, by simp⟩
    intro ye hye
    rcases List.mem_cons.1 hye with rfl | hye
    · exact .inl ⟨ih.grows.size, rfl⟩
    · exact ih.refs ye hye

namespace Entered

variable {s : State} {pre : List (Name × Passed)} {fr₀ : Copy.Frame} {s₀ : State}

theorem lookup_keep {y : Name} (hy : y ∉ pre.map Prod.fst) {e e' : Entry} {y' x : Name}
    {p : Path} (hmem : (y', Passed.place x p) ∈ pre) (hl : s₀.env.lookup y' = some e) :
    List.lookup y' ((y, e') :: s₀.env) = some e := by
  have hne : y' ≠ y := fun he => hy (List.mem_map.2 ⟨_, hmem, he⟩)
  rw [lookup_cons_ne hne, hl]

/-- Binding a parameter that takes a value. -/
theorem value (h : Entered s pre fr₀ s₀) {y : Name} (hy : y ∉ pre.map Prod.fst) {a : Passed}
    {v : Value} (ha : a.value? = some v) (hv : v.Safe) :
    Entered s (pre ++ [(y, a)]) ((y, v) :: fr₀) (bind s₀ y v) := by
  refine ⟨h.agrees.bindWith y hv false false, h.shared.cons rfl rfl rfl rfl,
    h.grows.trans (Grows.push _ _), ?_, ?_⟩
  · intro ye hye
    rcases List.mem_cons.1 hye with rfl | hye
    · exact .inl ⟨h.grows.size, rfl⟩
    · rcases h.refs ye hye with hfresh | ⟨y', x, p, e, hmem, hl, ha', heq⟩
      · exact .inl hfresh
      · exact .inr ⟨y', x, p, e, List.mem_append_left _ hmem, hl, ha', heq⟩
  · intro y' x p hmem
    rcases List.mem_append.1 hmem with hmem | hmem
    · obtain ⟨e, hl, hly, hu⟩ := h.places y' x p hmem
      exact ⟨e, hl, lookup_keep hy hmem hly, hu⟩
    · simp only [List.mem_singleton, Prod.mk.injEq] at hmem
      obtain ⟨-, rfl⟩ := hmem
      cases ha

/-- The home of an `inout` parameter's binding, below its root's home, doesn't overlap the home of
a binding that the start of the call made before it. -/
theorem home_apart {fr : Copy.Frame} (h : Entered s pre fr₀ s₀) (hs : AgreesAll fr s) {x : Name}
    {p : Path}
    (hc : ∀ y' x' p', (y', Passed.place x' p') ∈ pre → Passed.Compat (.place x' p') (.place x p))
    {e : Entry} (hl : s.env.lookup x = some e) (hae : e.alias = none) :
    ∀ b ∈ s₀.env, overlaps (inoutEntry e p).home b.2.home = false := by
  intro b hb
  have hlt : e.ref.loc < s.store.size := (hs.has (x, e) (mem_of_lookup hl)).2
  rcases h.refs b hb with ⟨hle, -⟩ | ⟨y', x', p', e', hmem, hl', hae', heq⟩
  · rw [overlaps_comm]
    exact overlaps_fresh (Nat.lt_of_lt_of_le hlt hle)
  · rw [heq]
    show overlaps (e.ref.at p) (e'.ref.at p') = false
    by_cases hx : x' = x
    · subst hx
      rw [hl] at hl'
      cases hl'
      rcases hc y' x' p' hmem with hne | hd
      · exact absurd rfl hne
      · exact overlaps_disjoint (Path.Disjoint.symm hd)
    · have hr : e.ref = e.home := by simp [Entry.ref, hae]
      have hr' : e'.ref = e'.home := by simp [Entry.ref, hae']
      rw [hr, hr']
      refine overlaps_at_both (homes_apart_of_mem hs.homes (mem_of_lookup hl)
        (mem_of_lookup hl') fun he => hx ?_) p p'
      exact (congrArg Prod.fst he).symm

/-- Binding an `inout` parameter to its argument's place, below a root that refers to its
home. -/
theorem place {fr : Copy.Frame} (h : Entered s pre fr₀ s₀) (hs : AgreesAll fr s)
    {shared : Name → Bool} (hsh : ∀ y, shared y = true) {y x : Name} {p : Path}
    (hy : y ∉ pre.map Prod.fst)
    (hc : ∀ y' x' p', (y', Passed.place x' p') ∈ pre → Passed.Compat (.place x' p') (.place x p))
    {e : Entry} (hl : s.env.lookup x = some e) (hae : e.alias = none) {u : Value}
    (hu : deref s e.ref p = .ok u) (hsafe : u.Safe) :
    Entered s (pre ++ [(y, .place x p)]) ((y, u) :: fr₀)
      { s₀ with env := (y, ⟨⟨e.ref.loc, e.ref.path ++ p⟩, none, !shared y, true, true⟩) ::
        s₀.env } := by
  have hent : (⟨⟨e.ref.loc, e.ref.path ++ p⟩, none, !shared y, true, true⟩ : Entry) =
      inoutEntry e p := by
    simp [inoutEntry, hsh y]
  rw [hent]
  have hlt : e.ref.loc < s.store.size := (hs.has (x, e) (mem_of_lookup hl)).2
  have hlt₀ : e.ref.loc < s₀.store.size := Nat.lt_of_lt_of_le hlt h.grows.size
  have hd : deref ⟨[], s₀.store⟩ (inoutEntry e p).ref [] = .ok u := by
    rw [← deref_grows (s := s) h.grows hlt p] at hu
    simpa [inoutEntry, Entry.ref, deref] using hu
  refine ⟨⟨by simp [h.agrees.len], by simp [h.agrees.align], ?_, fun ye hye => ?_,
      .cons (h.home_apart hs hc hl hae) h.agrees.homes, fun xv hxv => ?_⟩,
    ⟨fun ye hye => ?_, fun ye hye => ?_, fun ye hye => ?_⟩, h.grows, fun ye hye => ?_,
    fun y' x' p' hmem => ?_⟩
  · rw [Moving.keep_all (by simp) (by simp),
      Moving.keep_all (by simp) (by simpa using h.agrees.len_env)]
    have hh := h.agrees.holds
    rw [Moving.keep_all (by simp) (by simp), Moving.keep_all (by simp) h.agrees.len_env] at hh
    exact ⟨rfl, hd, hh⟩
  · rcases List.mem_cons.1 hye with rfl | hye
    · exact ⟨hlt₀, hlt₀⟩
    · exact h.agrees.has ye hye
  · rcases List.mem_cons.1 hxv with rfl | hxv
    · exact hsafe
    · exact h.agrees.safe xv hxv
  · rcases List.mem_cons.1 hye with rfl | hye
    · rfl
    · exact h.shared.shared ye hye
  · rcases List.mem_cons.1 hye with rfl | hye
    · exact .inr ⟨rfl, rfl⟩
    · exact h.shared.homes ye hye
  · rcases List.mem_cons.1 hye with rfl | hye
    · exact fun _ => rfl
    · exact h.shared.inout ye hye
  · rcases List.mem_cons.1 hye with rfl | hye
    · exact .inr ⟨y, x, p, e, by simp, hl, hae, rfl⟩
    · rcases h.refs ye hye with hfresh | ⟨y', x', p', e', hmem, hl', hae', heq⟩
      · exact .inl hfresh
      · exact .inr ⟨y', x', p', e', List.mem_append_left _ hmem, hl', hae', heq⟩
  · rcases List.mem_append.1 hmem with hmem | hmem
    · obtain ⟨e', hl', hly, hu'⟩ := h.places y' x' p' hmem
      exact ⟨e', hl', lookup_keep hy hmem hly, hu'⟩
    · simp only [List.mem_singleton, Prod.mk.injEq, Passed.place.injEq] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      exact ⟨e, hl, List.lookup_cons_self, u, hu⟩

end Entered

/-- Binding the parameters `rest`, after `pre`, ends alike in both models, when every root of an
`inout` argument refers to its home. -/
theorem enter_fold {fr : Copy.Frame} {s : State} (hs : AgreesAll fr s) {shared : Name → Bool}
    (hsh : ∀ y, shared y = true) :
    ∀ (rest pre : List (Name × Passed)) (fr₀ : Copy.Frame) (s₀ : State), Entered s pre fr₀ s₀ →
      ((pre ++ rest).map Prod.fst).Nodup → ((pre ++ rest).map Prod.snd).Pairwise Passed.Compat →
      InPlace.Sim.PassedSafe (rest.map Prod.snd) →
      (∀ y x p e, (y, Passed.place x p) ∈ rest → s.env.lookup x = some e → e.alias = none) →
      (∃ f, rest.foldlM (copyEnterStep fr) fr₀ = .error f ∧
          rest.foldlM (enterStep shared s) s₀ = .error f) ∨
        ∃ frc sc, rest.foldlM (copyEnterStep fr) fr₀ = .ok frc ∧
          rest.foldlM (enterStep shared s) s₀ = .ok sc ∧ Entered s (pre ++ rest) frc sc
  | [], pre, fr₀, s₀, h, _, _, _, _ => .inr ⟨fr₀, s₀, rfl, rfl, by simpa using h⟩
  | (y, a) :: rest, pre, fr₀, s₀, h, hnd, hc, hsafe, halone => by
    have hy : y ∉ pre.map Prod.fst := by
      intro hmem
      simp only [List.map_append, List.map_cons, List.nodup_append] at hnd
      exact hnd.2.2 y hmem y List.mem_cons_self rfl
    have hassoc : pre ++ (y, a) :: rest = (pre ++ [(y, a)]) ++ rest := by simp
    have hsafe' : InPlace.Sim.PassedSafe (rest.map Prod.snd) :=
      fun q hq => hsafe q (List.mem_cons_of_mem _ hq)
    have halone' : ∀ y x p e, (y, Passed.place x p) ∈ rest → s.env.lookup x = some e →
        e.alias = none := fun y x p e hm => halone y x p e (List.mem_cons_of_mem _ hm)
    cases a with
    | value v =>
      have hv : v.Safe := hsafe _ List.mem_cons_self v rfl
      rw [hassoc] at hnd hc ⊢
      exact enter_fold hs hsh rest _ _ _ (h.value hy rfl hv) hnd hc hsafe' halone'
    | moved x v =>
      have hv : v.Safe := hsafe _ List.mem_cons_self v rfl
      rw [hassoc] at hnd hc ⊢
      exact enter_fold hs hsh rest _ _ _ (h.value hy rfl hv) hnd hc hsafe' halone'
    | place x p =>
      have hcp : ∀ y' x' p', (y', Passed.place x' p') ∈ pre →
          Passed.Compat (.place x' p') (.place x p) := fun y' x' p' hmem => by
        simp only [List.map_append, List.map_cons, List.pairwise_append] at hc
        exact hc.2.2 _ (List.mem_map.2 ⟨_, hmem, rfl⟩) _ List.mem_cons_self
      have hread := hs.read x p
      simp only [List.foldlM_cons, copyEnterStep, enterStep]
      cases hl : s.env.lookup x with
      | none =>
        simp only [Sharing.read, hl] at hread
        simp only [hread]
        exact .inl ⟨.stuck, rfl, rfl⟩
      | some e =>
        simp only [Sharing.read, hl] at hread
        simp only [hread]
        cases hu : deref s e.ref p with
        | error f => exact .inl ⟨f, rfl, rfl⟩
        | ok u =>
          have hsu : u.Safe := hs.read_safe (hread.trans hu)
          have hae := halone y x p e List.mem_cons_self hl
          rw [hassoc] at hnd hc ⊢
          exact enter_fold hs hsh rest _ _ _ (h.place hs hsh hy hcp hl hae hu hsu) hnd hc hsafe'
            halone'

/-- Both models start a call alike when every binding is shared and every root of an `inout`
argument refers to its home. -/
theorem AgreesAll.enter {fr : Copy.Frame} {s : State} (hs : AgreesAll fr s)
    {shared : Name → Bool} (hsh : ∀ y, shared y = true)
    {captured : List (Name × Value)} (hc : ∀ xv ∈ captured, xv.2.Safe)
    {bound : List (Name × Passed)} (hnd : (bound.map Prod.fst).Nodup)
    (hcompat : (bound.map Prod.snd).Pairwise Passed.Compat)
    (hsafe : InPlace.Sim.PassedSafe (bound.map Prod.snd))
    (halone : ∀ y x p e, (y, Passed.place x p) ∈ bound → s.env.lookup x = some e →
      e.alias = none) :
    (∃ f, Copy.frames.enter fr captured bound = .error f ∧
        (frames shared).enter s captured bound = .error f) ∨
      ∃ frc sc, Copy.frames.enter fr captured bound = .ok frc ∧
        (frames shared).enter s captured bound = .ok sc ∧ Entered s bound frc sc := by
  rw [copy_enter_eq, enter_eq]
  exact enter_fold hs hsh bound [] _ _ (entered_base s hc) (by simpa using hnd)
    (by simpa using hcompat) hsafe halone

end Stilt.Sharing
