import Stilt.Sharing.Enter
import Stilt.InPlace.Leave

/-!
# Leaving a call with sharing

When a call ends, copy-in, copy-out writes each `inout` parameter's final value back to its
argument's place, from left to right (values.inout-arguments). Sharing wrote those places in the
caller's store all along, and nothing else of the caller's: the callee writes only below its
homes, which are new locations or the places of its `inout` arguments. So the caller's state
with the callee's store agrees with the frame that copy-out gives.
-/

namespace Stilt.Sharing

open InPlace (Ref Passed.Compat copyLeaveStep copy_leave_eq below)

/-! ## The store as a list -/

/-- A store that grows another holds it first. -/
theorem Grows.toList_append {a b : Array Value} (h : Grows a b) :
    b.toList = a.toList ++ b.toList.drop a.size := by
  apply List.ext_getElem?
  intro i
  rcases Nat.lt_or_ge i a.size with hi | hi
  · rw [List.getElem?_append_left (by simpa using hi), Array.getElem?_toList,
      Array.getElem?_toList, h.same i hi]
  · rw [List.getElem?_append_right (by simpa using hi), List.getElem?_drop, Array.length_toList,
      Nat.add_sub_cancel' hi]

/-- Two parts that don't overlap are at disjoint paths. -/
theorem disjoint_of_overlaps {a b : Ref} (h : overlaps a b = false) :
    a.toPath.Disjoint b.toPath := by
  simp only [overlaps, Bool.and_eq_false_iff, beq_eq_false_iff_ne, Bool.or_eq_false_iff] at h
  rcases h with h | ⟨h₁, h₂⟩
  · exact .inl fun he => h (Int.ofNat_inj.1 (by simpa using he))
  · refine .inr ?_
    have hp : ¬ a.path <+: b.path := fun hp => by simp [List.isPrefixOf_iff_prefix.2 hp] at h₁
    have hq : ¬ b.path <+: a.path := fun hq => by simp [List.isPrefixOf_iff_prefix.2 hq] at h₂
    exact disjoint_of_not_prefix hp hq
where
  disjoint_of_not_prefix : ∀ {p q : Path}, ¬ p <+: q → ¬ q <+: p → p.Disjoint q
    | [], _, hp, _ => absurd (List.nil_prefix) hp
    | _ :: _, [], _, hq => absurd (List.nil_prefix) hq
    | s :: p, t :: q, hp, hq => by
      by_cases hst : s = t
      · subst hst
        refine .inr (disjoint_of_not_prefix (fun h => hp ?_) (fun h => hq ?_))
        · exact (List.cons_prefix_cons).2 ⟨rfl, h⟩
        · exact (List.cons_prefix_cons).2 ⟨rfl, h⟩
      · exact .inl hst

/-! ## The places of a call's `inout` arguments -/

/-- The path in the store of the place an `inout` argument names. -/
def placePath (s : State) : Name × Passed → Option Path
  | (_, .place x p) => (s.env.lookup x).map fun e => (e.ref.at p).toPath
  | (_, .value _) | (_, .moved _ _) => none

theorem mem_placePaths {s : State} {bound : List (Name × Passed)} {P : Path}
    (hP : P ∈ bound.filterMap (placePath s)) :
    ∃ y x p e, (y, Passed.place x p) ∈ bound ∧ s.env.lookup x = some e ∧
      P = (e.ref.at p).toPath := by
  obtain ⟨⟨y, a⟩, hmem, ha⟩ := List.mem_filterMap.1 hP
  cases a with
  | value _ | moved _ _ => cases ha
  | place x p =>
    simp only [placePath, Option.map_eq_some_iff] at ha
    obtain ⟨e, hl, rfl⟩ := ha
    exact ⟨y, x, p, e, hmem, hl, rfl⟩

/-- The places of one call's `inout` arguments are disjoint when their roots refer to their
homes, which don't overlap. -/
theorem placePaths_disjoint {s : State}
    (hp : s.env.Pairwise fun a b => overlaps a.2.home b.2.home = false)
    {bound : List (Name × Passed)} (hc : (bound.map Prod.snd).Pairwise Passed.Compat)
    (halone : ∀ y x p e, (y, Passed.place x p) ∈ bound → s.env.lookup x = some e →
      e.alias = none) :
    (bound.filterMap (placePath s)).Pairwise Path.Disjoint := by
  rw [List.pairwise_filterMap]
  rw [List.pairwise_map] at hc
  have hsub : ∀ ya ∈ bound, ya ∈ bound := fun _ h => h
  refine List.Pairwise.imp_of_mem ?_ hc
  intro ya yb hya hyb hab P hP Q hQ
  obtain ⟨y, a⟩ := ya
  obtain ⟨y', b⟩ := yb
  cases a with
  | value _ | moved _ _ => cases hP
  | place x p =>
    cases b with
    | value _ | moved _ _ => cases hQ
    | place x' p' =>
      simp only [placePath, Option.map_eq_some_iff] at hP hQ
      obtain ⟨e, hl, rfl⟩ := hP
      obtain ⟨e', hl', rfl⟩ := hQ
      by_cases hx : x = x'
      · subst hx
        rw [hl] at hl'
        cases hl'
        rcases hab with hne | hd
        · exact absurd rfl hne
        · exact Path.Disjoint.prefix e.ref.toPath hd
      · have hr : e.ref = e.home := by simp [Entry.ref, halone y x p e hya hl]
        have hr' : e'.ref = e'.home := by simp [Entry.ref, halone y' x' p' e' hyb hl']
        have hd := disjoint_of_overlaps (homes_apart_of_mem hp (mem_of_lookup hl)
          (mem_of_lookup hl') fun he => hx (congrArg Prod.fst he))
        rw [← hr, ← hr'] at hd
        exact Path.Disjoint.append hd p p'

/-! ## Writing back -/

theorem AllShared.store {s : State} (h : AllShared s) (st : Array Value) :
    AllShared ⟨s.env, st⟩ :=
  ⟨h.shared, h.homes, h.inout⟩

/-- One write of copy-out, `w` along `p` below `x`, whose binding refers to its home, which no
other binding overlaps: both models write it, the frame and the state still agreeing, and the
state's store, as a list, written along the place's path. -/
theorem write_back {s : State} (hsh : AllShared s) {fr₁ : Copy.Frame} {st₁ : Array Value}
    (hag : AgreesAll fr₁ ⟨s.env, st₁⟩) {x : Name} {e : Entry} (hl : s.env.lookup x = some e)
    (ha : e.alias = none) (hov : ∀ ye ∈ s.env, ye.2 ≠ e → overlaps e.home ye.2.ref = false)
    {p : Path} {w : Value} (hw : w.Safe) {R : Value}
    (hset : (Value.list st₁.toList).set (e.ref.at p).toPath w = .ok R) :
    ∃ fr₂ st₂, Copy.write fr₁ x p w = .ok fr₂ ∧ R = Value.list st₂.toList ∧
      AgreesAll fr₂ ⟨s.env, st₂⟩ := by
  have hlt : e.ref.loc < st₁.size := (hag.has (x, e) (mem_of_lookup hl)).2
  have hu : st₁.toList[e.ref.loc]? = some st₁[e.ref.loc] := by
    rw [Array.getElem?_toList]
    exact Array.getElem?_eq_getElem hlt
  rw [show (e.ref.at p).toPath = e.ref.toPath ++ p by simp [InPlace.Ref.at, InPlace.Ref.toPath],
    InPlace.set_whole hu p w] at hset
  cases hu' : st₁[e.ref.loc].set (e.ref.path ++ p) w with
  | error f => simp [hu', Functor.map, Except.map] at hset
  | ok u' =>
    simp only [hu', Functor.map, Except.map, Except.ok.injEq] at hset
    rcases hag.holds_all.lookup x with ⟨h₁, h₂⟩ | ⟨vx, e', h₁, h₂, hd⟩
    · rw [hl] at h₂
      cases h₂
    · rw [hl, Option.some.injEq] at h₂
      subst h₂
      have hd' : deref ⟨s.env, st₁⟩ e.ref [] = .ok vx := hd
      have hg : st₁[e.ref.loc].get e.ref.path = .ok vx := by
        simpa [deref, Array.getElem?_eq_getElem hlt] using hd'
      have hu₀ := hu'
      rw [Value.set_append, hg] at hu'
      cases hv : vx.set p w with
      | error f => simp [hv, Except.bind] at hu'
      | ok v' =>
        have hs : setAt ⟨s.env, st₁⟩ e.ref p w = .ok ⟨s.env, st₁.set! e.ref.loc u'⟩ := by
          simp only [setAt, Array.getElem?_eq_getElem hlt, hu₀]
          rfl
        obtain ⟨hA, -, -⟩ := hag.write_home (hsh.store st₁) hw h₁ hl hd' hv hov ha hs
        refine ⟨assocSet fr₁ x v', st₁.set! e.ref.loc u', ?_, ?_, hA⟩
        · simp [Copy.write, h₁, hv]
          rfl
        · rw [← hset]
          simp

/-- Writing back the parameters `rest`, whose places' final parts are in `A'`, ends with a frame
that agrees with `A'`. -/
theorem leave_fold {s : State} (hsh : AllShared s) {bound : List (Name × Passed)}
    {fr' : Copy.Frame} {A' : List Value}
    (hread : ∀ y x p, (y, Passed.place x p) ∈ bound → ∃ e, s.env.lookup x = some e ∧
      e.alias = none ∧ (∀ ye ∈ s.env, ye.2 ≠ e → overlaps e.home ye.2.ref = false) ∧
      Copy.read fr' y [] = (Value.list A').get (e.ref.at p).toPath)
    (hsafe : ∀ y x p v, (y, Passed.place x p) ∈ bound → Copy.read fr' y [] = .ok v → v.Safe) :
    ∀ (rest : List (Name × Passed)), (∀ ya ∈ rest, ya ∈ bound) →
      ∀ (fr₁ : Copy.Frame) (st₁ : Array Value) (L : List (Path × Value)),
        AgreesAll fr₁ ⟨s.env, st₁⟩ → L.map Prod.fst = rest.filterMap (placePath s) →
        (∀ pw ∈ L, (Value.list A').get pw.1 = .ok pw.2) →
        (Value.list st₁.toList).setSeq L = .ok (.list A') →
        ∃ fr₂, rest.foldlM (copyLeaveStep fr') fr₁ = .ok fr₂ ∧ AgreesAll fr₂ ⟨s.env, A'.toArray⟩
  | [], _, fr₁, st₁, L, hag, hL, _, hseq => by
    have : L = [] := by simpa using hL
    subst this
    simp only [Value.setSeq, Except.ok.injEq, Value.list.injEq] at hseq
    subst hseq
    exact ⟨fr₁, rfl, hag⟩
  | (y, .value v) :: rest, hsub, fr₁, st₁, L, hag, hL, hget, hseq => by
    simp only [List.filterMap_cons, placePath] at hL
    exact leave_fold hsh hread hsafe rest (fun ya h => hsub ya (List.mem_cons_of_mem _ h))
      fr₁ st₁ L hag hL hget hseq
  | (y, .moved x v) :: rest, hsub, fr₁, st₁, L, hag, hL, hget, hseq => by
    simp only [List.filterMap_cons, placePath] at hL
    exact leave_fold hsh hread hsafe rest (fun ya h => hsub ya (List.mem_cons_of_mem _ h))
      fr₁ st₁ L hag hL hget hseq
  | (y, .place x p) :: rest, hsub, fr₁, st₁, L, hag, hL, hget, hseq => by
    obtain ⟨e, hl, ha, hov, hrd⟩ := hread y x p (hsub _ List.mem_cons_self)
    simp only [List.filterMap_cons, placePath, hl, Option.map_some] at hL
    cases L with
    | nil => simp at hL
    | cons pw L' =>
      obtain ⟨P, v⟩ := pw
      simp only [List.map_cons, List.cons.injEq] at hL
      obtain ⟨rfl, hL'⟩ := hL
      have hv : (Value.list A').get (e.ref.at p).toPath = .ok v := hget _ List.mem_cons_self
      have hsv : v.Safe := hsafe y x p v (hsub _ List.mem_cons_self) (hrd.trans hv)
      simp only [Value.setSeq] at hseq
      cases hset : (Value.list st₁.toList).set (e.ref.at p).toPath v with
      | error f => simp [hset, Except.bind] at hseq
      | ok R =>
        simp only [hset, Except.bind] at hseq
        obtain ⟨fr₂, st₂, hw, rfl, hag₂⟩ := write_back hsh hag hl ha hov hsv hset
        obtain ⟨fr₃, hfold, hag₃⟩ := leave_fold hsh hread hsafe rest
          (fun ya h => hsub ya (List.mem_cons_of_mem _ h)) fr₂ st₂ L' hag₂ hL'
          (fun pw hpw => hget pw (List.mem_cons_of_mem _ hpw)) hseq
        refine ⟨fr₃, ?_, hag₃⟩
        simp only [List.foldlM_cons, copyLeaveStep, hrd, hv, Except.bind, hw]
        exact hfold

/-- A store whose list starts with another's grows it. -/
theorem Grows.of_toList {a b : Array Value} {F : List Value} (h : b.toList = a.toList ++ F) :
    Grows a b := by
  refine ⟨?_, fun i hi => ?_⟩
  · have hl := congrArg List.length h
    simp only [Array.length_toList, List.length_append] at hl
    omega
  · rw [← Array.getElem?_toList, h, List.getElem?_append_left (by simpa using hi),
      Array.getElem?_toList]

/-- The frame agreeing with the state keeps agreeing once the store grows. -/
theorem AgreesAll.grow {fr : Copy.Frame} {s : State} (h : AgreesAll fr s) {st : Array Value}
    (hg : Grows s.store st) : AgreesAll fr ⟨s.env, st⟩ :=
  AgreesAll.of_alike h (ReadsAlike.grows hg fun ye hye => (h.has ye hye).2)
    (fun ye hye => ⟨State.Has.grows hg (h.has ye hye).1, State.Has.grows hg (h.has ye hye).2⟩)
    h.homes

/-- The path of an `inout` parameter's binding is its argument's place. -/
theorem inoutEntry_path (e : Entry) (p : Path) :
    (inoutEntry e p).ref.toPath = (e.ref.at p).toPath := by
  simp [inoutEntry, Entry.ref, InPlace.Ref.at]

/-- What the callee leaves at each `inout` parameter's place, which is what the copy frame's
parameter holds, read in the store the callee leaves, below the caller's store. -/
theorem leave_read {s sc s' : State} {bound : List (Name × Passed)} {frc fr' : Copy.Frame}
    (hent : Entered s bound frc sc) (hag : AgreesAll fr' s') (hK : Kept sc s')
    {A' rest : List Value} (hst : s'.store.toList = A' ++ rest)
    (hlen : A'.length = s.store.size) {y x : Name} {p : Path}
    (hmem : (y, Passed.place x p) ∈ bound) :
    ∃ e, s.env.lookup x = some e ∧ Copy.read fr' y [] = (Value.list A').get (e.ref.at p).toPath := by
  obtain ⟨e, hl, hly, u, hu⟩ := hent.places y x p hmem
  have hly' := KeptEntries.lookup hK hly rfl
  have hlt : e.ref.loc < A'.length := by
    rw [hlen]
    exact has_of_deref hu
  refine ⟨e, hl, ?_⟩
  rw [hag.read y [], Sharing.read, hly']
  dsimp only
  rw [deref_toList s' (by
    show (inoutEntry e p).ref.loc < s'.store.size
    have hloc : (inoutEntry e p).ref.loc = e.ref.loc := by simp [inoutEntry, Entry.ref]
    rw [← Array.length_toList, hst, List.length_append, hloc]
    omega) [], List.append_nil, hst, inoutEntry_path]
  simp only [InPlace.Ref.at, InPlace.Ref.toPath, Value.get, elemAt?]
  rw [List.getElem?_append_left (by simpa using hlt)]

/-- The writes of a callee at the caller's locations are below the places of its `inout`
arguments, since every other binding of its start has a new home. -/
theorem under_places {s sc : State} {bound : List (Name × Passed)} {frc : Copy.Frame}
    (hent : Entered s bound frc sc) {P : Path} {w : Value} (hP : P.Under sc.paths)
    (hb : below s.store.toList.length (P, w) = true) :
    P.Under (bound.filterMap (placePath s)) := by
  obtain ⟨Q, hQ, q, rfl⟩ := hP
  obtain ⟨ye, hye, hQ⟩ := List.mem_flatMap.1 hQ
  rcases hent.refs ye hye with ⟨hle, ha⟩ | ⟨y, x, p, e, hmem, hl, -, heq⟩
  · have hr : ye.2.ref = ye.2.home := by simp [Entry.ref, ha]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
    rcases hQ with rfl | rfl <;>
    · simp only [below, InPlace.Ref.toPath, List.cons_append, Array.length_toList,
        decide_eq_true_eq, hr] at hb
      omega
  · refine ⟨(e.ref.at p).toPath, List.mem_filterMap.2 ⟨_, hmem, by simp [placePath, hl]⟩, q, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
    rw [heq] at hQ
    rcases hQ with rfl | rfl
    · simp [inoutEntry, InPlace.Ref.at, InPlace.Ref.toPath]
    · rw [inoutEntry_path]

/-- The end of a call: copy-out's write-back gives a frame that agrees with the caller's
bindings over the store the callee left, which follows from the caller's state. -/
theorem leave_agrees {fr : Copy.Frame} {s : State} (hs : AgreesAll fr s) (hsh : AllShared s)
    {bound : List (Name × Passed)} {frc : Copy.Frame} {sc : State}
    (hent : Entered s bound frc sc) (hcompat : (bound.map Prod.snd).Pairwise Passed.Compat)
    (halone : ∀ y x p, (y, Passed.place x p) ∈ bound → Alone s x)
    {fr' : Copy.Frame} {s' : State} (hag : AgreesAll fr' s') (hF : Follows sc s') :
    ∃ fr'', Copy.frames.leave fr fr' bound = .ok fr'' ∧ AgreesAll fr'' ⟨s.env, s'.store⟩ ∧
      Follows s ⟨s.env, s'.store⟩ := by
  obtain ⟨⟨W, st, extra, hs', hW, hseq⟩, -, hK⟩ := hF
  rw [hent.grows.toList_append] at hseq
  obtain ⟨A', B', hR, hlenA, -, hlow, -⟩ := InPlace.setSeq_append_store
    (fun pw hpw => atLoc_of_under (hW pw hpw)) hseq
  simp only [Value.list.injEq] at hR
  subst hR
  have hroots : ∀ y x p e, (y, Passed.place x p) ∈ bound → s.env.lookup x = some e →
      e.alias = none := fun y x p e hmem hl => by
    obtain ⟨e', hl', ha', -⟩ := halone y x p hmem
    rw [hl] at hl'
    cases hl'
    exact ha'
  have hvalid : ∀ P ∈ bound.filterMap (placePath s), ∃ u,
      (Value.list s.store.toList).get P = .ok u := fun P hP => by
    obtain ⟨y, x, p, e, hmem, hl, rfl⟩ := mem_placePaths hP
    obtain ⟨e', hl', -, u, hu⟩ := hent.places y x p hmem
    rw [hl] at hl'
    cases hl'
    refine ⟨u, ?_⟩
    rw [← hu, deref_toList s (has_of_deref hu) p]
    simp [InPlace.Ref.at, InPlace.Ref.toPath]
  obtain ⟨L, hL, hget, hseqL⟩ := Value.setSeq_canon
    (placePaths_disjoint hs.homes hcompat hroots) hvalid
    (fun pw hpw => under_places hent (hW pw (List.mem_filter.1 hpw).1)
      (List.mem_filter.1 hpw).2) hlow
  have hst : s'.store.toList = A' ++ (B' ++ extra) := by rw [hs', List.append_assoc]
  have hlen : A'.length = s.store.size := by rw [hlenA, Array.length_toList]
  have hread : ∀ y x p, (y, Passed.place x p) ∈ bound → ∃ e, s.env.lookup x = some e ∧
      e.alias = none ∧ (∀ ye ∈ s.env, ye.2 ≠ e → overlaps e.home ye.2.ref = false) ∧
      Copy.read fr' y [] = (Value.list A').get (e.ref.at p).toPath := fun y x p hmem => by
    obtain ⟨e, hl, hrd⟩ := leave_read hent hag hK hst hlen hmem
    obtain ⟨e', hl', ha', hap⟩ := halone y x p hmem
    rw [hl] at hl'
    cases hl'
    exact ⟨e, hl, ha', hap, hrd⟩
  obtain ⟨fr'', hfold, hag''⟩ := leave_fold hsh hread
    (fun _ _ _ _ _ hv => hag.read_safe hv) bound (fun _ h => h) fr s.store L hs
    (by rw [hL]) hget hseqL
  have hg : Grows A'.toArray s'.store := Grows.of_toList (by simpa using hst)
  refine ⟨fr'', by rw [copy_leave_eq]; exact hfold, hag''.grow hg, ?_⟩
  refine ⟨⟨L, A', B' ++ extra, hst, fun pw hpw => ?_, hseqL⟩,
    fun P hP _ _ _ _ => ⟨P, hP, [], by rw [List.append_nil]⟩, Kept.same rfl⟩
  have hP : pw.1 ∈ bound.filterMap (placePath s) := hL ▸ List.mem_map_of_mem hpw
  obtain ⟨y, x, p, e, -, hl, hP⟩ := mem_placePaths hP
  refine ⟨e.ref.toPath, List.mem_flatMap.2 ⟨(x, e), mem_of_lookup hl, by simp⟩, p, ?_⟩
  rw [hP]
  simp [InPlace.Ref.at, InPlace.Ref.toPath]

end Stilt.Sharing
