import Stilt.InPlace.Enter

/-!
# Leaving a call

What the two models do when a call ends (values.inout-arguments and values.inout-argument-order). Copy-in,
copy-out writes each `inout` parameter's final value back to its argument's
place, from left to right. In place, the callee wrote those places as it
went, and nothing is written back.

The callee's state evolved only by writes below its references (`Evolves`):
below the places of its `inout` arguments, or in its own new locations. The
places don't overlap, so by `Value.setSeq_canon` the caller's part of the
store is the one that writing each place its final value gives, which is what
copy-in, copy-out does.
-/

namespace Stilt.InPlace

/-- One step of `Copy.leave`: writing back one parameter. -/
def copyLeaveStep (callee fr₁ : Copy.Frame) : Name × Passed → Except Fault Copy.Frame
  | (_, .value _) | (_, .moved _ _) => pure fr₁
  | (y, .place x path) => (Copy.read callee y []).bind fun v => Copy.write fr₁ x path v

theorem copy_leave_eq (caller callee : Copy.Frame) (bound : List (Name × Passed)) :
    Copy.frames.leave caller callee bound = bound.foldlM (copyLeaveStep callee) caller := by
  show Copy.leave caller callee bound = _
  unfold Copy.leave
  congr 1
  funext fr₁ ya
  obtain ⟨y, a⟩ := ya
  cases a <;> rfl

/-- The path in the store of the place an `inout` argument names. -/
def placePath (s : State) : Name × Passed → Option Path
  | (_, .place x p) => (s.env.lookup x).map fun r => (placeRef r p).toPath
  | (_, .value _) | (_, .moved _ _) => none

theorem mem_placePaths {s : State} {bound : List (Name × Passed)} {P : Path}
    (hP : P ∈ bound.filterMap (placePath s)) :
    ∃ y x p r, (y, Passed.place x p) ∈ bound ∧ s.env.lookup x = some r ∧
      P = (placeRef r p).toPath := by
  obtain ⟨⟨y, a⟩, hmem, ha⟩ := List.mem_filterMap.1 hP
  cases a with
  | value _ | moved _ _ => cases ha
  | place x p =>
    simp only [placePath, Option.map_eq_some_iff] at ha
    obtain ⟨r, hl, rfl⟩ := ha
    exact ⟨y, x, p, r, hmem, hl, rfl⟩

theorem placePaths_disjoint {s : State} (hp : s.env.Pairwise fun a b => a.2.Disjoint b.2)
    {bound : List (Name × Passed)} (hc : (bound.map Prod.snd).Pairwise Passed.Compat) :
    (bound.filterMap (placePath s)).Pairwise Path.Disjoint := by
  rw [List.pairwise_filterMap]
  rw [List.pairwise_map] at hc
  refine hc.imp fun {ya yb} hab P hP Q hQ => ?_
  obtain ⟨y, a⟩ := ya
  obtain ⟨y', b⟩ := yb
  cases a with
  | value _ | moved _ _ => cases hP
  | place x p =>
    cases b with
    | value _ | moved _ _ => cases hQ
    | place x' p' =>
      simp only [placePath, Option.map_eq_some_iff] at hP hQ
      obtain ⟨r, hl, rfl⟩ := hP
      obtain ⟨r', hl', rfl⟩ := hQ
      exact placeRef_disjoint hp hl hl' hab

theorem get_append_low {A B : List Value} {r : Ref} (h : r.loc < A.length) (p : Path) :
    (Value.list (A ++ B)).get (r.toPath ++ p) = (Value.list A).get (r.toPath ++ p) := by
  simp [Ref.toPath, Value.get, elemAt?, List.getElem?_append_left h]

/-- Writing back the parameters `rest`, whose places' final parts are in
`A'`, ends with a frame that agrees with `A'`. -/
theorem leave_fold {s : State} {bound : List (Name × Passed)} {fr' : Copy.Frame} {A' : List Value}
    (hread : ∀ y x p, (y, Passed.place x p) ∈ bound → ∃ r, s.env.lookup x = some r ∧
      Copy.read fr' y [] = (Value.list A').get (placeRef r p).toPath)
    (hsafe : ∀ y x p v, (y, Passed.place x p) ∈ bound → Copy.read fr' y [] = .ok v → v.Safe) :
    ∀ (rest : List (Name × Passed)), (∀ ya ∈ rest, ya ∈ bound) →
      ∀ (fr₁ : Copy.Frame) (st₁ : List Value) (L : List (Path × Value)),
        Agrees fr₁ ⟨s.env, st₁⟩ → L.map Prod.fst = rest.filterMap (placePath s) →
        (∀ pw ∈ L, (Value.list A').get pw.1 = .ok pw.2) →
        (Value.list st₁).setSeq L = .ok (.list A') →
        ∃ fr₂, rest.foldlM (copyLeaveStep fr') fr₁ = .ok fr₂ ∧ Agrees fr₂ ⟨s.env, A'⟩
  | [], _, fr₁, st₁, L, hag, hL, _, hseq => by
    have : L = [] := by simpa using hL
    subst this
    simp only [Value.setSeq, Except.ok.injEq, Value.list.injEq] at hseq
    subst hseq
    exact ⟨fr₁, rfl, hag⟩
  | (y, .value v) :: rest, hsub, fr₁, st₁, L, hag, hL, hget, hseq => by
    simp only [List.filterMap_cons, placePath] at hL
    exact leave_fold hread hsafe rest (fun ya h => hsub ya (List.mem_cons_of_mem _ h))
      fr₁ st₁ L hag hL hget hseq
  | (y, .moved x v) :: rest, hsub, fr₁, st₁, L, hag, hL, hget, hseq => by
    simp only [List.filterMap_cons, placePath] at hL
    exact leave_fold hread hsafe rest (fun ya h => hsub ya (List.mem_cons_of_mem _ h))
      fr₁ st₁ L hag hL hget hseq
  | (y, .place x p) :: rest, hsub, fr₁, st₁, L, hag, hL, hget, hseq => by
    obtain ⟨r, hl, hrd⟩ := hread y x p (hsub _ List.mem_cons_self)
    simp only [List.filterMap_cons, placePath, hl, Option.map_some] at hL
    cases L with
    | nil => simp at hL
    | cons pw L' =>
      obtain ⟨P, v⟩ := pw
      simp only [List.map_cons, List.cons.injEq] at hL
      obtain ⟨rfl, hL'⟩ := hL
      have hv : (Value.list A').get (placeRef r p).toPath = .ok v := hget _ List.mem_cons_self
      have hsv : v.Safe := hsafe y x p v (hsub _ List.mem_cons_self) (hrd.trans hv)
      have hlt : r.loc < st₁.length := hag.valid (x, r) (mem_of_lookup hl)
      obtain ⟨u, hu⟩ : ∃ u, st₁[r.loc]? = some u := ⟨_, List.getElem?_eq_getElem hlt⟩
      simp only [Value.setSeq] at hseq
      rw [show (placeRef r p).toPath = r.toPath ++ p from rfl, set_whole hu] at hseq
      cases hu' : u.set (r.path ++ p) v with
      | error f => simp [hu', Functor.map, Except.map, Except.bind] at hseq
      | ok u' =>
        simp only [hu', Functor.map, Except.map, Except.bind] at hseq
        have hiw : InPlace.write ⟨s.env, st₁⟩ x p v = .ok ⟨s.env, st₁.set r.loc u'⟩ := by
          simp [InPlace.write, hl, hu, hu', Functor.map, Except.map]
        rcases hag.write hsv x p with ⟨f, -, h₂⟩ | ⟨fr₂, s₂, h₁, h₂, hag₂, -⟩
        · rw [hiw] at h₂
          cases h₂
        · rw [hiw] at h₂
          cases h₂
          obtain ⟨fr₃, hfold, hag₃⟩ := leave_fold hread hsafe rest
            (fun ya h => hsub ya (List.mem_cons_of_mem _ h)) fr₂ _ L' hag₂ hL'
            (fun pw hpw => hget pw (List.mem_cons_of_mem _ hpw)) hseq
          refine ⟨fr₃, ?_, hag₃⟩
          simp only [List.foldlM_cons, copyLeaveStep, hrd, hv, Except.bind, h₁]
          exact hfold

end Stilt.InPlace
