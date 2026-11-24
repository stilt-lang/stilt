import Stilt.Moves.Start
import Stilt.InPlace.Leave

/-!
# The end of a call

When a call ends, the callee has written below the places of its `inout`
arguments, below the storage handed over to it, and in its own locations. The
places and the storage don't overlap, so by `Value.setSeq_canon` the caller's
part of the store is the one that writing each its final part gives, and the
writes may come in any order: first the `inout` places, which is copy-in,
copy-out's write-back (`leave_fold`), then the storage handed over, which
belongs to variables whose last use the call was. Those end, and the writes
below their storage change no live binding (values.passing-values, values.inout-arguments and values.inout-argument-order).
-/

namespace Stilt.Moving

open InPlace

/-- The path in the store of the storage that a last use hands over. -/
def movedPath (s : State) : Name × Passed → Option Path
  | (_, .moved x _) => (s.env.lookup x).map fun r => (placeRef r []).toPath
  | _ => none

theorem filterMap_cons_option {γ δ : Type} (f : γ → Option δ) (a : γ) (l : List γ) :
    (a :: l).filterMap f = (f a).toList ++ l.filterMap f := by
  cases h : f a <;> simp [h]

/-- The places of a call with last uses handed over are its `inout` places
and the storage handed over. -/
theorem perm_paths (s : State) : ∀ bound : List (Name × Passed),
    ((bound.map Moving.handOver).filterMap (placePath s)).Perm
      (bound.filterMap (placePath s) ++ bound.filterMap (movedPath s))
  | [] => .nil
  | (y, q) :: bound => by
    have ih := perm_paths s bound
    simp only [List.map_cons, filterMap_cons_option]
    cases q with
    | value v => simpa [Moving.handOver, placePath, movedPath] using ih
    | place x p =>
      simp only [Moving.handOver, movedPath, Option.toList_none, List.nil_append, List.append_assoc]
      exact ih.append_left _
    | moved x v =>
      simp only [Moving.handOver, placePath, movedPath, Option.toList_none, List.nil_append]
      refine (ih.append_left _).trans ?_
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.perm_append_comm.append_right _

theorem atLoc_placeRef (r : Ref) (p : Path) : AtLoc (placeRef r p).toPath := ⟨r.loc, _, rfl⟩

/-- Splits a sequence of writes at the paths `Ps₁ ++ Ps₂` into the writes at
each. -/
theorem split_writes {L : List (Path × Value)} {Ps₁ Ps₂ : List Path} {st A' : List Value}
    (hL : L.map Prod.fst = Ps₁ ++ Ps₂) (hat : ∀ P ∈ Ps₁, AtLoc P)
    (h : (Value.list st).setSeq L = .ok (.list A')) :
    ∃ L₁ L₂ A₁, L₁.map Prod.fst = Ps₁ ∧ L₂.map Prod.fst = Ps₂ ∧ L = L₁ ++ L₂ ∧
      (Value.list st).setSeq L₁ = .ok (.list A₁) ∧ (Value.list A₁).setSeq L₂ = .ok (.list A') ∧
      A₁.length = st.length := by
  obtain ⟨L₁, L₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.1 hL
  rw [Value.setSeq_append] at h
  cases h₃ : (Value.list st).setSeq L₁ with
  | error e => rw [h₃] at h; cases h
  | ok V =>
    rw [h₃] at h
    obtain ⟨A₁, B, hR, hlen, hB, -, -⟩ := setSeq_append_store (B := [])
      (fun pw hpw => hat _ (h₁ ▸ List.mem_map_of_mem hpw)) (by rw [List.append_nil]; exact h₃)
    have hB' : B = [] := List.eq_nil_of_length_eq_zero hB
    subst hB'
    rw [List.append_nil] at hR
    subst hR
    exact ⟨L₁, L₂, A₁, h₁, h₂, rfl, h₃, h, hlen⟩

/-- Writes at paths disjoint from every reference keep the agreement. -/
theorem Agrees.setSeq_disjoint {fr : Copy.Frame} {env : List (Name × Ref)} {A₁ A' : List Value}
    {L₂ : List (Path × Value)} (h : Agrees fr ⟨env, A₁⟩)
    (hd : ∀ pw ∈ L₂, ∀ e ∈ env, pw.1.Disjoint e.2.toPath)
    (hseq : (Value.list A₁).setSeq L₂ = .ok (.list A')) (hlen : A'.length = A₁.length) :
    Agrees fr ⟨env, A'⟩ := by
  refine ⟨Holds.write.mono h.holds fun xr hxr => ?_, h.disjoint, h.safe⟩
  have hlt := h.valid xr hxr
  rw [deref_eq_get (hlen ▸ hlt) [] [], deref_eq_get hlt [] [], List.append_nil]
  exact Value.get_setSeq_disjoint (fun pw hpw => hd pw hpw xr hxr) hseq

theorem mem_movedPaths {s : State} {bound : List (Name × Passed)} {P : Path}
    (hP : P ∈ bound.filterMap (movedPath s)) :
    ∃ y x v r, (y, Passed.moved x v) ∈ bound ∧ s.env.lookup x = some r ∧ P = r.toPath := by
  obtain ⟨⟨y, a⟩, hmem, ha⟩ := List.mem_filterMap.1 hP
  cases a with
  | value _ | place _ _ => cases ha
  | moved x v =>
    simp only [movedPath, Option.map_eq_some_iff] at ha
    obtain ⟨r, hl, rfl⟩ := ha
    exact ⟨y, x, v, r, hmem, hl, by simp [placeRef, Ref.toPath]⟩

/-- The callee's writes below the caller's part of the store are one write to
each place and each storage handed over, of its final part. -/
theorem leave_writes {fr : Copy.Frame} {s : State} (hs : Agrees fr s) {bound : List (Name × Passed)}
    {frc : Copy.Frame} {sc : State} (hent : Entered s (bound.map Moving.handOver) frc sc)
    (hcompat : ((bound.map Moving.handOver).map Prod.snd).Pairwise Passed.Compat) {s' : State}
    (hev : Evolves sc s') :
    ∃ L₁ L₂ A₁ A' rest, s'.store = A' ++ rest ∧ A'.length = s.store.length ∧
      L₁.map Prod.fst = bound.filterMap (placePath s) ∧
      L₂.map Prod.fst = bound.filterMap (movedPath s) ∧
      (∀ pw ∈ L₁ ++ L₂, (Value.list A').get pw.1 = .ok pw.2) ∧
      (Value.list s.store).setSeq L₁ = .ok (.list A₁) ∧ (Value.list A₁).setSeq L₂ = .ok (.list A') ∧
      A₁.length = s.store.length ∧
      (bound.filterMap (placePath s) ++ bound.filterMap (movedPath s)).Pairwise Path.Disjoint := by
  obtain ⟨-, W, st, extra, hs', hW, hseq⟩ := hev
  obtain ⟨F, hF⟩ := hent.store
  rw [hF] at hseq
  obtain ⟨A', B', hR, hlen, -, hlow, -⟩ := setSeq_append_store
    (fun pw hpw => atLoc_of_under (hW pw hpw)) hseq
  simp only [Value.list.injEq] at hR
  subst hR
  have hperm := perm_paths s bound
  have hd := (placePaths_disjoint hs.disjoint hcompat).perm hperm fun h => Path.Disjoint.symm h
  have hvalid : ∀ P ∈ bound.filterMap (placePath s) ++ bound.filterMap (movedPath s),
      ∃ u, (Value.list s.store).get P = .ok u := by
    intro P hP
    obtain ⟨y, x, p, r, hmem, hl, rfl⟩ := mem_placePaths (hperm.mem_iff.2 hP)
    obtain ⟨r', hl', -, u, hu⟩ := hent.places y x p hmem
    rw [hl] at hl'
    cases hl'
    refine ⟨u, ?_⟩
    show (Value.list s.store).get (r.toPath ++ p) = _
    rw [← deref_eq_get (lt_of_deref hu) s.env]
    exact hu
  have hunder : ∀ pw ∈ W.filter (below s.store.length),
      pw.1.Under (bound.filterMap (placePath s) ++ bound.filterMap (movedPath s)) := by
    intro pw hpw
    obtain ⟨hpw, hb⟩ := List.mem_filter.1 hpw
    obtain ⟨P, hP, q, hq⟩ := hW pw hpw
    obtain ⟨xr, hxr, rfl⟩ := List.mem_map.1 hP
    rcases hent.refs xr hxr with hfresh | ⟨y, x, p, r, hmem, hl, heq⟩
    · simp [below, hq, Ref.toPath] at hb
      omega
    · refine ⟨(placeRef r p).toPath, hperm.mem_iff.1 (List.mem_filterMap.2 ⟨_, hmem, ?_⟩), q,
        by rw [hq, heq]⟩
      simp [placePath, hl]
  obtain ⟨L, hL, hget, hseqL⟩ := Value.setSeq_canon hd hvalid hunder hlow
  obtain ⟨L₁, L₂, A₁, h₁, h₂, rfl, hs₁, hs₂, hlen₁⟩ := split_writes hL (fun P hP => by
    obtain ⟨_, _, _, r, -, -, rfl⟩ := mem_placePaths hP
    exact atLoc_placeRef r _) hseqL
  exact ⟨L₁, L₂, A₁, A', B' ++ extra, by rw [hs', List.append_assoc], hlen, h₁, h₂, hget, hs₁, hs₂,
    hlen₁, hd⟩

end Stilt.Moving
