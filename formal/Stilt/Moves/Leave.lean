import Stilt.Moves.End

/-!
# Leaving a call

Copy-in, copy-out's write-back after a call agrees with the store the callee
left on every binding of the caller but those whose last use the call was
(values.passing-values, values.inout-arguments and values.inout-argument-order), and the caller's state evolved only by writes
below the places and the storage that the call passed.
-/

namespace Stilt.Moving

open InPlace

/-- The write-back of the `inout` arguments, which `leave_fold` gives. -/
theorem leave_inout {fr : Copy.Frame} {s : State} (hs : Agrees fr s) {bound : List (Name × Passed)}
    {frc : Copy.Frame} {sc : State} (hent : Entered s (bound.map Moving.handOver) frc sc)
    {fr' : Copy.Frame} {s' : State} (henv : s'.env = sc.env)
    (hread : ∀ y x p, (y, Passed.place x p) ∈ bound →
      Copy.read fr' y [] = InPlace.read s' y [] ∧ ∀ v, Copy.read fr' y [] = .ok v → v.Safe)
    {L₁ L₂ : List (Path × Value)} {A₁ A' rest : List Value} (hs' : s'.store = A' ++ rest)
    (hlen : A'.length = s.store.length) (h₁ : L₁.map Prod.fst = bound.filterMap (placePath s))
    (hget : ∀ pw ∈ L₁ ++ L₂, (Value.list A').get pw.1 = .ok pw.2)
    (hs₁ : (Value.list s.store).setSeq L₁ = .ok (.list A₁))
    (hs₂ : (Value.list A₁).setSeq L₂ = .ok (.list A'))
    (hdis : ∀ pw ∈ L₂, ∀ P ∈ bound.filterMap (placePath s), pw.1.Disjoint P) :
    ∃ fr'', Copy.frames.leave fr fr' bound = .ok fr'' ∧ Agrees fr'' ⟨s.env, A₁⟩ := by
  have hgetA : ∀ P ∈ bound.filterMap (placePath s), (Value.list A').get P = (Value.list A₁).get P :=
    fun P hP => Value.get_setSeq_disjoint (fun pw hpw => hdis pw hpw P hP) hs₂
  have hget₁ : ∀ pw ∈ L₁, (Value.list A₁).get pw.1 = .ok pw.2 := fun pw hpw => by
    rw [← hgetA pw.1 (h₁ ▸ List.mem_map_of_mem hpw)]
    exact hget pw (List.mem_append_left _ hpw)
  have hread₁ : ∀ y x p, (y, Passed.place x p) ∈ bound → ∃ r, s.env.lookup x = some r ∧
      Copy.read fr' y [] = (Value.list A₁).get (placeRef r p).toPath := by
    intro y x p hmem
    obtain ⟨r, hl, hly, u, hu⟩ := hent.places y x p (List.mem_map.2 ⟨_, hmem, rfl⟩)
    have hlt := lt_of_deref hu
    refine ⟨r, hl, ?_⟩
    rw [(hread y x p hmem).1, ← hgetA _ (List.mem_filterMap.2 ⟨_, hmem, by simp [placePath, hl]⟩)]
    simp only [InPlace.read, henv, hly]
    rw [deref_store, hs', deref_eq_get (by simp [placeRef]; omega),
      get_append_low (by simpa [placeRef, hlen] using hlt), List.append_nil]
  obtain ⟨fr'', hfold, hag⟩ := leave_fold hread₁ (fun y x p v hm hv => (hread y x p hm).2 v hv)
    bound (fun _ h => h) fr s.store L₁ hs h₁ hget₁ hs₁
  exact ⟨fr'', by rw [copy_leave_eq]; exact hfold, hag⟩

/-- The end of a call: the write-back agrees with the store the callee left on
every binding but the variables `D`, which hold the last uses the call
passed, and the caller's state evolved by writes below the places and the
storage it passed. -/
theorem leave_moved {fr : Copy.Frame} {s : State} (hs : Agrees fr s) {bound : List (Name × Passed)}
    {frc : Copy.Frame} {sc : State} (hent : Entered s (bound.map Moving.handOver) frc sc)
    (hcompat : ((bound.map Moving.handOver).map Prod.snd).Pairwise Passed.Compat)
    {fr' : Copy.Frame} {s' : State} (hev : Evolves sc s')
    (hread : ∀ y x p, (y, Passed.place x p) ∈ bound →
      Copy.read fr' y [] = InPlace.read s' y [] ∧ ∀ v, Copy.read fr' y [] = .ok v → v.Safe)
    (D : List Name) (hD : ∀ y x v, (y, Passed.moved x v) ∈ bound → x ∈ D)
    {E : List (Name × Ref)} (hE : ∀ y x p r, (y, Passed.place x p) ∈ bound.map Moving.handOver →
      s.env.lookup x = some r → (x, r) ∈ E) :
    ∃ fr'', Copy.frames.leave fr fr' bound = .ok fr'' ∧
      Agrees (dropAll D fr'') ⟨dropAll D s.env, s'.store⟩ ∧ Evolves ⟨E, s.store⟩ ⟨E, s'.store⟩ := by
  obtain ⟨L₁, L₂, A₁, A', rest, hs', hlen, h₁, h₂, hget, hs₁, hs₂, hlen₁, hd⟩ :=
    leave_writes hs hent hcompat hev
  rw [List.pairwise_append] at hd
  have hdis : ∀ pw ∈ L₂, ∀ P ∈ bound.filterMap (placePath s), pw.1.Disjoint P := fun pw hpw P hP =>
    (hd.2.2 P hP pw.1 (h₂ ▸ List.mem_map_of_mem hpw)).symm
  obtain ⟨fr'', hfold, hag₁⟩ :=
    leave_inout hs hent hev.1 hread hs' hlen h₁ hget hs₁ hs₂ hdis
  refine ⟨fr'', hfold, ?_, ?_⟩
  · rw [hs']
    refine (Agrees.setSeq_disjoint (Agrees.dropAll D hag₁) (fun pw hpw e he => ?_) hs₂
      (by rw [hlen, hlen₁])).store_append rest
    obtain ⟨y, x, v, r, hmem, hl, hP⟩ := mem_movedPaths (h₂ ▸ List.mem_map_of_mem hpw)
    rw [hP]
    exact (disjoint_dropAll (hD y x v hmem) hs.disjoint hl e he).symm
  · refine ⟨rfl, L₁ ++ L₂, A', rest, hs', fun pw hpw => ?_, by
      rw [Value.setSeq_append, hs₁]
      exact hs₂⟩
    have hP : pw.1 ∈ (bound.map Moving.handOver).filterMap (placePath s) :=
      (perm_paths s bound).mem_iff.2 (by
        rw [← h₁, ← h₂, ← List.map_append]
        exact List.mem_map_of_mem hpw)
    obtain ⟨y, x, p, r, hmem, hl, hP⟩ := mem_placePaths hP
    exact ⟨r.toPath, List.mem_map.2 ⟨(x, r), hE y x p r hmem hl, rfl⟩, p, hP⟩

end Stilt.Moving
