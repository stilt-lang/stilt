import Stilt.Moves.Leave

/-!
# The write-back on live bindings

Copy-in, copy-out writes back only to the roots of `inout` arguments, which
are live: so the write-back on the caller's frame and on its live bindings
agree, and it keeps the frame's names. The values it writes back are values
that the callee's `inout` parameters hold, which a run may hold.
-/

namespace Stilt.Moving

open InPlace

variable {m : List Bool}

/-- The write-back on a frame and on its live bindings agree. -/
theorem leave_keep (fr' : Copy.Frame) : ∀ (bound : List (Name × Passed)) (acc : Copy.Frame),
    m.length = acc.length → (∀ y x p, (y, Passed.place x p) ∈ bound → LiveAt x m (names acc)) →
    (keep m ·) <$> bound.foldlM (copyLeaveStep fr') acc =
      bound.foldlM (copyLeaveStep fr') (keep m acc) ∧
    ∀ acc', bound.foldlM (copyLeaveStep fr') acc = .ok acc' → names acc' = names acc
  | [], _, _, _ => ⟨rfl, fun _ h => by cases h; rfl⟩
  | (y, q) :: bound, acc, hlen, hl => by
    have hl' : ∀ acc₂, names acc₂ = names acc →
        ∀ y x p, (y, Passed.place x p) ∈ bound → LiveAt x m (names acc₂) := fun acc₂ hn y x p hm => by
      rw [hn]
      exact hl y x p (List.mem_cons_of_mem _ hm)
    simp only [List.foldlM_cons]
    cases q with
    | value v | moved x v =>
      exact leave_keep fr' bound acc hlen (hl' acc rfl)
    | place x p =>
      simp only [copyLeaveStep]
      cases hr : Copy.read fr' y [] with
      | error e => exact ⟨rfl, fun _ h => by cases h⟩
      | ok v =>
        simp only [Except.bind]
        rw [← write_keep hlen (hl y x p List.mem_cons_self)]
        cases hw : Copy.write acc x p v with
        | error e => exact ⟨rfl, fun _ h => by cases h⟩
        | ok acc₂ =>
          have hn := write_names hw
          have hlen₂ : m.length = acc₂.length := by
            have := congrArg List.length hn
            simp only [names, List.length_map] at this
            rw [hlen, this]
          obtain ⟨h₁, h₂⟩ := leave_keep fr' bound acc₂ hlen₂ (hl' acc₂ hn)
          exact ⟨h₁, fun acc' h => (h₂ acc' h).trans hn⟩

/-- A write-back that succeeds on the live bindings succeeds on the frame. -/
theorem leave_full {fr fr' frL : Copy.Frame} {bound : List (Name × Passed)}
    (hlen : m.length = fr.length) (hl : ∀ y x p, (y, Passed.place x p) ∈ bound → LiveAt x m (names fr))
    (h : Copy.frames.leave (keep m fr) fr' bound = .ok frL) :
    ∃ fr₂, Copy.frames.leave fr fr' bound = .ok fr₂ ∧ keep m fr₂ = frL ∧ names fr₂ = names fr := by
  obtain ⟨hk₁, hk₂⟩ := leave_keep fr' bound fr hlen hl
  rw [copy_leave_eq, ← hk₁] at h
  rw [copy_leave_eq]
  cases hfr : bound.foldlM (copyLeaveStep fr') fr with
  | error e => rw [hfr] at h; cases h
  | ok fr₂ =>
    rw [hfr] at h
    simp only [Functor.map, Except.map, Except.ok.injEq] at h
    exact ⟨fr₂, rfl, h, hk₂ fr₂ hfr⟩

/-- The write-back writes values that the callee's `inout` parameters hold. -/
theorem leave_just {fr' : Copy.Frame} :
    ∀ (bound : List (Name × Passed)) (acc acc' : Copy.Frame), (∀ xv ∈ acc, xv.2.Justified) →
      (∀ y x p v, (y, Passed.place x p) ∈ bound → Copy.read fr' y [] = .ok v → v.Justified) →
      bound.foldlM (copyLeaveStep fr') acc = .ok acc' → ∀ xv ∈ acc', xv.2.Justified
  | [], _, _, hacc, _, h => by cases h; exact hacc
  | (y, q) :: bound, acc, acc', hacc, hv, h => by
    have hv' := fun y x p v (hm : (y, Passed.place x p) ∈ bound) => hv y x p v (List.mem_cons_of_mem _ hm)
    simp only [List.foldlM_cons] at h
    cases q with
    | value w | moved x w => exact leave_just bound acc acc' hacc hv' h
    | place x p =>
      simp only [copyLeaveStep] at h
      cases hr : Copy.read fr' y [] with
      | error e => rw [hr] at h; cases h
      | ok w =>
        rw [hr] at h
        simp only [Except.bind] at h
        cases hw : Copy.write acc x p w with
        | error e => rw [hw] at h; cases h
        | ok acc₂ =>
          rw [hw] at h
          refine leave_just bound acc₂ acc' (fun xv hxv => ?_) hv' h
          unfold Copy.write at hw
          split at hw
          · rename_i u hu
            cases hu' : u.set p w with
            | error e => rw [hu'] at hw; cases hw
            | ok u' =>
              rw [hu'] at hw
              cases hw
              rcases mem_assocSet hxv with hxv | hxv
              · exact hacc xv hxv
              · exact hxv ▸ Value.Justified.set (hacc _ (mem_of_lookup hu))
                  (hv y x p w List.mem_cons_self hr) hu'
          · cases hw

/-- A parameter bound to a place is an `inout` parameter (values.inout-arguments). -/
theorem bindArgs_inout : ∀ {params : List Param} {passed : List Passed} {bound : List (Name × Passed)},
    bindArgs params passed = some bound → ∀ y x p, (y, Passed.place x p) ∈ bound →
      (inoutLive params).mem y = true
  | [], [], _, h, _, _, _, hm => by cases h; simp at hm
  | p :: ps, a :: args, bound, h, y, x, q, hm => by
    have hmem : ∀ z, (inoutLive (p :: ps)).mem z = true ↔
        (p.mode = .inout ∧ p.name = z) ∨ (inoutLive ps).mem z = true := by
      intro z
      simp only [inoutLive, Live.mem_ofList, List.mem_map, List.mem_filter, List.mem_cons,
        beq_iff_eq]
      constructor
      · rintro ⟨p', ⟨rfl | hp', hm'⟩, rfl⟩
        · exact .inl ⟨hm', rfl⟩
        · exact .inr ⟨p', ⟨hp', hm'⟩, rfl⟩
      · rintro (⟨hm', rfl⟩ | ⟨p', ⟨hp', hm'⟩, rfl⟩)
        · exact ⟨p, ⟨.inl rfl, hm'⟩, rfl⟩
        · exact ⟨p', ⟨.inr hp', hm'⟩, rfl⟩
    have hsub : (inoutLive ps).mem y = true → (inoutLive (p :: ps)).mem y = true :=
      fun h => (hmem y).2 (.inr h)
    unfold bindArgs at h
    split at h <;> (try cases h) <;>
      (cases hb : bindArgs ps args with
        | none => simp [hb] at h
        | some b =>
          simp only [hb, Option.map_some, Option.some.injEq] at h
          subst h
          rcases List.mem_cons.1 hm with hm | hm
          · simp only [Prod.mk.injEq] at hm
            obtain ⟨rfl, hq⟩ := hm
            first
              | exact (hmem _).2 (.inl ⟨by assumption, rfl⟩)
              | cases hq
          · exact hsub (bindArgs_inout hb y x q hm))
  | [], _ :: _, _, h, _, _, _, _ | _ :: _, [], _, h, _, _, _, _ => by cases h

/-- A store only grows. -/
theorem Evolves.length_le {s s' : State} (h : Evolves s s') : s.store.length ≤ s'.store.length := by
  obtain ⟨-, W, st, extra, hs, hW, hseq⟩ := h
  obtain ⟨A, B, hR, hlen, hB, -, -⟩ := setSeq_append_store (B := [])
    (fun pw hpw => atLoc_of_under (hW pw hpw)) (by rw [List.append_nil]; exact hseq)
  have : B = [] := List.eq_nil_of_length_eq_zero hB
  subst this
  simp only [List.append_nil, Value.list.injEq] at hR
  subst hR
  rw [hs, List.length_append, hlen]
  omega

end Stilt.Moving
