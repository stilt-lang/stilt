import Stilt.OneShot.Outcomes

/-!
# Handlers that resume at most once

The body of an operation of a handler that takes control runs the rest of the
`with`'s block once for each `resume` it performs (handlers.resuming), so a
body that performs at most one on each path runs it at most once, and the
`with` performs no more `resume`s of the code around it than its block does: a
`with` names an effect other than that of `resume`, so the block's pass
through it. A call ends with the count of its callee's body.
-/

namespace Stilt

/-- The clause of a one-shot handler is one-shot. -/
theorem Value.OneShot.clause {handler c : Value} {op : Name} (hh : handler.OneShot)
    (hc : handler.clause? op = some c) : c.OneShot := by
  cases handler <;> simp only [Value.clause?, reduceCtorEq] at hc
  cases hh with
  | record hfs => exact hfs _ (mem_of_lookup hc)

namespace Outcome.OneShot

variable {α : Type} {P : α → Prop}

theorem fault {f : Fault} {s : Copy.State} (hs : State.OneShot s) {n : Nat} :
    (Outcome.fault f s : Outcome Copy.State α).OneShot P n := by
  cases f <;> first | exact hs | trivial

/-- The body of a clause that takes control, with at most `c ≤ 1` performances
of `resume` on each path, each running a rest with at most `m`: the `with`
performs at most `m` on each path, and none when the body never resumes. -/
theorem runBody (w : WriteBack) {resume : Value → World → Outcome Copy.State Value} {m : Nat}
    (hr : ∀ u x, u.OneShot → x.All Value.OneShot → (resume u x).OneShot Value.OneShot m) :
    ∀ {c : Nat} {o : Outcome Copy.State Value}, c ≤ 1 → o.OneShot Value.OneShot c →
      (o.runBody (Copy.memoryWith w) resume).OneShot Value.OneShot (c * m)
  | c, .performed op u s k, hc, h => by
    unfold Outcome.runBody
    split <;> rename_i hop
    · have h' := h.2.2
      simp only [hop, ↓reduceIte] at h'
      obtain rfl : c = 1 := by omega
      have hb := bind (b := 0) (f := fun r s' =>
          ((k r s'.2).runBody (Copy.memoryWith w) resume).lift (Copy.memoryWith w) s')
        (fun r s' (hr' : r.OneShot) hs' =>
          lift w hs' (by simpa using runBody w hr (Nat.zero_le 1) (h'.2 r s'.2 hr' hs'.2)))
        (hr u s.2 h.1 h.2.1.2)
      rw [Nat.one_mul]
      exact hb
    · exact performed h.1 h.2.1 (fun hop' => absurd hop' hop) fun u x hw hx => by
        simpa [hop] using runBody w hr hc (by simpa [hop] using h.rest hw hx)
  | _, .done _ _, _, h | _, .raised _ _, _, h | _, .jumped _ _, _, h | _, .panicked _ _, _, h
  | _, .outOfFuel, _, h | _, .stuck, _, h => h

/-- A `with` of a one-shot handler whose clauses' calls perform at most one
`resume` when it takes control, and none otherwise, keeps its block's count:
the block's own `resume`s go through it, since its effect is another. -/
theorem handleWith (w : WriteBack) {effect : Name} (heff : effect ≠ Operation.resume.effect)
    {control : Bool} {handler : Value}
    {call : Value → Value → Copy.State → Outcome Copy.State Value} (hh : handler.OneShot)
    (hcall : ∀ c v s, c.OneShot → v.OneShot → State.OneShot s →
      (call c v s).OneShot Value.OneShot (if control then 1 else 0)) :
    ∀ {n : Nat} {o : Outcome Copy.State Value}, o.OneShot Value.OneShot n →
      (o.handleWith (Copy.memoryWith w) effect control handler call).OneShot Value.OneShot n
  | n, .performed op v s k, h => by
    unfold Outcome.handleWith
    split <;> rename_i heq
    · have hop : op ≠ Operation.resume := fun hop => heff (hop ▸ heq).symm
      have hk : ∀ u x, u.OneShot → x.All Value.OneShot → (k u x).OneShot Value.OneShot n :=
        fun u x hw hx => by simpa [hop] using h.rest hw hx
      split
      · trivial
      · rename_i c hc
        have hcv := hcall c v s (hh.clause hc) h.1 h.2.1
        split <;> rename_i hctl
        · simp only [hctl, ↓reduceIte] at hcv
          simpa using runBody w (fun u x hu hx => handleWith w heff hh hcall (hk u x hu hx))
            (Nat.le_refl 1) hcv
        · simp only [hctl] at hcv
          simpa using bind (b := n) (f := fun u s' => Outcome.handleWith (Copy.memoryWith w) effect control handler call
            (k u ((Copy.memoryWith w).world s'))) (fun u s' hw hs' => handleWith w heff hh hcall (hk u _ hw hs'.2)) hcv
    · exact performed h.1 h.2.1 (fun hop => by
        have h' := h.2.2; simp only [hop, ↓reduceIte] at h'; exact h'.1)
        fun _ _ hw hx => handleWith w heff hh hcall (h.rest hw hx)
  | _, .done _ _, h | _, .raised _ _, h | _, .jumped _ _, h | _, .panicked _ _, h
  | _, .outOfFuel, h | _, .stuck, h => h

/-- A callee's outcome, the call left from a one-shot frame, a performance's
rest included. -/
theorem leaveCall (w : WriteBack) {s : Copy.State} (hs : State.OneShot s)
    {bound : List (Name × Passed)} :
    ∀ {n : Nat} {o : Outcome Copy.State Value}, o.OneShot Value.OneShot n →
      (o.leaveCall (Copy.memoryWith w) bound s).OneShot Value.OneShot n
  | _, .done _ s', h | _, .raised _ s', h | _, .panicked _ s', h => by
    simp only [Outcome.leaveCall]
    cases hle : (Copy.memoryWith w).leave s s' bound with
    | ok s'' =>
      obtain ⟨fr, hfr, rfl⟩ := Frames.withWorld_leave_ok _ hle
      first
        | exact ⟨h.1, Frame.OneShot.leave h.2.1 _ hs.1 hfr, h.2.2⟩
        | exact ⟨Frame.OneShot.leave h.1 _ hs.1 hfr, h.2⟩
    | error f => first | exact fault (s := (Copy.memoryWith w).setWorld s ((Copy.memoryWith w).world s')) ⟨hs.1, h.2.2⟩ | exact fault (s := (Copy.memoryWith w).setWorld s ((Copy.memoryWith w).world s')) ⟨hs.1, h.2⟩
  | _, .jumped (.ret _) s', h => by
    simp only [Outcome.leaveCall]
    cases hle : (Copy.memoryWith w).leave s s' bound with
    | ok s'' =>
      obtain ⟨fr, hfr, rfl⟩ := Frames.withWorld_leave_ok _ hle
      exact ⟨h.1, Frame.OneShot.leave h.2.1 _ hs.1 hfr, h.2.2⟩
    | error f => exact fault (s := (Copy.memoryWith w).setWorld s ((Copy.memoryWith w).world s')) ⟨hs.1, h.2.2⟩
  | _, .jumped .brk _, _ | _, .jumped .cont _, _ => trivial
  | _, .performed _ _ s' _, h => by
    simp only [Outcome.leaveCall]
    cases hle : (Copy.memoryWith w).leave s s' bound with
    | ok s'' =>
      obtain ⟨fr, hfr, rfl⟩ := Frames.withWorld_leave_ok _ hle
      exact performed h.1 ⟨Frame.OneShot.leave h.2.1.1 _ hs.1 hfr, h.2.1.2⟩ (fun hop => by
        have h' := h.2.2; simp only [hop, ↓reduceIte] at h'; exact h'.1)
        fun _ _ hu hx => leaveCall w hs (h.rest hu hx)
    | error f => exact fault (s := (Copy.memoryWith w).setWorld s ((Copy.memoryWith w).world s')) ⟨hs.1, h.2.1.2⟩
  | _, .outOfFuel, _ | _, .stuck, _ => trivial

end Outcome.OneShot

end Stilt
