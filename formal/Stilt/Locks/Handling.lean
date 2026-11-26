import Stilt.Locks.Outcomes
import Stilt.Handling

/-!
# Calls and handlers that take no cell

A call left from a lock-free frame writes lock-free values back, and holds no cell the
callee's outcome doesn't. A `with` whose clauses' calls take no cell takes none of its own:
the body of a clause that takes control runs the rest of the block at each `resume`, and the
rest goes on from the world the clause left (shared.locks).
-/

namespace Stilt

variable {D : Decls} {L : List Name}

namespace Outcome.TakesNone

variable {α : Type} {P : α → Prop}

/-- A callee's outcome, the call left from a lock-free frame, a performance's rest
included. -/
theorem leaveCall (w : WriteBack) {s : Copy.State} (hs : Frame.LockFree D L s.1)
    {bound : List (Name × Passed)} :
    ∀ {x : World} {o : Outcome Copy.State Value}, o.TakesNone D L (Value.LockFree D L) x →
      (o.leaveCall (Copy.memoryWith w) bound s).TakesNone D L (Value.LockFree D L) x
  | _, .done _ s', h | _, .raised _ s', h => by
    simp only [Outcome.leaveCall]
    cases hle : (Copy.memoryWith w).leave s s' bound with
    | ok s'' =>
      obtain ⟨fr, hfr, rfl⟩ := Frames.withWorld_leave_ok _ hle
      exact ⟨h.1, Frame.LockFree.leave h.2.1 _ hs hfr, h.2.2⟩
    | error f => exact fault (s := (s.1, s'.2)) h.2.2
  | _, .panicked _ s', h => by
    simp only [Outcome.leaveCall]
    cases hle : (Copy.memoryWith w).leave s s' bound with
    | ok s'' =>
      obtain ⟨fr, hfr, rfl⟩ := Frames.withWorld_leave_ok _ hle
      exact h
    | error f => exact fault (s := (s.1, s'.2)) h
  | _, .jumped (.ret _) s', h => by
    simp only [Outcome.leaveCall]
    cases hle : (Copy.memoryWith w).leave s s' bound with
    | ok s'' =>
      obtain ⟨fr, hfr, rfl⟩ := Frames.withWorld_leave_ok _ hle
      exact ⟨h.1, Frame.LockFree.leave h.2.1 _ hs hfr, h.2.2⟩
    | error f => exact fault (s := (s.1, s'.2)) h.2.2
  | _, .jumped .brk _, _ | _, .jumped .cont _, _ => trivial
  | _, .performed _ _ s' _, h => by
    simp only [Outcome.leaveCall]
    cases hle : (Copy.memoryWith w).leave s s' bound with
    | ok s'' =>
      obtain ⟨fr, hfr, rfl⟩ := Frames.withWorld_leave_ok _ hle
      exact ⟨h.1, Frame.LockFree.leave h.2.1 _ hs hfr, h.2.2.1,
        fun u y hu => leaveCall w hs (h.2.2.2 u y hu)⟩
    | error f => exact fault (s := (s.1, s'.2)) h.2.2.1
  | _, .outOfFuel, _ | _, .stuck, _ => trivial

/-- The body of a clause that takes control, each `resume` running a rest that takes no
cell from the world it is resumed in. -/
theorem runBody (w : WriteBack) {resume : Value → World → Outcome Copy.State Value}
    (hr : ∀ u y, u.LockFree D L → (resume u y).TakesNone D L (Value.LockFree D L) y) :
    ∀ {x : World} {o : Outcome Copy.State Value}, o.TakesNone D L (Value.LockFree D L) x →
      (o.runBody (Copy.memoryWith w) resume).TakesNone D L (Value.LockFree D L) x
  | x, .performed op u s k, h => by
    unfold Outcome.runBody
    split
    · exact weaken h.2.2.1 (bind (fun r s' hr' hs' =>
        lift w hs' (runBody w hr (h.2.2.2 r s'.2 hr'))) (hr u s.2 h.1))
    · exact ⟨h.1, h.2.1, h.2.2.1, fun u' y hu => runBody w hr (h.2.2.2 u' y hu)⟩
  | _, .done _ _, h | _, .raised _ _, h | _, .jumped _ _, h | _, .panicked _ _, h
  | _, .outOfFuel, h | _, .stuck, h => h

/-- A `with` of a lock-free handler whose clauses' calls take no cell. -/
theorem handleWith (w : WriteBack) {effect : Name} {control : Bool} {handler : Value}
    {call : Value → Value → Copy.State → Outcome Copy.State Value}
    (hh : handler.LockFree D L)
    (hcall : ∀ c v s, c.LockFree D L → v.LockFree D L → Frame.LockFree D L s.1 →
      (call c v s).TakesNone D L (Value.LockFree D L) s.2) :
    ∀ {x : World} {o : Outcome Copy.State Value}, o.TakesNone D L (Value.LockFree D L) x →
      (o.handleWith (Copy.memoryWith w) effect control handler call).TakesNone D L
        (Value.LockFree D L) x
  | x, .performed op v s k, h => by
    unfold Outcome.handleWith
    split
    · split
      · trivial
      · rename_i c hc
        have hcv := hcall c v s (hh.clause hc) h.1 h.2.1
        split
        · exact weaken h.2.2.1 (runBody w (fun u y hu => handleWith w hh hcall (h.2.2.2 u y hu)) hcv)
        · exact weaken h.2.2.1 (bind (fun u s' hu _ => handleWith w hh hcall (h.2.2.2 u s'.2 hu)) hcv)
    · exact ⟨h.1, h.2.1, h.2.2.1, fun u y hu => handleWith w hh hcall (h.2.2.2 u y hu)⟩
  | _, .done _ _, h | _, .raised _ _, h | _, .jumped _ _, h | _, .panicked _ _, h
  | _, .outOfFuel, h | _, .stuck, h => h

end Outcome.TakesNone

end Stilt
