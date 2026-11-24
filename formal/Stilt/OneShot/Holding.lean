import Stilt.OneShot.Steps
import Stilt.OneShot.Handling

/-!
# Holding shared values, one-shot

A `when` takes one-shot values out of a world whose cells hold one-shot values, and puts
back the one-shot values of its frame; a `with` lets cells go without changing a value. So
both keep every value of the state one-shot, and neither performs a `resume` (shared.when).
-/

namespace Stilt

variable {α : Type} {P : α → Prop}

/-- Putting values of a one-shot frame back keeps a state one-shot. -/
theorem State.OneShot.putBack (w : WriteBack) (held : Bool) :
    ∀ (cells : List (Name × Ty × Nat)) {s s' : Copy.State}, State.OneShot s →
      (Copy.memoryWith w).putBack held cells s = .ok s' → State.OneShot s'
  | [], _, _, hs, h => by cases h; exact hs
  | (x, c) :: rest, (fr, wd), s', hs, h => by
    simp only [Memory.putBack] at h
    cases hr : (Copy.memoryWith w).read (fr, wd) x [] with
    | error e => rw [hr] at h; cases h
    | ok v =>
      rw [hr] at h
      exact State.OneShot.putBack w held rest (s := (fr, wd.put c v held))
        ⟨hs.1, hs.2.put c (Frame.OneShot.read hs.1 (by exact hr)) held⟩ h

namespace Outcome.OneShot

theorem after (w : WriteBack) {held : Bool} {cells : List (Name × Ty × Nat)} {s : Copy.State}
    {n : Nat} {o : Copy.State → Outcome Copy.State α} (hs : State.OneShot s)
    (ho : ∀ s', State.OneShot s' → (o s').OneShot P n) :
    (Outcome.after ((Copy.memoryWith w).putBack held cells) s o).OneShot P n := by
  unfold Outcome.after
  split
  · rename_i s' h
    exact ho s' (hs.putBack w held cells h)
  · exact fault hs

/-- A `when`'s block, its names' values put back however it ends. -/
theorem release (w : WriteBack) (cells : List (Name × Ty × Nat)) :
    ∀ {n : Nat} {o : Outcome Copy.State α}, o.OneShot P n →
      (o.release (Copy.memoryWith w) cells).OneShot P n
  | _, .done _ _, h => after w h.2 fun _ hs => ⟨h.1, hs⟩
  | _, .raised _ _, h => after w h.2 fun _ hs => ⟨h.1, hs⟩
  | _, .jumped _ _, h => after w h.2 fun _ hs => ⟨h.1, hs⟩
  | _, .panicked _ _, h => after w h fun _ hs => hs
  | _, .performed _ _ _ _, h => after w h.2.1 fun _ hs => performed h.1 hs (fun hop => by
      have := h.2.2; simp only [hop, ↓reduceIte] at this; exact this.1)
      fun _ _ hu hx => release w cells (h.rest hu hx)
  | _, .outOfFuel, h | _, .stuck, h => h

/-- A `with`'s outcome, the cells its dropped rests hold let go. -/
theorem letGo (w : WriteBack) (before : World) :
    ∀ {n : Nat} {o : Outcome Copy.State α}, o.OneShot P n →
      (o.letGo (Copy.memoryWith w) before).OneShot P n
  | _, .done _ _, h | _, .raised _ _, h | _, .jumped _ _, h => ⟨h.1, h.2.1, h.2.2.letGo before⟩
  | _, .panicked _ _, h => ⟨h.1, h.2.letGo before⟩
  | _, .performed _ _ _ _, h => performed h.1 h.2.1 (fun hop => by
      have := h.2.2; simp only [hop, ↓reduceIte] at this; exact this.1)
      fun _ _ hu hx => letGo w before (h.rest hu hx)
  | _, .outOfFuel, h | _, .stuck, h => h

end Outcome.OneShot

namespace Eval.OneShot

theorem letGo (w : WriteBack) {n : Nat} {m : Eval Copy.State α} (hm : Eval.OneShot n P m) :
    Eval.OneShot n P (Eval.letGo (Copy.memoryWith w) m) := fun s hs =>
  (hm s hs).letGo w _

/-- A `when` whose block keeps to a count keeps to it (shared.when). -/
theorem held (w : WriteBack) {n : Nat} {m : Eval Copy.State Value} (hm : Eval.OneShot n Value.OneShot m)
    (names : List Name) (vs : List Value) :
    Eval.OneShot n Value.OneShot (Eval.held (Copy.memoryWith w) m names vs) := by
  unfold Eval.held
  refine bindLe (a := 0) (b := n) (ofExcept (P := fun _ => True) fun _ _ => trivial) (fun cells _ => ?_) (by omega)
  refine bindLe (a := 0) (bindLe (b := 0) (world w (R := Value.OneShot) _ fun x v x' hx h => ?_)
    (fun _ hv => asList hv) (Nat.le_refl 0)) (b := n) (fun us hus => ?_) (by omega)
  · cases ht : World.take cells x with
    | error e => rw [ht] at h; cases h
    | ok p =>
      rw [ht] at h
      cases h
      obtain ⟨hp, hx'⟩ := hx.take ht
      exact ⟨.list hp, hx'⟩
  · split
    · exact withVars w (fun s hs => (hm s hs).release w _) _ fun xv hxv => hus _ (List.of_mem_zip hxv).2
    · exact fail

end Eval.OneShot

end Stilt
