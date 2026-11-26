import Stilt.Locks.Values

/-!
# Outcomes that take no cell

`World.HoldsNoMore x y`: every cell that `y` holds, `x` holds. A cell is a place of the
store, made and never unmade, so a world holds no more than another when no `when` has taken
a cell since. `Outcome.TakesNone P x o`: every state `o` carries holds no more than `x`,
every value and frame in it is lock-free, a final value is one of which `P` holds, and a
performance's rest, resumed with a lock-free value in any world, holds no more than that
world (shared.locks). What the code around a performance runs before resuming it, the
handler's body, is not the code's own.
-/

namespace Stilt

variable {D : Decls} {L : List Name}

/-- Every cell that `y` holds, `x` holds. -/
def World.HoldsNoMore (x y : World) : Prop :=
  ∀ (i : Nat) (c : Cell), y.cells[i]? = some c → c.held = true →
    ∃ c', x.cells[i]? = some c' ∧ c'.held = true

namespace World.HoldsNoMore

variable {x y z : World}

theorem refl (x : World) : x.HoldsNoMore x := fun _ c h hc => ⟨c, h, hc⟩

theorem trans (h₁ : x.HoldsNoMore y) (h₂ : y.HoldsNoMore z) : x.HoldsNoMore z := fun i c h hc =>
  let ⟨_, h', hc'⟩ := h₂ i c h hc
  h₁ i _ h' hc'

/-- A new cell is held by no one. -/
theorem push (h : x.HoldsNoMore y) (u : Ty) (v : Value) : x.HoldsNoMore (y.push u v) := by
  intro i c hc hheld
  simp only [World.push] at hc
  by_cases hi : i < y.cells.length
  · rw [List.getElem?_append_left hi] at hc
    exact h i c hc hheld
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hc
    cases hk : i - y.cells.length with
    | zero => simp only [hk, List.getElem?_cons_zero, Option.some.injEq] at hc; subst hc; cases hheld
    | succ n => simp [hk] at hc

theorem letGo_cells : ∀ (bs cs : List Cell) (i : Nat) (c : Cell), (Cell.letGo bs cs)[i]? = some c →
    c.held = true → ∃ c', cs[i]? = some c' ∧ c'.held = true
  | b :: bs, c₀ :: cs, 0, c, h, hc => by
    simp only [Cell.letGo, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    refine ⟨c₀, rfl, ?_⟩
    split at hc
    · cases hc
    · rename_i hn
      revert hn hc
      cases c₀.held <;> simp
  | _ :: bs, _ :: cs, i + 1, c, h, hc => by
    simp only [Cell.letGo, List.getElem?_cons_succ] at h
    simpa using letGo_cells bs cs i c h hc
  | [], cs, i, c, h, hc => by
    simp only [Cell.letGo, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    cases hc
  | _ :: _, [], _, _, h, _ => by simp [Cell.letGo] at h

/-- Letting cells go holds no more. -/
theorem letGo (h : x.HoldsNoMore y) (before : World) : x.HoldsNoMore (before.letGo y) :=
  fun i c hc hheld =>
    let ⟨_, h', hc'⟩ := letGo_cells before.cells y.cells i c hc hheld
    h i _ h' hc'

/-- An operation holds no cell: it leaves the cells, or makes one. -/
theorem run (h : x.HoldsNoMore y) {o : Op} {vs : List Value} {v : Value} {y' : World}
    (hr : o.run vs y = .ok (v, y')) : x.HoldsNoMore y' := by
  cases o
  case world k =>
    rcases WorldOp.run_cells hr with hc | ⟨u, w, _, rfl⟩
    · exact fun i c hi => h i c (hc ▸ hi)
    · exact h.push u w
  all_goals
    simp only [Op.run, Functor.map, Except.map] at hr
    split at hr <;> cases hr
    exact h

end World.HoldsNoMore

/-- Every state an outcome carries holds no more than `x`, with lock-free values and frames;
a performance's rest, resumed with a lock-free value in a world, holds no more than it. -/
def Outcome.TakesNone {α : Type} (D : Decls) (L : List Name) (P : α → Prop) (x : World) :
    Outcome Copy.State α → Prop
  | .done a s => P a ∧ Frame.LockFree D L s.1 ∧ x.HoldsNoMore s.2
  | .raised e s => e.LockFree D L ∧ Frame.LockFree D L s.1 ∧ x.HoldsNoMore s.2
  | .jumped j s => j.LockFree D L ∧ Frame.LockFree D L s.1 ∧ x.HoldsNoMore s.2
  | .panicked _ s => x.HoldsNoMore s.2
  | .performed _ v s k => v.LockFree D L ∧ Frame.LockFree D L s.1 ∧ x.HoldsNoMore s.2 ∧
      ∀ u y, u.LockFree D L → Outcome.TakesNone D L P y (k u y)
  | .outOfFuel | .stuck => True

/-- From a lock-free frame, `m` ends holding no more than its world, with lock-free values
and frames. -/
def Eval.TakesNone {α : Type} (D : Decls) (L : List Name) (P : α → Prop)
    (m : Eval Copy.State α) : Prop :=
  ∀ s : Copy.State, Frame.LockFree D L s.1 → (m s).TakesNone D L P s.2

namespace Outcome.TakesNone

variable {α β : Type} {P : α → Prop} {Q : β → Prop} {x : World}

/-- A world that holds more is a base too. -/
theorem weaken {y : World} (hxy : x.HoldsNoMore y) :
    ∀ {o : Outcome Copy.State α}, o.TakesNone D L P y → o.TakesNone D L P x
  | .done _ _, h | .raised _ _, h | .jumped _ _, h => ⟨h.1, h.2.1, hxy.trans h.2.2⟩
  | .panicked _ _, h => hxy.trans h
  | .performed _ _ _ _, h => ⟨h.1, h.2.1, hxy.trans h.2.2.1, h.2.2.2⟩
  | .outOfFuel, h | .stuck, h => h

theorem mono {R : α → Prop} (hPQ : ∀ a, P a → R a) :
    ∀ {x : World} {o : Outcome Copy.State α}, o.TakesNone D L P x → o.TakesNone D L R x
  | _, .done _ _, h => ⟨hPQ _ h.1, h.2⟩
  | _, .performed _ _ _ _, h => ⟨h.1, h.2.1, h.2.2.1, fun u y hu => mono hPQ (h.2.2.2 u y hu)⟩
  | _, .raised _ _, h | _, .jumped _ _, h | _, .panicked _ _, h | _, .outOfFuel, h
  | _, .stuck, h => h

theorem fault {f : Fault} {s : Copy.State} (hx : x.HoldsNoMore s.2) :
    (Outcome.fault f s : Outcome Copy.State α).TakesNone D L P x := by
  cases f <;> first | exact hx | trivial

/-- What follows each value an outcome reaches. -/
theorem bind {f : α → Copy.State → Outcome Copy.State β}
    (hf : ∀ a s, P a → Frame.LockFree D L s.1 → (f a s).TakesNone D L Q s.2) :
    ∀ {x : World} {o : Outcome Copy.State α}, o.TakesNone D L P x → (o.bind f).TakesNone D L Q x
  | _, .done a s, h => weaken h.2.2 (hf a s h.1 h.2.1)
  | _, .performed _ _ _ _, h => ⟨h.1, h.2.1, h.2.2.1, fun u y hu => bind hf (h.2.2.2 u y hu)⟩
  | _, .raised _ _, h | _, .jumped _ _, h | _, .panicked _ _, h | _, .outOfFuel, h
  | _, .stuck, h => h

/-- A raise handed to a handler. -/
theorem handle {g : Value → Copy.State → Outcome Copy.State α}
    (hg : ∀ e s, e.LockFree D L → Frame.LockFree D L s.1 → (g e s).TakesNone D L P s.2) :
    ∀ {x : World} {o : Outcome Copy.State α}, o.TakesNone D L P x → (o.handle g).TakesNone D L P x
  | _, .raised e s, h => weaken h.2.2 (hg e s h.1 h.2.1)
  | _, .performed _ _ _ _, h => ⟨h.1, h.2.1, h.2.2.1, fun u y hu => handle hg (h.2.2.2 u y hu)⟩
  | _, .done _ _, h | _, .jumped _ _, h | _, .panicked _ _, h | _, .outOfFuel, h
  | _, .stuck, h => h

theorem turn {R : Value → Prop} :
    ∀ {x : World} {o : Outcome Copy.State Value}, o.TakesNone D L R x →
      o.turn.TakesNone D L (fun _ => True) x
  | _, .done _ _, h => ⟨trivial, h.2⟩
  | _, .jumped .brk _, h => ⟨trivial, h.2⟩
  | _, .jumped .cont _, h => ⟨trivial, h.2⟩
  | _, .jumped (.ret _) _, h => h
  | _, .performed _ _ _ _, h => ⟨h.1, h.2.1, h.2.2.1, fun u y hu => turn (h.2.2.2 u y hu)⟩
  | _, .raised _ _, h | _, .panicked _ _, h | _, .outOfFuel, h | _, .stuck, h => h

/-- A scope's end, which drops its binding from every frame. -/
theorem unbind (w : WriteBack) :
    ∀ {x : World} {o : Outcome Copy.State α}, o.TakesNone D L P x →
      (o.unbind (Copy.memoryWith w)).TakesNone D L P x
  | _, .done _ _, h | _, .raised _ _, h | _, .jumped _ _, h => ⟨h.1, h.2.1.tail, h.2.2⟩
  | _, .panicked _ _, h => h
  | _, .performed _ _ _ _, h =>
    ⟨h.1, h.2.1.tail, h.2.2.1, fun u y hu => unbind w (h.2.2.2 u y hu)⟩
  | _, .outOfFuel, h | _, .stuck, h => h

/-- A clause's outcome as the `with`'s, from a lock-free frame. -/
theorem lift (w : WriteBack) {s : Copy.State} (hs : Frame.LockFree D L s.1) :
    ∀ {x : World} {o : Outcome Copy.State α}, o.TakesNone D L P x →
      (o.lift (Copy.memoryWith w) s).TakesNone D L P x
  | _, .done _ _, h | _, .raised _ _, h | _, .jumped _ _, h => ⟨h.1, hs, h.2.2⟩
  | _, .panicked _ _, h => h
  | _, .performed _ _ _ _, h => ⟨h.1, hs, h.2.2.1, fun u y hu => lift w hs (h.2.2.2 u y hu)⟩
  | _, .outOfFuel, h | _, .stuck, h => h

/-- A `with`'s outcome, the cells its dropped rests hold let go. -/
theorem letGo (w : WriteBack) (before : World) :
    ∀ {x : World} {o : Outcome Copy.State α}, o.TakesNone D L P x →
      (o.letGo (Copy.memoryWith w) before).TakesNone D L P x
  | _, .done _ _, h | _, .raised _ _, h | _, .jumped _ _, h => ⟨h.1, h.2.1, h.2.2.letGo before⟩
  | _, .panicked _ _, h => World.HoldsNoMore.letGo h before
  | _, .performed _ _ _ _, h =>
    ⟨h.1, h.2.1, h.2.2.1, fun u y hu => letGo w before (h.2.2.2 u y hu)⟩
  | _, .outOfFuel, h | _, .stuck, h => h

end Outcome.TakesNone

end Stilt
