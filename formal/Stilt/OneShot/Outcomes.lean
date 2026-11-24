import Stilt.OneShot.Values

/-!
# Outcomes that resume at most so often

`Outcome.OneShot P n o`: on each path through `o`, at most `n` performances of
`resume`, every value one-shot, a final value of which `P` holds, and every
state one-shot: its frame and the values its world's cells hold. A performance's
rest is taken at every one-shot value, in every world whose cells hold one-shot
values, since the handler gives it those; the rest of a `resume` has one fewer left. What
follows a step adds its own count to the step's, and a `catch` its handler's to
its operand's (handlers.resume-at-most-once).
-/

namespace Stilt

/-- On each path through an outcome, at most `n` performances of `resume`, and
every value and state one-shot. -/
def Outcome.OneShot {α : Type} (P : α → Prop) : Nat → Outcome Copy.State α → Prop
  | _, .done a s => P a ∧ State.OneShot s
  | _, .raised e s => e.OneShot ∧ State.OneShot s
  | _, .jumped j s => j.OneShot ∧ State.OneShot s
  | _, .panicked _ s => State.OneShot s
  | n, .performed op v s k => v.OneShot ∧ State.OneShot s ∧
      if op = Operation.resume then
        0 < n ∧ ∀ w x, w.OneShot → x.All Value.OneShot → Outcome.OneShot P (n - 1) (k w x)
      else ∀ w x, w.OneShot → x.All Value.OneShot → Outcome.OneShot P n (k w x)
  | _, .outOfFuel | _, .stuck => True

/-- From a one-shot state, `m` ends with at most `n` performances of `resume` on
each path, and with one-shot values and states. -/
def Eval.OneShot {α : Type} (n : Nat) (P : α → Prop) (m : Eval Copy.State α) : Prop :=
  ∀ s, State.OneShot s → Outcome.OneShot P n (m s)

namespace Outcome.OneShot

variable {α β : Type} {P : α → Prop} {Q : β → Prop}

/-- A rest taken at a one-shot value, one fewer `resume` left after one. -/
theorem rest {op : Operation} {n : Nat} {v : Value} {s : Copy.State} {k : Value → World → Outcome Copy.State α}
    (h : (Outcome.performed op v s k).OneShot P n) {w : Value} {x : World} (hw : w.OneShot)
    (hx : x.All Value.OneShot) :
    (k w x).OneShot P (if op = Operation.resume then n - 1 else n) := by
  obtain ⟨_, _, h⟩ := h
  split <;> rename_i hop <;> simp only [hop, ↓reduceIte] at h
  · exact h.2 w x hw hx
  · exact h w x hw hx

/-- A performance whose rests keep to the count. -/
theorem performed {op : Operation} {n : Nat} {v : Value} {s : Copy.State} {k : Value → World → Outcome Copy.State α}
    (hv : v.OneShot) (hs : State.OneShot s) (hn : op = Operation.resume → 0 < n)
    (hk : ∀ w x, w.OneShot → x.All Value.OneShot → (k w x).OneShot P (if op = Operation.resume then n - 1 else n)) :
    (Outcome.performed op v s k).OneShot P n := by
  refine ⟨hv, hs, ?_⟩
  split <;> rename_i hop
  · exact ⟨hn hop, fun w x hw hx => by simpa [hop] using hk w x hw hx⟩
  · exact fun w x hw hx => by simpa [hop] using hk w x hw hx

theorem mono {Q : α → Prop} (hPQ : ∀ a, P a → Q a) :
    ∀ {n m : Nat} {o : Outcome Copy.State α}, n ≤ m → o.OneShot P n → o.OneShot Q m
  | _, _, .done _ _, _, h => ⟨hPQ _ h.1, h.2⟩
  | _, _, .performed op _ _ _, hnm, h => by
    refine performed h.1 h.2.1 (fun hop => ?_) fun w x hw hx => mono hPQ ?_ (h.rest hw hx)
    · have h' := h.2.2
      simp only [hop, ↓reduceIte] at h'
      omega
    · split <;> omega
  | _, _, .raised _ _, _, h | _, _, .jumped _ _, _, h | _, _, .panicked _ _, _, h
  | _, _, .outOfFuel, _, h | _, _, .stuck, _, h => h

/-- What follows each value an outcome reaches, with at most `b` performances of
`resume` of its own. -/
theorem bind {f : α → Copy.State → Outcome Copy.State β} {b : Nat}
    (hf : ∀ a s, P a → State.OneShot s → (f a s).OneShot Q b) :
    ∀ {a : Nat} {o : Outcome Copy.State α}, o.OneShot P a → (o.bind f).OneShot Q (a + b)
  | _, .done x s, h => (hf x s h.1 h.2).mono (fun _ h => h) (by omega)
  | a, .performed op _ _ _, h => by
    have h' := h.2.2
    refine performed h.1 h.2.1 (fun hop => ?_) fun w x hw hx => ?_
    · simp only [hop, ↓reduceIte] at h'; omega
    · have := bind hf (h.rest hw hx)
      split <;> rename_i hop
      · simp only [hop, ↓reduceIte] at h'
        exact this.mono (fun _ h => h) (by simp only [hop, ↓reduceIte]; omega)
      · simpa [hop] using this
  | _, .raised _ _, h | _, .jumped _ _, h | _, .panicked _ _, h | _, .outOfFuel, h | _, .stuck, h => h

/-- A raise handed to a handler with at most `b` performances of `resume`. -/
theorem handle {h : Value → Copy.State → Outcome Copy.State α} {b : Nat}
    (hh : ∀ e s, e.OneShot → State.OneShot s → (h e s).OneShot P b) :
    ∀ {a : Nat} {o : Outcome Copy.State α}, o.OneShot P a → (o.handle h).OneShot P (a + b)
  | _, .raised e s, h' => (hh e s h'.1 h'.2).mono (fun _ h => h) (by omega)
  | a, .performed op _ _ _, h' => by
    have h'' := h'.2.2
    refine performed h'.1 h'.2.1 (fun hop => ?_) fun w x hw hx => ?_
    · simp only [hop, ↓reduceIte] at h''; omega
    · have := handle hh (h'.rest hw hx)
      split <;> rename_i hop
      · simp only [hop, ↓reduceIte] at h''
        exact this.mono (fun _ h => h) (by simp only [hop, ↓reduceIte]; omega)
      · simpa [hop] using this
  | _, .done _ _, h' => ⟨h'.1, h'.2⟩
  | _, .jumped _ _, h' | _, .panicked _ _, h' | _, .outOfFuel, h' | _, .stuck, h' => h'

theorem turn {R : Value → Prop} :
    ∀ {n : Nat} {o : Outcome Copy.State Value}, o.OneShot R n → o.turn.OneShot (fun _ => True) n
  | _, .done _ _, h => ⟨trivial, h.2⟩
  | _, .jumped .brk _, h => ⟨trivial, h.2⟩
  | _, .jumped .cont _, h => ⟨trivial, h.2⟩
  | _, .jumped (.ret _) _, h => h
  | _, .performed _ _ _ _, h => performed h.1 h.2.1 (fun hop => by
      have := h.2.2; simp only [hop, ↓reduceIte] at this; exact this.1) fun _ _ hw hx => turn (h.rest hw hx)
  | _, .raised _ _, h | _, .panicked _ _, h | _, .outOfFuel, h | _, .stuck, h => h

/-- A scope's end, which drops its binding from every frame. -/
theorem unbind (w : WriteBack) :
    ∀ {n : Nat} {o : Outcome Copy.State α}, o.OneShot P n → (o.unbind (Copy.memoryWith w)).OneShot P n
  | _, .done _ _, h => ⟨h.1, Frame.OneShot.tail h.2.1, h.2.2⟩
  | _, .raised _ _, h => ⟨h.1, Frame.OneShot.tail h.2.1, h.2.2⟩
  | _, .jumped _ _, h => ⟨h.1, Frame.OneShot.tail h.2.1, h.2.2⟩
  | _, .panicked _ _, h => ⟨Frame.OneShot.tail h.1, h.2⟩
  | _, .performed _ _ _ _, h => performed h.1 ⟨Frame.OneShot.tail h.2.1.1, h.2.1.2⟩ (fun hop => by
      have := h.2.2; simp only [hop, ↓reduceIte] at this; exact this.1) fun _ _ hw hx => unbind w (h.rest hw hx)
  | _, .outOfFuel, h | _, .stuck, h => h

/-- A clause's outcome as the `with`'s, from a one-shot state. -/
theorem lift (w : WriteBack) {s : Copy.State} (hs : State.OneShot s) :
    ∀ {n : Nat} {o : Outcome Copy.State α}, o.OneShot P n → (o.lift (Copy.memoryWith w) s).OneShot P n
  | _, .done _ _, h => ⟨h.1, hs.1, h.2.2⟩
  | _, .raised _ _, h => ⟨h.1, hs.1, h.2.2⟩
  | _, .jumped _ _, h => ⟨h.1, hs.1, h.2.2⟩
  | _, .panicked _ _, h => ⟨hs.1, h.2⟩
  | _, .performed _ _ _ _, h => performed h.1 ⟨hs.1, h.2.1.2⟩ (fun hop => by
      have := h.2.2; simp only [hop, ↓reduceIte] at this; exact this.1) fun _ _ hw hx => lift w hs (h.rest hw hx)
  | _, .outOfFuel, h | _, .stuck, h => h

end Outcome.OneShot

end Stilt
