import Stilt.InPlace.Steps

/-!
# Holding shared values in place

Both models of memory run a `when` alike: they read the same values of its names and put them
back in one world, and a `with` lets the same cells go. The cells keep safe values, since the
values put back are safe (shared.when).
-/

namespace Stilt.InPlace

variable {α : Type}

/-- Putting values back from states that agree: the same fault, or states that still agree,
the in-place one's variables unchanged. -/
theorem putBack_agrees (held : Bool) : ∀ (cells : List (Name × Ty × Nat)) {fr : Copy.State}
    {s : State × World}, AgreesIn fr s →
    (∃ e, Copy.memory.putBack held cells fr = .error e ∧
        InPlace.memory.putBack held cells s = .error e) ∨
      ∃ fr' s', Copy.memory.putBack held cells fr = .ok fr' ∧
        InPlace.memory.putBack held cells s = .ok s' ∧ AgreesIn fr' s' ∧ s'.1 = s.1
  | [], _, _, h => .inr ⟨_, _, rfl, rfl, h, rfl⟩
  | (x, c) :: rest, (f, w), (t, y), ⟨hag, hw, hsafe⟩ => by
    cases hw
    have hr : Copy.memory.read (f, w) x [] = InPlace.memory.read (t, w) x [] := hag.read x []
    simp only [Memory.putBack]
    rw [← hr]
    cases hv : Copy.memory.read (f, w) x [] with
    | error e => exact .inl ⟨e, rfl, rfl⟩
    | ok v =>
      have hsv : v.Safe := hag.read_safe (by exact hv)
      exact putBack_agrees held rest (fr := (f, w.put c v held)) (s := (t, w.put c v held))
        ⟨hag, rfl, hsafe.put c hsv held⟩

theorem Corr.after {G : α → Prop} {held : Bool} {cells : List (Name × Ty × Nat)} {s₀ : State}
    {fr : Copy.State} {s : State × World} (hs : AgreesIn fr s) (hev : Evolves s₀ s.1)
    {o : Copy.State → Outcome Copy.State α} {o' : State × World → Outcome (State × World) α}
    (ho : ∀ fr' s', AgreesIn fr' s' → s'.1 = s.1 → Corr G s₀ (o fr') (o' s')) :
    Corr G s₀ (Outcome.after (Copy.memory.putBack held cells) fr o)
      (Outcome.after (InPlace.memory.putBack held cells) s o') := by
  unfold Outcome.after
  rcases putBack_agrees held cells hs with ⟨e, h₁, h₂⟩ | ⟨fr', s', h₁, h₂, hag, h₁₂⟩
  · rw [h₁, h₂]
    cases e
    · exact ⟨rfl, hs, hev⟩
    · trivial
  · rw [h₁, h₂]
    exact ho fr' s' hag h₁₂

/-- A `when`'s block in both models, its names' values put back however it ends. -/
theorem Corr.release {G : α → Prop} (cells : List (Name × Ty × Nat)) {s₀ : State} :
    ∀ {o : Outcome Copy.State α} {o' : Outcome (State × World) α}, Corr G s₀ o o' →
      Corr G s₀ (o.release Copy.memory cells) (o'.release InPlace.memory cells)
  | .done _ _, .done _ _, ⟨rfl, hG, hag, hev⟩ =>
    Corr.after hag hev fun _ _ hag' h => ⟨rfl, hG, hag', h ▸ hev⟩
  | .raised _ _, .raised _ _, ⟨rfl, he, hag, hev⟩ =>
    Corr.after hag hev fun _ _ hag' h => ⟨rfl, he, hag', h ▸ hev⟩
  | .jumped _ _, .jumped _ _, ⟨rfl, hj, hag, hev⟩ =>
    Corr.after hag hev fun _ _ hag' h => ⟨rfl, hj, hag', h ▸ hev⟩
  | .panicked _ _, .panicked _ _, ⟨rfl, hag, hev⟩ =>
    Corr.after hag hev fun _ _ hag' h => ⟨rfl, hag', h ▸ hev⟩
  | .performed _ _ _ _, .performed _ _ _ _, ⟨⟨rfl, rfl, hv, hag, hev⟩, hk⟩ =>
    Corr.after hag hev fun _ _ hag' h =>
      ⟨⟨rfl, rfl, hv, hag', h ▸ hev⟩, fun w x w' x' hw => Corr.release cells (hk w x w' x' hw)⟩
  | .outOfFuel, .outOfFuel, _ | .stuck, .stuck, _ => trivial

/-- A `with` in both models, letting go of the same cells. -/
theorem Corr.letGo {G : α → Prop} (before : World) {s₀ : State} :
    ∀ {o : Outcome Copy.State α} {o' : Outcome (State × World) α}, Corr G s₀ o o' →
      Corr G s₀ (o.letGo Copy.memory before) (o'.letGo InPlace.memory before)
  | .done _ (_, _), .done _ (_, _), ⟨rfl, hG, ⟨hag, rfl, hx⟩, hev⟩ =>
    ⟨rfl, hG, ⟨hag, rfl, hx.letGo before⟩, hev⟩
  | .raised _ (_, _), .raised _ (_, _), ⟨rfl, he, ⟨hag, rfl, hx⟩, hev⟩ =>
    ⟨rfl, he, ⟨hag, rfl, hx.letGo before⟩, hev⟩
  | .jumped _ (_, _), .jumped _ (_, _), ⟨rfl, hj, ⟨hag, rfl, hx⟩, hev⟩ =>
    ⟨rfl, hj, ⟨hag, rfl, hx.letGo before⟩, hev⟩
  | .panicked _ (_, _), .panicked _ (_, _), ⟨rfl, ⟨hag, rfl, hx⟩, hev⟩ =>
    ⟨rfl, ⟨hag, rfl, hx.letGo before⟩, hev⟩
  | .performed _ _ _ _, .performed _ _ _ _, ⟨h, hk⟩ =>
    ⟨h, fun w x w' x' hw => Corr.letGo before (hk w x w' x' hw)⟩
  | .outOfFuel, .outOfFuel, _ | .stuck, .stuck, _ => trivial

namespace Sim

theorem letGo {G : α → Prop} {m : Eval Copy.State α} {m' : Eval (State × World) α} (hm : Sim G m m') :
    Sim G (Eval.letGo Copy.memory m) (Eval.letGo InPlace.memory m') := by
  intro fr s hs
  show Corr G s.1 ((m fr).letGo Copy.memory fr.2) ((m' s).letGo InPlace.memory s.2)
  rw [hs.2.1]
  exact Corr.letGo s.2 (hm fr s hs)

/-- A `when` in both models (shared.when). -/
theorem held {m : Eval Copy.State Value} {m' : Eval (State × World) Value} (hm : Sim Value.Safe m m')
    (names : List Name) (vs : List Value) :
    Sim Value.Safe (Eval.held Copy.memory m names vs) (Eval.held InPlace.memory m' names vs) := by
  unfold Eval.held
  refine bind (G := fun _ => True) (ofExcept _ fun _ _ => trivial) fun cells _ => ?_
  refine bind (bind (world _ fun x v x' hx h => ?_) fun _ hv => asList hv) fun us hus => ?_
  · cases ht : World.take cells x with
    | error e => rw [ht] at h; cases h
    | ok p =>
      rw [ht] at h
      cases h
      obtain ⟨hp, hx'⟩ := hx.take ht
      exact ⟨.list hp, hx'⟩
  · split
    · exact withVars (fun fr s hs => Corr.release _ (hm fr s hs)) _
        fun xv hxv => hus _ (List.of_mem_zip hxv).2
    · exact fail _

end Sim

end Stilt.InPlace
