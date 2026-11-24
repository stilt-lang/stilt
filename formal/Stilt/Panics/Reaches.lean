import Stilt.Panics.Keeps

/-!
# The values a run reaches

An evaluation reaches a value and a state when it ends with them, or when it
performs an operation whose rest, resumed with some value in some world, reaches them
(handlers.performing-operation). What code knows when it goes on from a value,
the facts that tests give among it, holds at every value it reaches, since a
rest goes on from the state that the performance left: the handler's body
reaches no place of the code it suspends (handlers.resuming-keeps-exclusivity).
-/

namespace Stilt

/-- `o` reaches the value `a` in the state `s`. -/
inductive Outcome.Reaches {σ α : Type} : Outcome σ α → α → σ → Prop
  | done {a : α} {s : σ} : Outcome.Reaches (.done a s) a s
  | rest {op : Operation} {v : Value} {s : σ} {k : Value → World → Outcome σ α} (w : Value)
      (x : World) {a : α} {s' : σ} :
      Outcome.Reaches (k w x) a s' → Outcome.Reaches (.performed op v s k) a s'

namespace Outcome.Reaches

variable {σ α β : Type}

theorem of_eq {o : Outcome σ α} {a : α} {s : σ} (h : o = .done a s) : o.Reaches a s := h ▸ .done

theorem inv {a b : α} {s s' : σ} (h : (Outcome.done a s : Outcome σ α).Reaches b s') :
    b = a ∧ s' = s := by
  cases h
  exact ⟨rfl, rfl⟩

/-- A value that a step and what follows reach comes from one the step reaches. -/
theorem bind {f : α → σ → Outcome σ β} {b : β} {s'' : σ} :
    ∀ {o : Outcome σ α}, (o.bind f).Reaches b s'' → ∃ a s', o.Reaches a s' ∧ (f a s').Reaches b s''
  | .done a s, h => ⟨a, s, .done, h⟩
  | .performed _ _ _ _, .rest w x h => by
    obtain ⟨a, s', h₁, h₂⟩ := bind h
    exact ⟨a, s', .rest w x h₁, h₂⟩
  | .raised _ _, h | .jumped _ _, h | .panicked _ _, h | .outOfFuel, h | .stuck, h => by cases h

/-- What a scope's end reaches, its body reaches in a state with one more binding. -/
theorem unbind (M : Memory σ) {a : α} {s : σ} :
    ∀ {o : Outcome σ α}, (o.unbind M).Reaches a s → ∃ s', o.Reaches a s' ∧ s = M.unbind s'
  | .done _ _, .done => ⟨_, .done, rfl⟩
  | .performed _ _ _ _, .rest w x h => by
    obtain ⟨s', h₁, h₂⟩ := unbind M h
    exact ⟨s', .rest w x h₁, h₂⟩
  | .raised _ _, h | .jumped _ _, h | .panicked _ _, h | .outOfFuel, h | .stuck, h => by cases h

/-- A value that a run reaches, from a frame, keeps what the run keeps. -/
theorem keeps {W L : List Name} {P : α → Prop} {s₀ : Copy.Frame} {a : α} {s : Copy.State} :
    ∀ {o : Outcome Copy.State α}, o.Reaches a s → o.Keeps W L P s₀ → P a ∧ Frame.Keeps W L s₀ s.1
  | _, .done, h => h
  | _, .rest w x h, ⟨_, hk⟩ => keeps h (hk w x)

end Outcome.Reaches

theorem Eval.bind_reaches {σ α β : Type} {m : Eval σ α} {f : α → Eval σ β} {s s' : σ} {b : β}
    (h : ((m >>= f) s).Reaches b s') : ∃ a s₁, (m s).Reaches a s₁ ∧ (f a s₁).Reaches b s' :=
  Outcome.Reaches.bind h

theorem Eval.ofExcept_reaches {σ α : Type} {x : Except Fault α} {s s' : σ} {a : α}
    (h : (Eval.ofExcept x s).Reaches a s') : x = .ok a ∧ s' = s := by
  unfold Eval.ofExcept at h
  cases x with
  | ok b => obtain ⟨rfl, rfl⟩ := h.inv; exact ⟨rfl, rfl⟩
  | error f => cases f <;> cases h

/-- Reading and writing the world reaches what its function gives, on the same frame. -/
theorem Eval.world_reaches {τ : Type} {F : Frames τ} {f : World → Except Fault (Value × World)}
    {s s' : τ × World} {a : Value} (h : (Eval.world F.withWorld f s).Reaches a s') :
    f s.2 = .ok (a, s'.2) ∧ s'.1 = s.1 := by
  obtain ⟨fr, x⟩ := s
  cases hf : f x with
  | ok p =>
    rw [Eval.world_ok hf] at h
    obtain ⟨rfl, rfl⟩ := h.inv
    exact ⟨rfl, rfl⟩
  | error e =>
    rw [Eval.world_error hf] at h
    cases e <;> cases h

theorem Eval.pure_reaches {σ α : Type} {a b : α} {s s' : σ} (h : ((Pure.pure a : Eval σ α) s).Reaches b s') :
    b = a ∧ s' = s :=
  Outcome.Reaches.inv h

theorem Eval.asBool_reaches {σ : Type} {v : Value} {s s' : σ} {b : Bool}
    (h : (Eval.asBool v s).Reaches b s') : v = .bool b ∧ s' = s := by
  cases v <;> cases h
  exact ⟨rfl, rfl⟩

theorem Eval.asList_reaches {σ : Type} {v : Value} {s s' : σ} {vs : List Value}
    (h : (Eval.asList v s).Reaches vs s') : v = .list vs ∧ s' = s := by
  cases v <;> cases h
  exact ⟨rfl, rfl⟩

end Stilt
