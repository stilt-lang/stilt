/-!
# No deadlock among `when`s

shared.when-order and shared.locks: a `when` waits until it holds every value it names, all
at once, and a `when` whose block runs another is E0430, so a task never waits
while it holds a value. The model is a system of tasks, each with the `when`s
it has still to run, in order, each the list of the values it names, and the
values it holds, if it is inside a `when`. A task acquires all the values of
its next `when` in one step, once no task holds any of them, and its next step
is to release them, since its block runs no `when`. `no_deadlock` proves that a
system with a task that hasn't ended can always take a step: no deadlock. That a task
inside a `when` acquires nothing is, for the core calculus's sequential run, the promise
`Program.Locks.block`.
-/

namespace Stilt.Shared.Deadlock

/-- A shared value, by its identity. -/
abbrev Value := Nat

/-- A task: the values it holds, inside a `when`, and the `when`s it has still
to run, each the values it names. -/
structure Task where
  holding : Option (List Value)
  pending : List (List Value)

/-- A task has ended once it holds nothing and has no `when` left. -/
def Task.Done (t : Task) : Prop := t.holding = none ∧ t.pending = []

/-- What a task holds: nothing outside a `when`. -/
def Task.held (t : Task) : List Value := t.holding.getD []

/-- The values that no task of the system holds. -/
def Free (s : List Task) (vs : List Value) : Prop :=
  ∀ t ∈ s, ∀ v ∈ vs, v ∉ t.held

/-- A step of one task (shared.when and shared.locks). A `when` takes every value it names at
once, when all are free; a task inside a `when` runs no other, so it releases
what it holds before it takes anything else. -/
inductive Step : List Task → List Task → Prop
  | acquire (s : List Task) (i : Nat) (h : i < s.length) (vs : List Value)
      (rest : List (List Value)) :
      s[i] = ⟨none, vs :: rest⟩ → Free s vs →
      Step s (s.set i ⟨some vs, rest⟩)
  | release (s : List Task) (i : Nat) (h : i < s.length) (vs : List Value)
      (rest : List (List Value)) :
      s[i] = ⟨some vs, rest⟩ →
      Step s (s.set i ⟨none, rest⟩)

/-- A system that holds nothing has every value free. -/
theorem free_of_none {s : List Task} (h : ∀ t ∈ s, t.holding = none)
    (vs : List Value) : Free s vs := by
  intro t ht v _ hv
  simp [Task.held, h t ht] at hv

/-- No deadlock (shared.when-order): while a task hasn't ended, some task can step. A
task inside a `when` can release its values; when none is inside one, every
value is free, and a task with a `when` left takes all it names. -/
theorem no_deadlock (s : List Task) (h : ∃ t ∈ s, ¬ t.Done) :
    ∃ s', Step s s' := by
  by_cases hold : ∃ t ∈ s, t.holding ≠ none
  · obtain ⟨t, ht, hn⟩ := hold
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
    obtain ⟨vs, hvs⟩ := Option.ne_none_iff_exists'.mp hn
    have e : s[i] = ⟨s[i].holding, s[i].pending⟩ := rfl
    rw [hvs] at e
    exact ⟨_, Step.release s i hi vs s[i].pending e⟩
  · have idle : ∀ t ∈ s, t.holding = none := by
      intro t ht
      exact Classical.byContradiction fun hn => hold ⟨t, ht, hn⟩
    obtain ⟨t, ht, hd⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
    have hnone := idle _ ht
    cases hp : s[i].pending with
    | nil => exact absurd ⟨hnone, hp⟩ hd
    | cons vs rest =>
        have e : s[i] = ⟨s[i].holding, s[i].pending⟩ := rfl
        rw [hnone, hp] at e
        exact ⟨_, Step.acquire s i hi vs rest e (free_of_none idle vs)⟩

end Stilt.Shared.Deadlock
