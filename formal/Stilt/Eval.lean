import Stilt.World

/-!
# Evaluation steps

How an evaluation ends, and the monad that the evaluator of `Stilt.Semantics`
is written in: a step goes from a state to an outcome. A raise, a panic and
running out of fuel skip the steps after them, and a handler takes over from a
raise (effects.innermost-catch). A performance carries the steps after it in
its rest, which goes on once a handler resumes it (handlers.performing-operation),
in the world the handler resumes it in.
-/

namespace Stilt

/-- A jump on its way to where it goes: `break` and `continue` to the innermost
loop whose body holds them, `return` with its value to the end of the function
or closure whose body holds it (expressions.break-and-continue and
expressions.closure-boundaries). -/
inductive Jump where
  | brk
  | cont
  | ret (value : Value)

/-- How an evaluation ends: with a value, with a raise on its way to a
`catch`, with a jump on its way to its loop or its function, with a panic, with
a performance on its way to its handler, or short of fuel. A value, a raise, a
jump, a panic and a performance come with the state at that point, since neither a raise nor a panic undoes any change
(values.inout-arguments): a panic ends the process, and what the program wrote
before it, which the state holds, stays written (effects.panic-kinds). `stuck`
is an evaluation gone wrong, such as reading a field of an integer, which type
soundness rules out.

A performance of `op` on its argument (handlers.performing-operation) carries
the rest of the evaluation, from the value that resumes it and the world it
resumes in. The rest goes on from the frames the performance left, since a
handler's body reaches no place of the code it suspends
(handlers.resuming-keeps-exclusivity), and in the world the handler's body
left, which it may have written to (`Stilt.World`); the state it
carries is the one a handler that ends the `with` leaves, with every call
between ended as on a raise (handlers.call-that-handler-ends). -/
inductive Outcome (σ α : Type) where
  | done (value : α) (state : σ)
  | raised (error : Value) (state : σ)
  | jumped (jump : Jump) (state : σ)
  | panicked (kind : PanicKind) (state : σ)
  | performed (op : Operation) (arg : Value) (state : σ)
      (rest : Value → World → Outcome σ α)
  | outOfFuel
  | stuck

/-- The rest `f` after an outcome: a value goes on to `f`; a raise, a jump, a
panic and running out of fuel skip it; and a performance's rest goes on to it,
once resumed. -/
def Outcome.bind {σ α β : Type} : Outcome σ α → (α → σ → Outcome σ β) → Outcome σ β
  | .done a s, f => f a s
  | .raised e s, _ => .raised e s
  | .jumped j s, _ => .jumped j s
  | .panicked k s, _ => .panicked k s
  | .performed op v s k, f => .performed op v s fun w x => (k w x).bind f
  | .outOfFuel, _ => .outOfFuel
  | .stuck, _ => .stuck

/-- An outcome with a raise handed to `handler` (effects.innermost-catch), in a
performance's rest too. -/
def Outcome.handle {σ α : Type} : Outcome σ α → (Value → σ → Outcome σ α) → Outcome σ α
  | .raised e s, h => h e s
  | .performed op v s k, h => .performed op v s fun w x => (k w x).handle h
  | o, _ => o

/-- A loop body's outcome as its turn's: a `break` ends the loop, with
`false`, a `continue` ends the turn, and every other outcome is the body's
(expressions.break-and-continue). -/
def Outcome.turn {σ : Type} : Outcome σ Value → Outcome σ Bool
  | .done _ s' => .done true s'
  | .jumped .cont s' => .done true s'
  | .jumped .brk s' => .done false s'
  | .jumped (.ret v) s' => .jumped (.ret v) s'
  | .raised e s' => .raised e s'
  | .panicked k s' => .panicked k s'
  | .performed op v s' k => .performed op v s' fun w x => (k w x).turn
  | .outOfFuel => .outOfFuel
  | .stuck => .stuck

/-- A step after an outcome ends with a value only after a value. -/
theorem Outcome.bind_eq_done {σ α β : Type} {o : Outcome σ α} {f : α → σ → Outcome σ β} {b : β}
    {s : σ} (h : o.bind f = .done b s) : ∃ a s₁, o = .done a s₁ ∧ f a s₁ = .done b s := by
  cases o with
  | done a s₁ => exact ⟨a, s₁, rfl, h⟩
  | _ => cases h

/-- The outcome of a fault at a state. -/
def Outcome.fault {σ α : Type} : Fault → σ → Outcome σ α
  | .panic k, s => .panicked k s
  | .stuck, _ => .stuck

/-- A step of the evaluator: from a state, an outcome. -/
def Eval (σ α : Type) : Type := σ → Outcome σ α

namespace Eval

variable {σ α β : Type}

/-- Ends with a value and the state unchanged. -/
protected def pure (a : α) : Eval σ α := fun s => .done a s

/-- Runs `m`, then `f` on its value. A raise, a jump, a panic and running out
of fuel skip `f`. -/
protected def bind (m : Eval σ α) (f : α → Eval σ β) : Eval σ β := fun s =>
  (m s).bind fun a s' => f a s'

instance : Monad (Eval σ) where
  pure := Eval.pure
  bind := Eval.bind

/-- Ends with a fault. -/
def fail (f : Fault) : Eval σ α := fun s => .fault f s

/-- Ends short of fuel. -/
def outOfFuel : Eval σ α := fun _ => .outOfFuel

/-- Raises an error (effects.raise). -/
def throw (e : Value) : Eval σ α := fun s => .raised e s

/-- Ends with a value, or a fault. -/
def ofExcept (x : Except Fault α) : Eval σ α := fun s =>
  match x with
  | .ok a => .done a s
  | .error f => .fault f s

/-- Ends with a value read from the state, or a fault. -/
def inspect (f : σ → Except Fault α) : Eval σ α := fun s => ofExcept (f s) s

/-- Changes the state, or ends with a fault. -/
def update (f : σ → Except Fault σ) : Eval σ Unit := fun s =>
  match f s with
  | .ok s' => .done () s'
  | .error e => .fault e s

/-- Runs `m`, and if it raises, runs the handler on the error instead
(effects.innermost-catch). -/
def handle (m : Eval σ α) (handler : Value → Eval σ α) : Eval σ α := fun s =>
  (m s).handle fun e s' => handler e s'

/-- Jumps to where it goes (expressions.break-and-continue). -/
def jump (j : Jump) : Eval σ α := fun s => .jumped j s

/-- A turn of a loop's body: a `break` ends the loop, with `false`, a
`continue` ends the turn, and every other outcome is the body's
(expressions.break-and-continue). -/
def turn (m : Eval σ Value) : Eval σ Bool := fun s => (m s).turn

/-- Runs `body` on each element of a list, in order, until a turn ends the
loop (expressions.for-iterables). -/
def forEach (body : Value → Eval σ Bool) : List Value → Eval σ Unit
  | [] => pure ()
  | v :: vs => do
    if ← body v then forEach body vs else pure ()

end Eval

end Stilt
