import Stilt.Eval
import Stilt.Memory

/-!
# Handling performances

What a `with` does with the performances that reach it (handlers.with). A
handler is a record of closures, one for each operation of its effect, under
the operation's name. A performance of the handler's effect calls the closure
of its operation on the performance's argument, from the state the performance
left; any other performance goes on outward. The handler is installed again
around the rest of the block when it is resumed, so it is deep.

A handler written `handler E { … }` resumes the performance with the value its
body ends with (handlers.resuming). One written `handler E -> R { … }` takes
control: its body's value is the `with`'s, and `resume(v)` in it, a
performance of the reserved operation `Operation.resume`, runs the rest of the
block under the handler and gives the body the value that rest ends with; the
body then goes on, and whatever it ends with comes after the rest of the block,
on the frames the rest left, since the body reaches no place of the block
(handlers.resuming-keeps-exclusivity), in the world the body left. So what a
body writes to the world stays written however it ends. A body that never resumes ends the
`with` from the state the performance left, every call between ended as on a
raise (handlers.call-that-handler-ends).
-/

namespace Stilt

variable {σ α : Type}

/-- An outcome of a handler's body as the `with`'s, on the frames of the state
`s` the rest of the block left: the body reached no place of the block, so the
frames are the block's, and the world is the one the body ended in. -/
def Outcome.lift (M : Memory σ) (s : σ) : Outcome σ α → Outcome σ α
  | .done a s' => .done a (M.setWorld s (M.world s'))
  | .raised e s' => .raised e (M.setWorld s (M.world s'))
  | .jumped j s' => .jumped j (M.setWorld s (M.world s'))
  | .panicked k s' => .panicked k (M.setWorld s (M.world s'))
  | .performed op v s' k => .performed op v (M.setWorld s (M.world s')) fun w x => (k w x).lift M s
  | .outOfFuel => .outOfFuel
  | .stuck => .stuck

/-- The outcome of the body of a handler that takes control: each `resume(v)`
runs `resume v x`, the rest of the block under the handler in the body's world
`x`, and the body goes on from the value that rest ends with, in the world it
left, after it; every other performance goes on outward (handlers.resuming). -/
def Outcome.runBody (M : Memory σ) (resume : Value → World → Outcome σ Value) :
    Outcome σ Value → Outcome σ Value
  | .performed op u s k =>
    if op = Operation.resume then
      (resume u (M.world s)).bind fun r s' => ((k r (M.world s')).runBody M resume).lift M s'
    else .performed op u s fun w x => (k w x).runBody M resume
  | o => o

/-- The clause of a handler for an operation: the field of that name. -/
def Value.clause? : Value → Name → Option Value
  | .record _ fields, op => fields.lookup op
  | _, _ => none

/-- The outcome of a `with`'s block, its performances of `effect` handled by
`handler`, which takes control when `control` holds; `call c v s` calls the
clause `c` on the argument `v` from the state `s` (handlers.with). A resuming
clause's value resumes the rest in the world the clause's call ended in. -/
def Outcome.handleWith (M : Memory σ) (effect : Name) (control : Bool) (handler : Value)
    (call : Value → Value → σ → Outcome σ Value) : Outcome σ Value → Outcome σ Value
  | .performed op v s k =>
    if op.effect = effect then
      match handler.clause? op.name with
      | none => .stuck
      | some c =>
        if control then
          (call c v s).runBody M fun u x => (k u x).handleWith M effect control handler call
        else (call c v s).bind fun w s' => (k w (M.world s')).handleWith M effect control handler call
    else .performed op v s fun w x => (k w x).handleWith M effect control handler call
  | o => o

namespace Eval

variable {σ : Type}

/-- Performs `op` on `v`: the rest, once resumed with a value in a world, gives
the value from the frames the performance left, in that world
(handlers.performing-operation). -/
def perform (M : Memory σ) (op : Operation) (v : Value) : Eval σ Value := fun s =>
  .performed op v s fun w x => .done w (M.setWorld s x)

/-- Runs `m` with `handler` installed for `effect` (handlers.with). -/
def handleWith (M : Memory σ) (effect : Name) (control : Bool) (handler : Value)
    (call : Value → Value → Eval σ Value) (m : Eval σ Value) : Eval σ Value := fun s =>
  (m s).handleWith M effect control handler call

end Eval

end Stilt
