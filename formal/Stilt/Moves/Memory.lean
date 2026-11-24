import Stilt.Semantics

/-!
# Moving

A third model of memory, `Moving`: in-place mutation in which the last use of
a variable hands its storage over instead of copying it (values.passing-values).

* `let y = move x` and `var y = move x` make `y` refer to the part of the
  store that `x` refers to.
* A call passes an argument `move x` as the place of `x`, as it passes an
  `inout` argument, so the callee's parameter refers to the caller's storage
  and the callee changes it where it is. Nothing is written back, as nothing
  is in place.

Every other operation is in-place mutation's. `Stilt.Moves.Theorem` proves
that on a program whose marks are last uses, `Moving` and copy-in, copy-out
give the same observation.
-/

namespace Stilt

namespace Moving

open InPlace

/-- An argument as `Moving` passes it: the last use of a variable as that
variable's place (values.passing-values), any other argument as it is. -/
def handOver : Name × Passed → Name × Passed
  | (y, .moved x _) => (y, .place x [])
  | ya => ya

/-- Binds `y` to the storage of `x`, whose last use gives its value: `y`
refers to the part of the store that `x` refers to, and nothing is copied
(values.consumed-parameters). -/
def bindMoved (s : State) (y x : Name) (v : Value) : State :=
  match s.env.lookup x with
  | some r => { s with env := (y, r) :: s.env }
  | none => InPlace.bind s y v

/-- The frames of the model in which last uses hand their storage over. -/
def frames : Frames State where
  read := InPlace.read
  write := InPlace.write
  bind := InPlace.bind
  bindMoved := bindMoved
  unbind s := { s with env := s.env.tail }
  capture s := s.env.mapM fun (x, r) => (x, ·) <$> deref s r []
  enter caller captured params := InPlace.enter caller captured (params.map handOver)
  leave caller callee _ := pure { caller with store := callee.store }

/-- The model in which last uses hand their storage over. -/
def memory : Memory (State × World) := frames.withWorld

end Moving

/-- Runs `main` with last uses handing their storage over. -/
def Program.runMoving (p : Program) (fuel : Nat) (input : String := "") :
    Outcome (InPlace.State × World) Value :=
  p.run Moving.memory (⟨[], []⟩, World.start input) fuel

end Stilt
