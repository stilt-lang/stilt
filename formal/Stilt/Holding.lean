import Stilt.Eval
import Stilt.Memory

/-!
# Holding shared values

What a `when` does to the cells it holds once its block ends, and what a `with` does
to the cells held by the rest of its block that its handler drops (shared.when).

A `when` binds each of its names to the value of its cell and holds the cell. However
its block ends, with a value, a raise, a jump or a panic, it puts the value of each name
back in its cell and lets the cell go (`Outcome.release`). A performance that leaves the
block puts each value back too, the cell still held, so that a handler's body finds the
cell held, and the rest of the block goes on with its names once resumed. A `with` whose
handler ends it without resuming the rest of its block lets go of every cell that a `when`
in that rest holds (`Outcome.letGo`), each keeping the value put back when the
performance left the block: a value keeps what its place holds when the block ends,
however it ends.
-/

namespace Stilt

variable {σ α : Type}

/-- The cell a value names, if it is a handle (shared.std-sync). -/
def Value.cellOf : Value → Except Fault (Ty × Nat)
  | .handle u k => .ok (u, k)
  | _ => .error .stuck

/-- Puts the value of each name back in its cell, still held or let go (shared.when). -/
def Memory.putBack (M : Memory σ) (held : Bool) : List (Name × Ty × Nat) → σ → Except Fault σ
  | [], s => .ok s
  | (x, h) :: rest, s => do
    let v ← M.read s x []
    M.putBack held rest (M.setWorld s ((M.world s).put h v held))

/-- The outcome of a state that a step `f` gives, or the fault it ends with. -/
def Outcome.after (f : σ → Except Fault σ) (s : σ) (o : σ → Outcome σ α) : Outcome σ α :=
  match f s with
  | .ok s' => o s'
  | .error e => .fault e s

/-- The outcome of a `when`'s block, with each name's value put back in its cell however
the block ends: let go at its end, and still held when a performance leaves the block,
whose rest, once resumed, ends the same way (shared.when). -/
def Outcome.release (M : Memory σ) (cells : List (Name × Ty × Nat)) : Outcome σ α → Outcome σ α
  | .done a s => Outcome.after (M.putBack false cells) s (.done a)
  | .raised e s => Outcome.after (M.putBack false cells) s (.raised e)
  | .jumped j s => Outcome.after (M.putBack false cells) s (.jumped j)
  | .panicked k s => Outcome.after (M.putBack false cells) s (.panicked k)
  | .performed op v s k =>
    Outcome.after (M.putBack true cells) s fun s' =>
      .performed op v s' fun w x => (k w x).release M cells
  | .outOfFuel => .outOfFuel
  | .stuck => .stuck

/-- The outcome of a `with`, which lets go of every cell held when it ends that wasn't held
when it started: the cells of the `when`s in a rest of its block that its handler dropped
(shared.when). -/
def Outcome.letGo (M : Memory σ) (before : World) : Outcome σ α → Outcome σ α
  | .done a s => .done a (M.setWorld s (before.letGo (M.world s)))
  | .raised e s => .raised e (M.setWorld s (before.letGo (M.world s)))
  | .jumped j s => .jumped j (M.setWorld s (before.letGo (M.world s)))
  | .panicked k s => .panicked k (M.setWorld s (before.letGo (M.world s)))
  | .performed op v s k => .performed op v s fun w x => (k w x).letGo M before
  | .outOfFuel => .outOfFuel
  | .stuck => .stuck

/-- Putting values back changes no frame. -/
theorem Frames.putBack_frame {τ : Type} (F : Frames τ) (held : Bool) :
    ∀ (cells : List (Name × Ty × Nat)) {s s' : τ × World},
      F.withWorld.putBack held cells s = .ok s' → s'.1 = s.1
  | [], _, _, h => by cases h; rfl
  | (x, c) :: rest, (fr, w), s', h => by
    simp only [Memory.putBack] at h
    cases hr : F.withWorld.read (fr, w) x [] with
    | error e => rw [hr] at h; cases h
    | ok v =>
      rw [hr] at h
      exact Frames.putBack_frame F held rest (s := (fr, w.put c v held)) h

namespace Eval

/-- Runs a `with` and lets go of the cells that the rest of its block, dropped, holds. -/
def letGo (M : Memory σ) (m : Eval σ α) : Eval σ α := fun s => (m s).letGo M (M.world s)

/-- Runs a `when`'s block, and puts back the values of its names however it ends. -/
def release (M : Memory σ) (cells : List (Name × Ty × Nat)) (m : Eval σ α) : Eval σ α :=
  fun s => (m s).release M cells

end Eval

end Stilt
