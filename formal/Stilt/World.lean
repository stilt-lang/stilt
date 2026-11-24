import Stilt.Values
import Stilt.StrNatives

/-!
# The world

What a run changes outside its frames: the output and standard error it has
written, the input it has yet to read (std.io), and a store of cells, each
holding a value of its type or taken while code holds it.

Every model of memory carries the world beside its frames (`Stilt.Memory`): a
call starts in its caller's world and its caller goes on in the world the call
ends in, however it ends, so nothing a body writes to the world is undone by a
raise or a panic (effects.panic-kinds). A performance's rest takes the world
it resumes in, so what a handler's body writes stays written however the body
ends (handlers.resuming-keeps-exclusivity).
-/

namespace Stilt

/-- A cell of the store: the type of the values it holds, its value, and whether a `when`
holds it (shared.when). -/
structure Cell where
  type : Ty
  value : Value
  held : Bool := false

/-- What a run changes outside its frames. -/
structure World where
  /-- The standard output written so far. -/
  out : String := ""
  /-- The standard error written so far. -/
  err : String := ""
  /-- The input not read yet. -/
  input : String := ""
  /-- The store of cells. -/
  cells : List Cell := []

/-- The world a program starts in: nothing written, and its whole input to read. -/
def World.start (input : String) : World := { input }

/-- The cells of a type, in the order they were made. -/
def World.cellsOf (w : World) (u : Ty) : List Cell := w.cells.filter fun c => c.type = u

/-- The cell a handle names: the `k`-th cell of type `u` (shared.std-sync). -/
def World.cell? (w : World) (u : Ty) (k : Nat) : Option Cell := (w.cellsOf u)[k]?

/-- The world with a new cell of type `u` holding `v`, which is the cell of that type
numbered by how many there were. -/
def World.push (w : World) (u : Ty) (v : Value) : World :=
  { w with cells := w.cells ++ [⟨u, v, false⟩] }

/-- The cells with `f` applied to the `k`-th one of type `u`. -/
def Cell.modifyOf (u : Ty) (f : Cell → Cell) : List Cell → Nat → List Cell
  | [], _ => []
  | c :: cs, k =>
    if c.type = u then
      match k with
      | 0 => f c :: cs
      | k + 1 => c :: Cell.modifyOf u f cs k
    else c :: Cell.modifyOf u f cs k

/-- The world with `f` applied to the cell a handle names. -/
def World.modify (w : World) (h : Ty × Nat) (f : Cell → Cell) : World :=
  { w with cells := Cell.modifyOf h.1 f w.cells h.2 }

/-- Takes the values of the cells the handles name, and holds the cells: if one of them is
held, or two handles name one cell, the `when` panics with `deadlock` before it holds
anything (shared.when-on-value-already-held). -/
def World.take (hs : List (Ty × Nat)) (w : World) : Except Fault (List Value × World) :=
  match hs.mapM fun h => w.cell? h.1 h.2 with
  | some cs =>
    if hs.Nodup ∧ cs.all (!·.held) then
      .ok (cs.map Cell.value, hs.foldl (fun x h => x.modify h fun c => { c with held := true }) w)
    else .error (.panic .deadlock)
  | none => .error (.panic .deadlock)

/-- Puts a value back in the cell a handle names, still held or let go (shared.when). -/
def World.put (w : World) (h : Ty × Nat) (v : Value) (held : Bool) : World :=
  w.modify h fun c => { c with value := v, held }

/-- Lets go of every cell of the second list held where the same cell of the first, an earlier
store, isn't: those after the earlier store's are new. -/
def Cell.letGo : List Cell → List Cell → List Cell
  | b :: bs, c :: cs => (if c.held && !b.held then { c with held := false } else c) :: Cell.letGo bs cs
  | [], cs => cs.map fun c => { c with held := false }
  | _ :: _, [] => []

/-- Lets go of every cell held in `w` that wasn't held in `before` (shared.when). -/
def World.letGo (before w : World) : World := { w with cells := Cell.letGo before.cells w.cells }

/-- What a run shows of a world: its standard output and its standard error. -/
structure Output where
  out : String
  err : String
  deriving DecidableEq, Repr

/-- The output and standard error of a world. -/
def World.output (w : World) : Output := ⟨w.out, w.err⟩

/-- What an operation on the world gives from its operands' values, and the world it
leaves (std.io, std.read-line and shared.std-sync). -/
def WorldOp.run : WorldOp → List Value → World → Except Fault (Value × World)
  | .write false newline, [.str s], w =>
    .ok (.unit, { w with out := w.out ++ s ++ if newline then "\n" else "" })
  | .write true newline, [.str s], w =>
    .ok (.unit, { w with err := w.err ++ s ++ if newline then "\n" else "" })
  | .readLine, [], w =>
    .ok (.list ((Str.nextLine w.input).map .str), { w with input := Str.afterLine w.input })
  | .readAll, [], w => .ok (.str w.input, { w with input := "" })
  | .sharedNew u, [v], w => .ok (.handle u (w.cellsOf u).length, w.push u v)
  | _, _, _ => .error .stuck

end Stilt
