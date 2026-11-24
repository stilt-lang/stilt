import Stilt.Run.Program

/-!
# `stilt-model`

Runs a program that the reference interpreter exports (`stilt-ref model`) in the
Lean model, and shows what the run shows as a process: its standard output, what
it writes to standard error and its exit status (program.exit-statuses), which is
2 for a program with errors (program.programs-with-errors). A
program the model can't decide, one whose run runs out of fuel or gets stuck,
whose models of memory disagree, or that isn't one of the calculus's, ends
with status 70 and says why; a run it declines, one that panics or that raises
a value it can't show, ends with status 77, which nothing else ends with.
-/

open Stilt Run

/-- The deepest nesting a run may reach, far beyond any test's. -/
def fuel : Nat := 1000000

/-- The status by which the model declines a program or a run, which the
conformance runner counts as neither passed nor failed (`just model`). -/
def declined : UInt32 := 77

def main (args : List String) : IO UInt32 := do
  let [path] := args | do
    IO.eprintln "usage: stilt-model PROGRAM.json"
    return 2
  let text ← IO.FS.readFile path
  -- program.programs-with-errors: a program with errors ends with status 2, however it ends.
  let erroneous := match Lean.Json.parse text with
    | .ok j => (j.getObjValAs? Bool "erroneous").toOption.getD false
    | .error _ => false
  let result : Except Problem Shown := do
    let json ← (Lean.Json.parse text).mapError Problem.fails
    let p ← (program json).mapError Problem.fails
    -- std.io: the input the run reads, which the world starts with.
    let input := (json.getObjValAs? String "input").toOption.getD ""
    run p input fuel
  match result with
  | .ok s =>
    IO.print s.stdout
    IO.eprint s.stderr
    return if erroneous then 2 else s.status
  | .error (.declines why) =>
    IO.eprintln s!"stilt-model: declined: {why}"
    return declined
  | .error (.fails why) =>
    IO.eprintln s!"stilt-model: {why}"
    return 70
