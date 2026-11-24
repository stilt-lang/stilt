import Stilt.Guards.Theorem

/-!
# Guards and list patterns, run

The examples of patterns.guards, run by the evaluator: an or-pattern whose
first way fails the guard and whose second passes it, and two or-patterns in a
tuple, whose ways the guard sees with the leftmost one's alternatives varying
slowest, printing each time it runs. Then the arms of
patterns.guards-and-constants, which cover every integer but which the check
doesn't count, list patterns of each length the check counts, and a `for` over
pairs with an irrefutable pattern.
-/

namespace Stilt.Guards.Examples

open Expr

/-- `[x, ..] | [_, x, ..]`. -/
def firstOrSecond (x : Name) : Pat :=
  .or (.prefix [.bind x] none) (.prefix [.wild, .bind x] none)

/-- `match [5, 30] { [x, ..] | [_, x, ..] if x > 10 => x, _ => 0 }` takes the
second alternative, with `x` bound to `30`. -/
example :
    runMatch [] (.list [.int 5, .int 30])
      [⟨firstOrSecond "x", some (lt (num 10) (var "x")), var "x"⟩, ⟨.wild, none, num 0⟩] =
      .done (.int 30) [] := rfl

/-- `([x, ..] | [_, x, ..], [y, ..] | [_, y, ..]) if p(x, y)`, with a `p` that
prints its operands and is false: the guard sees the first element of each list,
then the first of the first list with the second of the second, then the second
of the first with each of the second, and the `match` takes the last arm. -/
example :
    runMatch [] (.tuple [.list [.int 1, .int 2], .list [.int 3, .int 4]])
      [⟨.tuple [firstOrSecond "x", firstOrSecond "y"],
          some (print (var "x") (print (var "y") (bool false))), num 1⟩,
        ⟨.wild, none, num 0⟩] =
      .done (.int 0) [.int 1, .int 3, .int 1, .int 4, .int 2, .int 3, .int 2, .int 4] := rfl

/-- `x if x > 0` and `x if x <= 0` cover every integer, but an arm with a guard
covers nothing for exhaustiveness (patterns.guards-and-constants), and neither
does a constant: the check rejects both matches, and accepts one with `_`. -/
example :
    exhaustive [⟨.bind "x", some (lt (num 0) (var "x")), unit⟩,
      ⟨.bind "x", some (lt (var "x") (num 1)), unit⟩] .int = false := rfl

example : exhaustive [⟨.const "YES" (.bool true), none, unit⟩, ⟨.bool false, none, unit⟩] .bool = false := rfl

example : exhaustive [⟨.bool true, none, unit⟩, ⟨.bool false, none, unit⟩] .bool = true := rfl

example :
    exhaustive [⟨.bind "x", some (lt (num 0) (var "x")), unit⟩, ⟨.wild, none, unit⟩] .int = true := rfl

/-- `match xs { [] => 0, [x] => x, [x, y, ..rest] => x + y }`. -/
def byLength : List Arm :=
  [⟨.list [], none, num 0⟩, ⟨.list [.bind "x"], none, var "x"⟩,
    ⟨.prefix [.bind "x", .bind "y"] (some "rest"), none, add (var "x") (var "y")⟩]

/-- Its arms cover every list (patterns.algorithm), and without `[x]` they
don't. -/
example : exhaustive byLength (.list .int) = true := rfl

example :
    exhaustive [⟨.list [], none, unit⟩, ⟨.prefix [.bind "x", .bind "y"] (some "rest"), none, unit⟩]
      (.list .int) = false := rfl

/-- So `run_sound` applies: on every list of integers, the `match` ends with an
integer. -/
example {v : Val} (hv : ValTy v (.list .int)) :
    ∃ r out, runMatch [] v byLength = .done r out ∧ ValTy r .int := by
  refine run_sound (Γ := []) (fuel := 256) (fun a ha => ?_) hv (fun _ _ h => nomatch h) rfl
  simp only [byLength, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact ⟨[], .list .nil, fun _ h => (nomatch h), .num⟩
  · exact ⟨_, .list (.cons .bind .nil), fun _ h => (nomatch h), .var rfl⟩
  · exact ⟨_, .prefixRest (.cons .bind (.cons .bind .nil)), fun _ h => (nomatch h),
      .add (.var rfl) (.var rfl)⟩

example : runMatch [] (.list [.int 4, .int 5, .int 6]) byLength = .done (.int 9) [] := rfl

/-- `[Some(true), ..]`, `[Some(false), ..]`, `[None, ..]` and `[]` cover the
lists of `Option<bool>`. -/
example :
    exhaustive [⟨.prefix [.some (.bool true)] none, none, unit⟩,
      ⟨.prefix [.some (.bool false)] none, none, unit⟩, ⟨.prefix [.none] none, none, unit⟩,
      ⟨.list [], none, unit⟩] (.list (.option .bool)) = true := rfl

/-- `rest` binds the remaining elements as a list. -/
example :
    runMatch [] (.list [.int 1, .int 2, .int 3])
      [⟨.prefix [.wild] (some "rest"), none, print (var "rest") unit⟩, ⟨.wild, none, unit⟩] =
      .done .unit [.list [.int 2, .int 3]] := rfl

/-- `for (a, b) in [(1, 2), (3, 4)] { print(a + b) }`. -/
example :
    runFor [] (.tuple [.bind "a", .bind "b"]) (print (add (var "a") (var "b")) unit)
      [.tuple [.int 1, .int 2], .tuple [.int 3, .int 4]] = .done .unit [.int 3, .int 7] := rfl

end Stilt.Guards.Examples
