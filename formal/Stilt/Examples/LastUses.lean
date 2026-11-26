import Stilt.Moves.Marking
import Stilt.Rows.Types

/-!
# Last uses

The check of last uses on the cases facts.last-use decides: a mark is a last
use when no use of its binding follows it in source order, a use inside a loop
that the binding's declaration is outside of is never one, and a use inside a
closure literal counts as a use at the literal. The check goes by bindings, so
a binder that reuses a name is no use of the binding it hides, and
`Expr.markMoves` marks each of these last uses.
-/

namespace Stilt.Examples.LastUses

/-- `f(e)`. -/
private def f (e : Expr) : Expr := .call (.fnRef "f" [] []) [.value e] .unit

/-- `|| { body }`. -/
private def thunk (body : Expr) : Expr := .closure [] .unit Row.pure body

/-- Whether every mark of a body is a last use. -/
private def ok (e : Expr) : Bool := e.movesOk .empty

/-- `loop { let y = 1; f(move y) }`: `y` is declared inside the loop. -/
example : ok (.loop (.letIn "y" .i64 (.int 1) (f (.move "y")))) = true := by decide +kernel

/-- `for x in [1] { f(move x) }`: each turn binds `x` again. -/
example : ok (.for "x" .i64 (.list .i64 [.int 1]) (f (.move "x"))) = true := by decide +kernel

/-- `f(move y); let y = 2; f(y)`: the later `y` is another binding. -/
example : ok (.seq (f (.move "y")) (.letIn "y" .i64 (.int 2) (f (.var "y")))) = true := by
  decide +kernel

/-- `f(move y); || { let y = 2; f(y) }`: the closure binds a `y` of its own. -/
example : ok (.seq (f (.move "y")) (thunk (.letIn "y" .i64 (.int 2) (f (.var "y"))))) = true := by
  decide +kernel

/-- `{ let x = 2; f(move x) }; f(x)`: the mark is the last use of the inner `x`,
and the use after the block is of the `x` it hides. -/
example : ok (.seq (.letIn "x" .i64 (.int 2) (f (.move "x"))) (f (.var "x"))) = true := by
  decide +kernel

/-- `try … catch y => f(move y)`, then `f(y)`: the arm's `y` hides the later one's. -/
example : ok (.seq (.tryCatch (.raise (.int 1)) .i64 "y" (f (.move "y")) .unit) (f (.var "y"))) =
    true := by decide +kernel

/-- The analysis marks the last use of a binding declared inside a loop. -/
example : Expr.markMoves .empty false (.loop (.letIn "y" .i64 (.int 1) (f (.var "y")))) =
    .loop (.letIn "y" .i64 (.int 1) (f (.move "y"))) := rfl

/-- The analysis marks the inner `x`, whose hidden outer `x` is used after the block. -/
example : Expr.markMoves .empty false
      (.seq (.letIn "x" .i64 (.int 2) (f (.var "x"))) (f (.var "x"))) =
    .seq (.letIn "x" .i64 (.int 2) (f (.move "x"))) (f (.move "x")) := rfl

/-- `f(move y); f(y)`: a use follows the mark. -/
example : ok (.seq (f (.move "y")) (f (.var "y"))) = false := by decide +kernel

/-- `loop { f(move y) }`: `y` is declared outside the loop. -/
example : ok (.loop (f (.move "y"))) = false := by decide +kernel

/-- `f(move y); || f(y)`: the closure literal uses `y`. -/
example : ok (.seq (f (.move "y")) (thunk (f (.var "y")))) = false := by decide +kernel

/-- `{ let x = move x; f(x) }; f(x)`: the initializer's `x` is the outer one,
used after the block. -/
example : ok (.seq (.letIn "x" .i64 (.move "x") (f (.var "x"))) (f (.var "x"))) = false := by
  decide +kernel

end Stilt.Examples.LastUses
