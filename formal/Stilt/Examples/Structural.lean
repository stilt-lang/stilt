import Stilt.Structural

/-!
# Structural comparisons

The cases that traits.structural-calls and traits.floats name: a variant compares
first by its constructor's place in its type's declaration, so `None < Some(0)`
and `Ok(1) < Err(0)`; a shorter list comes before a longer one that starts with
it; different variants are unequal; and in `compare`, `-0.0` comes before `0.0`.
-/

namespace Stilt.Examples.Structural

private def orders : CtorOrders := [("Option", ["None", "Some"]), ("Result", ["Ok", "Err"])]

private def none : Value := .variant "Option" "None" []
private def some (k : Int) : Value := .variant "Option" "Some" [.int k]
private def ok (k : Int) : Value := .variant "Result" "Ok" [.int k]
private def err (k : Int) : Value := .variant "Result" "Err" [.int k]

example : Cmp.lt.values orders none (some 0) = true := by decide
example : Cmp.lt.values orders (ok 1) (err 0) = true := by decide
example : Cmp.eq.values orders none (some 0) = false := by decide
example : Cmp.lt.values orders (.list [.int 1]) (.list [.int 1, .int 0]) = true := by decide
example : Cmp.eq.values orders (.list [.int 1]) (.list [.int 1, .int 0]) = false := by decide
example : Cmp.lt.values orders (.tuple [.int 1, .int 9]) (.tuple [.int 2, .int 0]) = true := by
  decide

/-- `compare` orders `-0.0`, whose bits are only its sign, before `0.0`, and a
negative float before a positive one; Lean's floats are opaque to the kernel,
so these read the key of their bits: `-0.0` is `-1`, `0.0` is `0`, and the
next float below `-0.0` is `-2`. -/
example : FloatVal.totalKey.key 63 (2 ^ 63) = Option.some (-1) := by decide
example : FloatVal.totalKey.key 63 0 = Option.some 0 := by decide
example : FloatVal.totalKey.key 63 (2 ^ 63 + 1) = Option.some (-2) := by decide

end Stilt.Examples.Structural
