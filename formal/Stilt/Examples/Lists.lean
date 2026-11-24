import Stilt.Maps

/-!
# Lists

The bounds of std.lists: `slice(start, end)` panics with `bounds` unless
`0 ≤ start ≤ end ≤ len`, `insert(i, x)` unless `0 ≤ i ≤ len`, and `remove(i)`
unless `0 ≤ i < len`; within them, each keeps the order of the other elements.
-/

namespace Stilt.Examples.Lists

private def xs : Value := .list [.int 1, .int 2, .int 3]
private def ints (ns : List Int) : Except Fault Value := .ok (.list (ns.map .int))
private def bounds : Except Fault Value := .error (.panic .bounds)

example : ListOp.slice.apply [xs, .int 1, .int 3] = ints [2, 3] := rfl
example : ListOp.slice.apply [xs, .int 3, .int 3] = ints [] := rfl
example : ListOp.slice.apply [xs, .int 2, .int 1] = bounds := rfl
example : ListOp.slice.apply [xs, .int 0, .int 4] = bounds := rfl
example : ListOp.insert.apply [xs, .int 3, .int 9] = ints [1, 2, 3, 9] := rfl
example : ListOp.insert.apply [xs, .int 0, .int 9] = ints [9, 1, 2, 3] := rfl
example : ListOp.insert.apply [xs, .int 4, .int 9] = bounds := rfl
example : ListOp.removeAt.apply [xs, .int 1] = ints [1, 3] := rfl
example : ListOp.removeAt.apply [xs, .int 3] = bounds := rfl
example : ListOp.removeAt.apply [xs, .int (-1)] = bounds := rfl

end Stilt.Examples.Lists
