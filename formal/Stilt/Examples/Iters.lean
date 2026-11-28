import Stilt.Typing.Tasks
import Stilt.Semantics

/-!
# Iterators

Runs of the functions of iterators as the export declares them (views.making-iterator,
views.adapters, views.laziness and views.consumers): adapters over a list and a range, read by
consumers, and the order in which the adapters ask, which `views/laziness.lt` shows: `take(1)`
asks for no second element, every consumer starts from the first, and an element passes
through `map` and then `filter` before the next is asked for.
-/

namespace Stilt.Examples.Iters

open Iter

private def decls : Decls :=
  ⟨[⟨iterName, [("next", Ty.iterNext (.param "T"))], ["T"]⟩],
    [⟨optionName, [("None", []), ("Some", [.param "T"])], ["T"]⟩],
    IterFn.every.map IterFn.decl, [], [], [], [], []⟩

/-- What a run ends with: its value, or the kind of its panic. -/
private def run (e : Expr) : Option (Value ⊕ PanicKind) :=
  match eval decls Copy.memory 400 e ([], World.start "") with
  | .done v _ => some (.inl v)
  | .panicked k _ => some (.inr k)
  | _ => none

private def ints (ns : List Int) : Expr := .list .i64 (ns.map .int)

private def vals (ns : List Int) : Value := .list (ns.map .int)

/-- `Iter.of(xs)` at `i64`. -/
private def of (xs : List Int) : Expr := .iterOf .of [.i64] [] [.value (ints xs), .value (.int 0)] (Ty.iter .i64)

/-- An adapter `f` of an iterator of `i64`s, with its other arguments. -/
private def adapt (f : IterFn) (it : Expr) (args : List Expr) (τ : Ty := .i64) : Expr :=
  .iterOf f [.i64] [] ((it :: args).map .value) (Ty.iter τ)

/-- `it.collect()` and `it.count()`. -/
private def collect (it : Expr) : Expr := .iterOf .collect [.i64] [] [.value it] (.list .i64)
private def count (it : Expr) : Expr := .iterOf .count [.i64] [] [.value it] .i64

/-- `|x| e` on an `i64`. -/
private def fn (σ : Ty) (e : Expr) : Expr := .closure [⟨.let, "x", .i64, none⟩] σ Row.pure e

/-- `it.map(|x| x * 10)` of `[1, 2, 3]`, and `filter` of an even number of `view.range(0, 6)`. -/
example : run (collect (.iterOf .map [.i64, .i64] [] [.value (of [1, 2, 3]),
    .value (fn .i64 (.op (.arith .mul .i64) [.var "x", .int 10]))] (Ty.iter .i64))) =
    some (.inl (vals [10, 20, 30])) := rfl

example : run (collect (adapt .filter
    (.iterOf .range [] [] [.value (.int 0), .value (.int 6)] (Ty.iter .i64))
    [fn .bool (.op (.compare .eq .i64) [.op (.arith .rem .i64) [.var "x", .int 2], .int 0])])) =
    some (.inl (vals [0, 2, 4])) := rfl

/-- `take`, `skip` and `chain`. -/
example : (run (collect (adapt .take (of [1, 2, 3]) [.int 2])),
    run (collect (adapt .skip (of [1, 2, 3]) [.int 2])),
    run (collect (adapt .chain (of [1]) [of [2, 3]]))) =
    (some (.inl (vals [1, 2])), some (.inl (vals [3])), some (.inl (vals [1, 2, 3]))) := rfl

/-- `it` is `Iter.of([2, 0]).map(|x| 10 / x)`. -/
private def tenOver : Expr :=
  .iterOf .map [.i64, .i64] [] [.value (of [2, 0]),
    .value (fn .i64 (.op (.arith .div .i64) [.int 10, .var "x"]))] (Ty.iter .i64)

/-- views.laziness: `it.take(1)` asks for no second element, whose `map` would divide by zero, and
`count` of it starts from the first element again, after `collect` read it. -/
example : run (.letIn "it" (Ty.iter .i64) tenOver
    (.op .tuple [collect (adapt .take (.var "it") [.int 1]),
      count (adapt .take (.var "it") [.int 1]), count (adapt .take (.var "it") [.int 0])])) =
    some (.inl (.tuple [vals [5], .int 1, .int 0])) := rfl

/-- views.laziness: the first element goes through `map` and then `filter` before the second is
asked for, so `filter` panics with `bounds` before `map` divides by zero. -/
example : run (count (adapt .filter tenOver
    [fn .bool (.op (.compare .eq .i64) [.index (ints [1]) (.var "x"), .int 1])])) =
    some (.inr .bounds) := rfl

end Stilt.Examples.Iters
