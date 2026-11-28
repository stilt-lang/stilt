import Stilt.Typing.Tasks
import Stilt.Modes.ParDemands
import Stilt.Capabilities
import Stilt.Semantics

/-!
# The functions of `std.par`, views indexed, and capabilities

Runs of the forms of `std.par` in the sequential run (par.sequential-meaning): `par.map` gives the
values in order, `par.both` the pair, and `par.fold` combines in the tree of par.fold-tree, which
`10 * p + q`, not associative, shows. `v[i]` on a view reads the element of its part. Then E0431
(par.what-runs-in-parallel) on functions that capture a view or a shared value, and the fact
`console` (facts.capabilities), which a function has through a `print` it calls.
-/

namespace Stilt.Examples.Par

private def decls (fns : List FnDecl := []) : Decls := ⟨[], [], fns, [], [], [], [], []⟩

/-- What a run ends with, a value or a raise, and the output it wrote. -/
private def shown (D : Decls) (e : Expr) : Option (Value × String) :=
  match eval D Copy.memory 200 e ([], World.start "") with
  | .done v s | .raised v s => some (v, s.2.out)
  | _ => none

private def ints (ns : List Int) : Expr := .list .i64 (ns.map .int)

private def vals (ns : List Int) : Value := .list (ns.map .int)

/-- `|x| x * 2`. -/
private def double : Expr :=
  .closure [⟨.let, "x", .i64, none⟩] .i64 Row.pure (.op (.arith .mul .i64) [.var "x", .int 2])

/-- `par.map([1, 2, 3], |x| x * 2)` is `[2, 4, 6]`. -/
example : shown (decls) (.parMapOf "n" "g" "acc" "x" .i64 .i64 (ints [1, 2, 3]) double) =
    some (vals [2, 4, 6], "") := rfl

/-- `par.both(|| 1, || 2)` is `(1, 2)`. -/
example : shown (decls) (.parBothOf "a" "b" .i64 .i64 (.closure [] .i64 Row.pure (.int 1))
    (.closure [] .i64 Row.pure (.int 2))) =
    some (.tuple [.int 1, .int 2], "") := rfl

/-- `|p, q| 10 * p + q`. -/
private def digits : Expr :=
  .closure [⟨.let, "p", .i64, none⟩, ⟨.let, "q", .i64, none⟩] .i64 Row.pure
    (.op (.arith .add .i64) [.op (.arith .mul .i64) [.int 10, .var "p"], .var "q"])

/-- par.fold-tree: `fold([1, 2, 3], 0, f)` is `f(1, f(2, 3))`, and `fold([1, 2, 3, 4], 0, f)`
is `f(f(1, 2), f(3, 4))`; an empty list gives `empty`. -/
example : (shown (decls [FnDecl.foldTree]) (.parFoldOf "n" "d" "g" .i64 (ints [1, 2, 3]) (.int 0)
      digits),
    shown (decls [FnDecl.foldTree]) (.parFoldOf "n" "d" "g" .i64 (ints [1, 2, 3, 4]) (.int 0)
      digits),
    shown (decls [FnDecl.foldTree]) (.parFoldOf "n" "d" "g" .i64 (ints []) (.int 9) digits)) =
    (some (.int 33, ""), some (.int 154, ""), some (.int 9, "")) := rfl

/-- `v[1]` of `View.of([5, 6, 7], 1, 3)` is `7`. -/
example : shown (decls) (.letIn "v" (.view (.list .i64)) (.view [ints [5, 6, 7], .int 1, .int 3])
    (.form .viewIndex (.index (.op .copy [.var "v"]) (.int 1)))) = some (.int 7, "") := rfl

/-- `par.map(xs, |x| x + w.len())`, whose function captures `w`. -/
private def mapOver (w : Name) : Expr :=
  .parMapOf "n" "g" "acc" "x" .i64 .i64 (ints [1])
    (.closure [⟨.let, "x", .i64, none⟩] .i64 Row.pure (.var w))

/-- E0431: a function given to `par.map` that captures a view is `fixed`, one that captures a
shared value `contended`, and one that captures a list is neither. -/
example : ((mapOver "w").parDemandsMet (decls) [⟨.let, "w", .view (.list .i64), none⟩],
    (mapOver "c").parDemandsMet (decls) [⟨.let, "c", .shared .i64, none⟩],
    (mapOver "xs").parDemandsMet (decls) [⟨.let, "xs", .list .i64, none⟩]) =
    (false, false, true) := by decide

/-- `fn say() { print("hi") }`, and `fn quiet() -> i64 { 1 }`. -/
private def say : FnDecl :=
  ⟨"say", [], [], [], .unit, ⟨true, none, [], [], none⟩,
    .op (.world (.write false true)) [.op (.str "hi") []], {}⟩
private def quiet : FnDecl := ⟨"quiet", [], [], [], .i64, Row.pure, .int 1, {}⟩

/-- facts.capabilities: `say` has `console`, and so does code that names it; `quiet` has none. -/
example : ((decls [say, quiet]).caps .console, (decls [say, quiet]).caps .fs,
    (Expr.call (.fnRef "say" [] []) [] .unit).capFree (decls [say, quiet]) .console ["say"]) =
    (["say"], [], false) := by decide

end Stilt.Examples.Par
