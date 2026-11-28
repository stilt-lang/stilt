/-!
# The forms of the calculus

The forms of the Reference that the calculus keeps with the code they mean (`Expr.form`): those
whose typing has rules of its own, those of projections (`Stilt.Projections`), those of
writable views (`Stilt.Writable`) and those of tasks, scopes and lazy values
(`Stilt.Typing.Tasks`), and those whose meaning has a shape of its own (`Form.Shaped`).
-/

namespace Stilt

/-- A form of the Reference whose typing has rules of its own beside those of the `match`
it means, which `Expr.form` keeps with it: `let P = e else x` with a refutable `P`, a
let-else (patterns.let-else), and `e₁ else e₂`, the `Option` fallback
(expressions.option-fallback). -/
inductive Form where
  | letElse
  | orElse
  /-- A projection's body, written for one type of its access (`Expr.projectionBody`). -/
  | projection
  /-- `yield p`, the access called with `p` `inout` (`Expr.yieldOf`). -/
  | yield
  /-- The access's value, which the body ends with and its `return` gives (`Expr.yieldedOf`). -/
  | yielded
  /-- A projection's call where a place is (projections.call-is-place, `Expr.projectCall`). -/
  | project
  /-- A writable binding and the rest of its block, written as a call of a closure literal that
  takes the binding's source `inout` (`Stilt.Writable`): `var v = view.into(inout xs, a, b)`, or
  `view.part(inout w, a, b)` of a writable binding `w`, its offsets counted from `w`'s start, once
  the offsets are checked as `View.of` checks them, which panics with `bounds`; `view.split`'s two
  parts are copies, which its function takes as writable bindings (projections.writable-views). -/
  | writes
  /-- An index of a place through a writable binding, `v[i]`: the index into its source, or `-1`
  when it lies outside the binding's part (`Expr.throughOf`). So `v[i]` is a place of the source's
  parameter, which can be assigned to, passed `inout` and be the receiver of a method that takes
  `inout self`, and whose access panics with `bounds` past the part's end as a read of `v[i]`
  does; a view made from `v` has that parameter as its source, so a change through `v` while it
  lives is E0423 (projections.places-through-views). -/
  | through
  /-- `place op= e` (`Expr.Compound`), an integer literal at a float type, and `e.f` through an
  `Option` (`Form.Shaped`). -/
  | compound | intFloat | optionField
  /-- `{ ..base, f: e }`, a record update (`Expr.Update`). -/
  | update
  /-- `task.spawn(f)`, which runs the task's function to its end (`Expr.spawnOf`). -/
  | spawn
  /-- `t.await()`, the value the task ended with (`Expr.awaitOf`). -/
  | await
  /-- `task.scope(f)`, `f` called with a new scope (`Expr.scopeOf`). -/
  | scope
  /-- `s.spawn(f)`, a task of a scope, which may raise (`Expr.scopeSpawnOf`). -/
  | scopeSpawn
  /-- A `with` of a handler of `async`, its block's run (`Expr.asyncWith`). -/
  | async
  /-- `Lazy.new(f)`, the lazy value that keeps `f` (`Expr.lazyNewOf`). -/
  | lazyNew
  /-- `l.get()`, the value of the function a lazy value keeps (`Expr.lazyGetOf`). -/
  | lazyGet
  deriving DecidableEq, Repr

end Stilt
