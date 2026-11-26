import Stilt.ViewReads
import Stilt.ViewContained

/-!
# The checks of views

The required tests of views.change-while-viewed (E0423) and views.escaping (E0422), as the
calculus writes them: `views/durations.lt` and `views/escaping.lt`, each
error on its own, and the programs that `views/durations_accepted.lt` and
`views/escaping_accepted.lt` accept. Every program of the conformance suite
that the export writes passes both checks.
-/

namespace Stilt.Examples.ViewChecks

/-- `type Doc = { lines: List<str>, n: i64 }` and `fn bump(inout xs: List<i64>)`. -/
private def decls : Decls :=
  ⟨[⟨"Doc", [("lines", .list .str), ("n", .i64)], []⟩], [],
    [⟨"bump", [], [], [⟨.inout, "xs", .list .i64, none⟩], .unit, Row.pure, .unit, {}⟩],
    [], [], [], []⟩

private def ints (ns : List Int) : Expr := .list .i64 (ns.map .int)

private def listTy : Ty := .list .i64

/-- `var xs = [1, 2, 3]`, then `rest`. -/
private def withXs (rest : Expr) : Expr := .varIn "xs" listTy (ints [1, 2, 3]) rest

/-- `let v = View.of(xs, 0, 2)`, then `rest`. -/
private def withView (rest : Expr) : Expr :=
  .letIn "v" (.view listTy) (.view [.var "xs", .int 0, .int 2]) rest

/-- `var d = Doc { lines: ["a"], n: 0 }` and `let w = View.all(d.lines)`, then `rest`. -/
private def withDoc (rest : Expr) : Expr :=
  .varIn "d" (.record "Doc" []) (.record "Doc" [] [("lines", .list .str [.op (.str "a") []]), ("n", .int 0)])
    (.letIn "w" (.view (.list .str)) (.view [.field (.var "d") "lines"]) rest)

/-- Whether a `main` passes the check of E0423. -/
private def reads (main : Expr) : Bool := main.viewsRead decls [] []

/-! ### E0423: a modification of a source while its view lives -/

/-- `xs[0] = 9` while `v` lives. -/
example : reads (withXs (withView (.assign ⟨"xs", [.index (.int 0)]⟩ (.int 9)))) = false := rfl

/-- `bump(inout xs)` while `v` lives. -/
example : reads (withXs (withView (.call (.fnRef "bump" [] []) [.inout ⟨"xs", []⟩] .unit))) = false :=
  rfl

/-- `d = Doc { … }` and `d.lines[0] = "b"` while `w` views `d.lines`. -/
example : reads (withDoc (.assign ⟨"d", []⟩ (.record "Doc" [] [("lines", .list .str []), ("n", .int 1)])))
    = false := rfl
example : reads (withDoc (.assign ⟨"d", [.field "lines", .index (.int 0)]⟩ (.op (.str "b") [])))
    = false := rfl

/-- `for x in View.all(xs) { bump(inout xs) }`: the loop's view reads `xs` for its body
(views.for-over-view). -/
example : reads (withXs (.for "x" .i64 (.view [.var "xs"])
    (.call (.fnRef "bump" [] []) [.inout ⟨"xs", []⟩] .unit))) = false := rfl

/-- `View.of(xs, bump(inout xs), 2)`: the view's read of `xs` starts when `xs`, its source
operand, is evaluated, so the offset that changes `xs` changes it while viewed. -/
example : reads (withXs (.letIn "v" (.view listTy)
    (.view [.var "xs", .call (.fnRef "bump" [] []) [.inout ⟨"xs", []⟩] .unit, .int 2]) .unit)) = false :=
  rfl

/-- `var ys = [4]; var w = View.all(xs); w = View.all(ys); ys[0] = 9`: `w` reads `xs`, the source
it was bound with, for its scope, so a view of `ys` assigned to it would leave `ys` unread. -/
example : reads (withXs (.varIn "ys" listTy (ints [4]) (.varIn "w" (.view listTy) (.view [.var "xs"])
    (.seq (.assign ⟨"w", []⟩ (.view [.var "ys"])) (.assign ⟨"ys", [.index (.int 0)]⟩ (.int 9))))))
    = false := rfl

/-- `w = w.view(0, 1)`: a view made of the place `w` reads `w` itself, which `w` wasn't bound
with. -/
example : reads (withXs (.varIn "w" (.view listTy) (.view [.var "xs"])
    (.assign ⟨"w", []⟩ (.view [.var "w", .int 0, .int 1])))) = false := rfl

/-! ### Accepted: a modification before the view, after its scope, or of another place -/

/-- `xs[0] = 9` before `let v = View.of(xs, 0, 2)`, and `v[0]` after. -/
example : reads (withXs (.seq (.assign ⟨"xs", [.index (.int 0)]⟩ (.int 9))
    (withView (.index (.var "v") (.int 0))))) = true := rfl

/-- `d.n = 1` while `w` views `d.lines`, a place beside it (modes.overlap). -/
example : reads (withDoc (.assign ⟨"d", [.field "n"]⟩ (.int 1))) = true := rfl

/-- A view of a temporary, `View.of([1, 2, 3], 0, 2)`, reads nothing `xs[0] = 9` changes. -/
example : reads (withXs (.letIn "v" (.view listTy) (.view [ints [1, 2, 3], .int 0, .int 2])
    (.assign ⟨"xs", [.index (.int 0)]⟩ (.int 9)))) = true := rfl

/-! ### E0422: a view that outlives its source -/

/-- A function's body, with its parameters and its result type, passes the check of E0422. -/
private def contained (ps : List Param) (result : Ty) (body : Expr) : Bool :=
  let Γ := ViewScope.params decls [] ps
  let params := resultParams decls ps result
  body.contained decls Γ params && leaves params (body.sources decls Γ)

private def letParam (x : Name) (τ : Ty) : Param := ⟨.let, x, τ, none⟩

/-- `fn of_local() -> View<str> { let s = "ab"; View.all(s) }`. -/
example : contained [] (.view .str)
    (.letIn "s" .str (.op (.str "ab") []) (.view [.var "s"])) = false := rfl

/-- `fn captured(s: str) -> fn() -> i64 { let v = View.all(s); || v.len() }`: a closure that
captures a view can't leave, since its type isn't a view type. -/
example : contained [letParam "s" .str] (.fn [] .i64 Row.pure)
    (.letIn "v" (.view .str) (.view [.var "s"])
      (.closure [] .i64 Row.pure (.op .len [.op .copy [.var "v"]]))) = false := rfl

/-- `let v = { var ys = [1, 2]; View.of(ys, 0, 1) }`: a block's value views the block's binding. -/
example : contained [] .i64
    (.letIn "v" (.view listTy) (.varIn "ys" listTy (ints [1, 2]) (.view [.var "ys", .int 0, .int 1]))
      (.index (.var "v") (.int 0))) = false := rfl

/-- `fn of_field(b: Bag) -> View<List<i64>> { View.all(b.items) }`: a view of a part of a
parameter views the callee's copy (views.across-calls). -/
example : contained [letParam "b" (.record "Doc" [])] (.view (.list .str))
    (.view [.field (.var "b") "lines"]) = false := rfl

/-- `var w = View.all(xs)` outside a block that binds `ys`, then `w = View.all(ys)` in it: the
view would outlive `ys` (views.escaping). -/
example : contained [] .unit
    (.varIn "xs" listTy (ints [1]) (.varIn "w" (.view listTy) (.view [.var "xs"])
      (.varIn "ys" listTy (ints [2]) (.assign ⟨"w", []⟩ (.view [.var "ys"]))))) = false := rfl

/-! ### Accepted: views of parameters in results, and views inside their sources' scopes -/

/-- `fn first(s: str) -> View<str> { View.of(s, 0, 1) }`. -/
example : contained [letParam "s" .str] (.view .str) (.view [.var "s", .int 0, .int 1]) = true :=
  rfl

/-- `fn part(v: View<str>) -> View<str> { v.view(0, 1) }`: a view parameter's sources are the
caller's. -/
example : contained [letParam "v" (.view .str)] (.view .str) (.view [.var "v", .int 0, .int 1])
    = true := rfl

/-- A view of a local, read inside its scope: `let ys = [1, 2]; View.all(ys)[0]`. -/
example : contained [] .i64
    (.letIn "ys" listTy (ints [1, 2]) (.index (.view [.var "ys"]) (.int 0))) = true := rfl

end Stilt.Examples.ViewChecks
