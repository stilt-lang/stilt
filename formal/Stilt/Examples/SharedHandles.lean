import Stilt.Modes.Facts

/-!
# Shared writes through calls and handles

The bindings that the inference of shared writes calls shared (`ModeEnv.bodyShared`) in the
programs of the conformance tests `modes/copies_stored_by_calls.lt`,
`modes/copies_stored_in_inout_arguments.lt`, `modes/handles.lt` and `modes/shared_writes_in_when.lt`,
written in the calculus, each expected verdict the test's:

* a call may store an argument when, by the call's types, a part of it may become a part of its
  result or of an `inout` argument, whatever the callee's body does with it, and what it stores
  in an `inout` argument lasts as long as the binding that argument is a part of;
* the end of a `when` gives each name's value back to its handle, so it writes each name, and
  `Shared.new` gives the value it takes to a handle in the same way;
* the names of one `when` of one type may be one place.

Lists of `i64` stand for every copy-on-write type, `push(inout xs, x)` for a write.
-/

namespace Stilt.Examples.SharedHandles

private def lst : Ty := .list .i64

private def param (x : Name) (τ : Ty := lst) (mode : Mode := .let) : Param := ⟨mode, x, τ, none⟩

private def v (x : Name) : Expr := .var x

private def ints (ns : List Int) : Expr := .list .i64 (ns.map .int)

/-- `push(inout xs, x)`, a write of `xs`. -/
private def push (xs : Name) (x : Int) : Expr :=
  .call (.fnRef "push" [] []) [.inout ⟨xs, []⟩, .value (.int x)] .unit

/-- `xs.len()`, which stores nothing. -/
private def len (e : Expr) : Expr := .op (.list .len) [e]

/-- `Shared.new(e)`. -/
private def share (e : Expr) : Expr := .op (.world (.sharedNew lst)) [e]

private def decl (name : Name) (ps : List Param) (body : Expr) (result : Ty) : FnDecl :=
  ⟨name, [], [], ps, result, Row.pure, body, {}⟩

/-- `push` writes its `inout` parameter; `put(inout to, x)` pushes `x` on `to`; `peek(xs)`
gives an empty list and `count(xs)` zero, so neither consumes `xs`, but by its types `peek` may
store it and `count` can't. -/
private def D : Decls :=
  ⟨[], [],
    [decl "push" [param "xs" lst .inout, param "x" .i64]
       (.assign ⟨"xs", [.index (.int 0)]⟩ (v "x")) .unit,
     decl "put" [param "to" (.list lst) .inout, param "x"]
       (.assign ⟨"to", []⟩ (.op (.list .push) [v "to", v "x"])) .unit,
     decl "peek" [param "xs"] (ints []) lst,
     decl "count" [param "xs"] (.int 0) .i64], [], [], [], [], []⟩

private def M : ModeEnv := ⟨D, D.consumed, D.onceParams⟩

private def call (f : Name) (args : List Arg) (τ : Ty) : Expr := .call (.fnRef f [] []) args τ

/-! ## Calls that may store their arguments -/

/-- `var a = [1]; let c = peek(a); push(inout a, 2); c.len()`: `peek` consumes nothing, but its
result may hold `a`, so the push is shared while `c` lasts. -/
example : M.bodyShared [] (.varIn "a" lst (ints [1]) (.letIn "c" lst (call "peek" [.value (v "a")] lst)
    (.seq (push "a" 2) (len (v "c"))))) = ["a"] := by decide +kernel

/-- `count` gives an `i64`, which holds no part of `a`, so the push is unique. -/
example : M.bodyShared [] (.varIn "a" lst (ints [1]) (.letIn "n" .i64 (call "count" [.value (v "a")] .i64)
    (.seq (push "a" 2) (v "n")))) = [] := by decide

/-- `var ls = []; { let b = a; put(inout ls, b) }; push(inout a, 4); ls.len()`: the copy that
`put` keeps in `ls` lasts as `ls` does. -/
example : M.bodyShared [param "a" lst .inout] (.varIn "ls" (.list lst) (.list lst [])
    (.seq (.letIn "b" lst (v "a") (call "put" [.inout ⟨"ls", []⟩, .value (v "b")] .unit))
      (.seq (push "a" 4) (len (v "ls"))))) = ["a"] := by decide +kernel

/-- A receiver whose scope ends with the block holds the copy no longer. -/
example : M.bodyShared [param "a" lst .inout] (.varIn "n" .i64 (.int 0)
    (.seq (.varIn "ls" (.list lst) (.list lst [])
        (.letIn "b" lst (v "a") (.seq (call "put" [.inout ⟨"ls", []⟩, .value (v "b")] .unit)
          (.assign ⟨"n", []⟩ (len (v "ls"))))))
      (.seq (push "a" 4) (v "n")))) = [] := by decide +kernel

/-! ## Handles -/

private def handle : Param := param "h" (.shared lst)

/-- `when h { a }`: the block gives a copy of `a` that lasts past the `when`, so its end is
shared. -/
example : M.bodyShared [handle] (.held [("a", lst)] [v "h"] (v "a")) = ["a"] := by decide

/-- `when h { let z = a; z.len() }`: the copy ends with the block. -/
example : M.bodyShared [handle] (.held [("a", lst)] [v "h"] (.letIn "z" lst (v "a") (len (v "z")))) =
    [] := by decide

/-- `when h { a = ys }; ys.len()`: `a` holds a copy of `ys`, which `ys` reads after the end. -/
example : M.bodyShared [handle, param "ys"]
    (.seq (.held [("a", lst)] [v "h"] (.assign ⟨"a", []⟩ (v "ys"))) (len (v "ys"))) = ["a"] := by
  decide

/-- `var ys = [1]; when h { a = ys }`: nothing reads `ys` after. -/
example : M.bodyShared [handle] (.varIn "ys" lst (ints [1])
    (.held [("a", lst)] [v "h"] (.assign ⟨"a", []⟩ (v "ys")))) = [] := by decide

/-- `var ys = [1]; when h { a = ys }; push(inout ys, 2)`: the handle holds the copy on, so the
push is shared; and the push names `ys` after the `when`, so the end is shared too, which the
test leaves out, since a site of `copy` on the push already rejects the function. -/
example : M.bodyShared [handle] (.varIn "ys" lst (ints [1])
    (.seq (.held [("a", lst)] [v "h"] (.assign ⟨"a", []⟩ (v "ys"))) (push "ys" 2))) =
    ["ys", "a"] := by decide +kernel

/-- `Shared.new(xs)` of a parameter, which the caller may still read. -/
example : M.bodyShared [param "xs"] (share (v "xs")) = ["xs"] := by decide

/-- `var xs = [1]; let s = Shared.new(xs); xs.len()`: read after the call. -/
example : M.bodyShared [] (.varIn "xs" lst (ints [1])
    (.letIn "s" (.shared lst) (share (v "xs")) (len (v "xs")))) = ["xs"] := by decide

/-- `var xs = [1]; Shared.new(xs)`: given at its last use. -/
example : M.bodyShared [] (.varIn "xs" lst (ints [1]) (share (v "xs"))) = [] := by decide

/-- `when h { push(inout a, 1); a.len() }`: nothing else holds the value. -/
example : M.bodyShared [handle] (.held [("a", lst)] [v "h"] (.seq (push "a" 1) (len (v "a")))) =
    [] := by decide

/-! ## Names of one `when` that may be one place -/

/-- `when g, h { let c = a; push(inout b, 1); c.len() }`: `b` may be `a`, so the push is shared
while `c` lasts, as a write of `b` and as one of `a`. -/
example : M.bodyShared [param "g" (.shared lst), handle]
    (.held [("a", lst), ("b", lst)] [v "g", v "h"]
      (.letIn "c" lst (v "a") (.seq (push "b" 1) (len (v "c"))))) = ["a", "b"] := by decide +kernel

/-- `when g, h { var y = a; push(inout y, 1); b.len() }`: `b` names what `a` does, after the
push. -/
example : (M.bodyShared [param "g" (.shared lst), handle]
    (.held [("a", lst), ("b", lst)] [v "g", v "h"]
      (.varIn "y" lst (v "a") (.seq (push "y" 1) (len (v "b")))))).contains "y" := by
  decide +kernel

/-- Names of different types are never one place. -/
example : M.bodyShared [param "g" (.shared lst), param "k" (.shared (.list .bool))]
    (.held [("a", lst), ("b", .list .bool)] [v "g", v "k"]
      (.letIn "c" lst (v "a") (.seq (.assign ⟨"b", [.index (.int 0)]⟩ (.bool true)) (len (v "c"))))) =
    [] := by decide +kernel

end Stilt.Examples.SharedHandles
