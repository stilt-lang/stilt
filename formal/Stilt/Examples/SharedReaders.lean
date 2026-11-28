import Stilt.Sharing.Names

/-!
# Readers of shared storage that the inference counts

Four programs in which a write that the inference once called `unique` reached storage that
another binding read after it, so that the model of sharing (`Stilt.Sharing`) showed what copies
don't. `stilt-model` found each one. The inference now calls each write shared:

* `formerValue`: `var o = [1, 2]; var z = o; let w = o; o = t; z[0] = 9; w[0]`. The assignment
  of the whole of `o` ends the copies of its value for `o`'s writes, but `z` and `w` still hold
  that value, and `z`'s write reaches what `w` reads (modes.shared-holders). Without `w`, the
  write is unique: `o` reads its new value.
* `whenEnd`: `when a { var z = n; z[0] = 9 }`, where `n` is the name. The end of the `when`
  gives `n`'s value back to its handle, so `n` is read after every point of the block.
* `twoArguments`: `var a = t; var b = t; both(inout a, inout b)`. The call modifies `a` when it
  starts and reads `b` until it returns.
* `captured`: `|| { var z = xs; z[0] = 9; xs[0] }`. The closure's body reads `xs`, which it
  captures, after the write; the walk of a closure's body reads its captures as parameters.

Lists of `i64` stand for every copy-on-write type.
-/

namespace Stilt.Examples.SharedReaders

private def lst : Ty := .list .i64

private def param (x : Name) (τ : Ty := lst) (mode : Mode := .let) : Param := ⟨mode, x, τ, none⟩

private def v (x : Name) : Expr := .var x

private def ints (ns : List Int) : Expr := .list .i64 (ns.map .int)

/-- `x[0] = n`. -/
private def setFirst (x : Name) (n : Int) : Expr := .assign ⟨x, [.index (.int 0)]⟩ (.int n)

/-- `x[0]`. -/
private def first (x : Name) : Expr := .index (v x) (.int 0)

private def decl (name : Name) (ps : List Param) (body : Expr) (result : Ty) : FnDecl :=
  ⟨name, [], [], ps, result, Row.pure, body, {}⟩

/-- `both(inout p, inout q)` writes `p` and reads `q`. -/
private def D : Decls :=
  ⟨[], [], [decl "both" [param "p" lst .inout, param "q" lst .inout]
    (.seq (setFirst "p" 5) (first "q")) .i64], [], [], [], [], []⟩

private def M : ModeEnv := ⟨D, D.consumed, D.onceParams⟩

/-- `var o = [1, 2]; var z = o; let w = o; let t = [7, 8]; o = t; z[0] = 9; w[0]`, and the
same without `w`, reading `o` at the end. -/
private def formerValue (other : Bool) : Expr :=
  .varIn "o" lst (ints [1, 2]) (.varIn "z" lst (v "o")
    (if other then .letIn "w" lst (v "o") (rest (first "w")) else rest (first "o")))
where
  rest (last : Expr) : Expr :=
    .letIn "t" lst (ints [7, 8]) (.seq (.assign ⟨"o", []⟩ (v "t")) (.seq (setFirst "z" 9) last))

example : M.bodyShared [] (formerValue true) = ["z"] := by decide +kernel

example : M.bodyShared [] (formerValue false) = [] := by decide +kernel

/-- `when a { var z = n; z[0] = 9 }`, where `n` names the value of the handle `a`. -/
example : M.bodyShared [param "a" (.shared lst)]
    (.held [("n", lst)] [v "a"] (.varIn "z" lst (v "n") (setFirst "z" 9))) = ["z"] := by
  decide +kernel

/-- `let t = [1, 2]; var a = t; var b = t; both(inout a, inout b)`. -/
example : M.bodyShared [] (.letIn "t" lst (ints [1, 2]) (.varIn "a" lst (v "t")
    (.varIn "b" lst (v "t") (.call (.fnRef "both" [] []) [.inout ⟨"a", []⟩, .inout ⟨"b", []⟩]
      .i64)))) = ["b", "a"] := by decide +kernel

/-- `let xs = [1, 2]; let f = || { var z = xs; z[0] = 9; xs[0] }; f()`. -/
example : M.allShared [] (.letIn "xs" lst (ints [1, 2]) (.letIn "f" (.fn [] .i64 Row.pure)
    (.closure [] .i64 Row.pure (.varIn "z" lst (v "xs") (.seq (setFirst "z" 9) (first "xs"))))
    (.call (v "f") [] .i64))) = ["z"] := by decide +kernel

end Stilt.Examples.SharedReaders
