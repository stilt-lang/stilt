import Stilt.Typing.Shapes

/-!
# The functions of `std.par`

`par.map`, `par.each`, `par.both` and `par.fold` as `Expr.form` keeps them, each with the code
it means in the sequential run (par.sequential-meaning), which `TaskForm` shapes as it does the
forms of tasks: the closures are bound first, in the order the arguments are written, at the
types of `std.par`'s parameters, whose rows are empty, and then called on the elements from the
first to the last. `par.fold` calls the function that the export declares for it,
`FnDecl.foldTree`, the tree of par.fold-tree written in the calculus.
-/

namespace Stilt

/-- `fn(T) -> U` with an empty row, the type of `par.map`'s function. -/
def Ty.parMapFn (T U : Ty) : Ty := .fn [(.let, T)] U Row.pure

/-- `fn(inout T)` with an empty row, the type of `par.each`'s function. -/
def Ty.parEachFn (T : Ty) : Ty := .fn [(.inout, T)] .unit Row.pure

/-- `fn(T, T) -> T` with an empty row, the type of `par.fold`'s function. -/
def Ty.parFoldFn (T : Ty) : Ty := .fn [(.let, T), (.let, T)] T Row.pure

/-- `par.map(xs, f)`: the list bound to `n`, the function to `g`, then `g` called on each element,
from the first to the last, each value pushed onto the list `acc`, which the call gives. -/
def Expr.parMapOf (n g acc x : Name) (T U : Ty) (xs f : Expr) : Expr :=
  .form .parMap (.letIn n (.list T) xs (.letIn g (Ty.parMapFn T U) f
    (.varIn acc (.list U) (.list U [])
      (.seq (.for x T (.var n) (.assign ⟨acc, []⟩
        (.op (.list .push) [.var acc, .call (.var g) [.value (.var x)] U]))) (.var acc)))))

/-- The place of the element at the index `i` of the list at the place `P`. -/
def Place.at (P : Place) (i : Name) : Place := ⟨P.root, P.path ++ [.index (.var i)]⟩

/-- `par.each(inout xs, f)` for a place `xs` of fields, `P`: the function bound to `g`, then
called with each element of the list at `P` `inout`, from the first index to the last. -/
def Expr.parEachOf (g i : Name) (T : Ty) (P : Place) (f : Expr) : Expr :=
  .form .parEach (.letIn g (Ty.parEachFn T) f
    (.for i .i64 (.op (.list (.range false)) [.int 0, .op (.list .len) [P.read]])
      (.call (.var g) [.inout (P.at i)] .unit)))

/-- `par.both(f, g)`: `f` bound to `a`, `g` to `b`, then `a` called, then `b`, and the pair of
their values. -/
def Expr.parBothOf (a b : Name) (A B : Ty) (f g : Expr) : Expr :=
  .form .parBoth (.letIn a (.fn [] A Row.pure) f (.letIn b (.fn [] B Row.pure) g
    (.op .tuple [.call (.var a) [] A, .call (.var b) [] B])))

/-- The name of the function that the export declares for `par.fold`. No declaration of a
program has it. -/
def foldTreeName : Name := "std.par.fold"

/-- A call of the fold's function at the element type `T`, on the list `xs` and the function
`f`. -/
def Expr.foldTreeCall (T : Ty) (xs f : Expr) : Expr :=
  .call (.fnRef foldTreeName [T] []) [.value xs, .value f] T

/-- The body of the fold's function, of type parameter `T`, on a list `xs` of at least one
element and the function `f` (par.fold-tree): a list of one element is that element; a longer
list, of `n` elements, is its first `n / 2` folded, then the rest folded, then `f` of the two. -/
def Expr.foldTreeBody : Expr :=
  let T : Ty := .param "T"
  .letIn "n" .i64 (.op (.list .len) [.var "xs"])
    (.if (.op (.compare .eq .i64) [.var "n", .int 1]) T (.index (.var "xs") (.int 0))
      (.letIn "h" .i64 (.op (.arith .div .i64) [.var "n", .int 2])
        (.letIn "l" T (Expr.foldTreeCall T (.op (.list .slice) [.var "xs", .int 0, .var "h"])
            (.var "f"))
          (.letIn "r" T (Expr.foldTreeCall T (.op (.list .slice) [.var "xs", .var "h", .var "n"])
              (.var "f"))
            (.call (.var "f") [.value (.var "l"), .value (.var "r")] T)))))

/-- The function the export declares for `par.fold`, generic over the element type `T`, whose
function parameter is `escaping` with an empty row (par.what-runs-in-parallel). -/
def FnDecl.foldTree : FnDecl :=
  ⟨foldTreeName, [⟨"T", [], []⟩], [],
    [⟨.let, "xs", .list (.param "T"), none⟩, ⟨.let, "f", Ty.parFoldFn (.param "T"), none⟩],
    .param "T", Row.pure, Expr.foldTreeBody, {}⟩

/-- `par.fold(xs, empty, f)`: the list bound to `n`, `empty` to `d` and the function to `g`, in
order; then `d` when the list is empty, and otherwise the fold's function called on the list and
`g`. -/
def Expr.parFoldOf (n d g : Name) (T : Ty) (xs e f : Expr) : Expr :=
  .form .parFold (.letIn n (.list T) xs (.letIn d T e (.letIn g (Ty.parFoldFn T) f
    (.if (.op (.compare .eq .i64) [.op (.list .len) [.var n], .int 0]) T (.var d)
      (Expr.foldTreeCall T (.var n) (.var g))))))

end Stilt
