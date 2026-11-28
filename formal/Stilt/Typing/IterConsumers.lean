import Stilt.Typing.Iters

/-!
# The consumers of iterators

The functions of `impl<T> Iter<T>` that read an iterator's elements, each declared once by the
export, generic over the element types, as `Stilt.Typing.Iters` declares the adapters. Each asks
its iterator for one element at a time, from the first, in a loop, and calls its callback on each
element as it reads it. A callback is a non-escaping parameter, whose implicit row variable the
consumer's own row holds, so a use instantiates it with the row of the callback it is given and
the callback's effects pass through to the caller (effects.non-escaping-parameters).
-/

namespace Stilt

namespace Iter

/-- The implicit row variable of a consumer's callback. -/
def cbRow : Row := ⟨false, none, ["r"], [], none⟩

/-- A non-escaping callback parameter, `name: fn(ps) -> σ`, whose row holds its implicit variable. -/
def callback (n : Name) (ps : List Ty) (σ : Ty) : Param :=
  ⟨.let, n, .fn (ps.map (.let, ·)) σ cbRow, some "r"⟩

/-- The iterator `it` of `τ`s read to its end: bound to `c`, then asked for one element at a
time, each bound to `x` while `body` runs, the rest kept in `c`; once it ends, `after`. A `return`
in `body` ends the consumer there. -/
def walk (τ : Ty) (it : Expr) (x : Name) (body after : Expr) : Expr :=
  .varIn "c" (Ty.iter τ) it
    (.seq (.loop (cases (ask τ (.var "c")) .unit x "r" (.seq body (.assign ⟨"c", []⟩ (.var "r")))
      .break)) after)

/-- `Some(x)` and `None`, of `Option<τ>`. -/
def someOf (τ : Ty) (x : Expr) : Expr := .variant optionName [τ] "Some" [x]
def noneOf (τ : Ty) : Expr := .variant optionName [τ] "None" []

end Iter

open Iter

/-- views.consumers: `it.collect()`, the list of every element, in order. Of a view type an
element can't be consumed into a list (E0421), which the model leaves out. -/
def FnDecl.iterCollect : FnDecl :=
  ⟨fnName "collect", [tp "T"], [], [arg "it" (Ty.iter T)], .list T, Row.pure,
    .varIn "acc" (.list T) (.list T [])
      (walk T (.var "it") "x" (.assign ⟨"acc", []⟩ (.op (.list .push) [.var "acc", .var "x"]))
        (.var "acc")), {}⟩

/-- views.consumers: `it.fold(init, f)`, `f` called on the value so far and each element in
turn, its row passed through. -/
def FnDecl.iterFold : FnDecl :=
  ⟨fnName "fold", [tp "T", tp "A"], ["r"], [arg "it" (Ty.iter T), arg "init" A, callback "f" [A, T] A],
    A, cbRow,
    .varIn "acc" A (.var "init")
      (walk T (.var "it") "x" (.assign ⟨"acc", []⟩ (apply "f" [.var "acc", .var "x"] A))
        (.var "acc")), {}⟩

/-- views.consumers: `it.count()`, the number of elements, each read. -/
def FnDecl.iterCount : FnDecl :=
  ⟨fnName "count", [tp "T"], [], [arg "it" (Ty.iter T)], .i64, Row.pure,
    .varIn "n" .i64 (.int 0)
      (walk T (.var "it") "x" (.assign ⟨"n", []⟩ (succ (.var "n"))) (.var "n")), {}⟩

/-- views.consumers: `it.any(p)`, which stops at the first element that `p` accepts. -/
def FnDecl.iterAny : FnDecl :=
  ⟨fnName "any", [tp "T"], ["r"], [arg "it" (Ty.iter T), callback "p" [T] .bool], .bool, cbRow,
    walk T (.var "it") "x" (.if (apply "p" [.var "x"] .bool) .unit (.return (.bool true)) .unit)
      (.bool false), {}⟩

/-- views.consumers: `it.all(p)`, which stops at the first element that `p` rejects. -/
def FnDecl.iterAll : FnDecl :=
  ⟨fnName "all", [tp "T"], ["r"], [arg "it" (Ty.iter T), callback "p" [T] .bool], .bool, cbRow,
    walk T (.var "it") "x" (.if (apply "p" [.var "x"] .bool) .unit .unit (.return (.bool false)))
      (.bool true), {}⟩

/-- views.consumers: `it.find(p)`, the first element that `p` accepts, which ends the reading. -/
def FnDecl.iterFind : FnDecl :=
  ⟨fnName "find", [tp "T"], ["r"], [arg "it" (Ty.iter T), callback "p" [T] .bool], Ty.option T,
    cbRow,
    walk T (.var "it") "x"
      (.if (apply "p" [.var "x"] .bool) .unit (.return (someOf T (.var "x"))) .unit) (noneOf T), {}⟩

/-- views.consumers: `it.first()`, which asks for one element. -/
def FnDecl.iterFirst : FnDecl :=
  ⟨fnName "first", [tp "T"], [], [arg "it" (Ty.iter T)], Ty.option T, Row.pure,
    cases (ask T (.var "it")) (Ty.option T) "x" "r" (someOf T (.var "x")) (noneOf T), {}⟩

/-- views.consumers: `it.last()`, which reads every element. -/
def FnDecl.iterLast : FnDecl :=
  ⟨fnName "last", [tp "T"], [], [arg "it" (Ty.iter T)], Ty.option T, Row.pure,
    .varIn "l" (Ty.option T) (noneOf T)
      (walk T (.var "it") "x" (.assign ⟨"l", []⟩ (someOf T (.var "x"))) (.var "l")), {}⟩

/-- views.consumers: `it.nth(n)`, the element at the index `n`, reading those before it; a
negative `n` reads none. -/
def FnDecl.iterNth : FnDecl :=
  ⟨fnName "nth", [tp "T"], [], [arg "it" (Ty.iter T), arg "n" .i64], Ty.option T, Row.pure,
    .if (lt (.var "n") (.int 0)) (Ty.option T) (noneOf T)
      (.varIn "i" .i64 (.var "n")
        (walk T (.var "it") "x"
          (.if (.op (.compare .eq .i64) [.var "i", .int 0]) .unit (.return (someOf T (.var "x")))
            (.assign ⟨"i", []⟩ (pred (.var "i"))))
          (noneOf T))), {}⟩

/-- The greatest element, by `better(best, x)`, which says whether `x` takes the place of the
best so far: `None` for no element. -/
def Iter.extreme (better : Expr → Expr → Expr) : Expr :=
  cases (ask T (.var "it")) (Ty.option T) "x" "r"
    (.varIn "best" T (.var "x")
      (walk T (.var "r") "y" (.if (better (.var "best") (.var "y")) .unit
        (.assign ⟨"best", []⟩ (.var "y")) .unit) (someOf T (.var "best"))))
    (noneOf T)

/-- views.consumers: in `impl<T: Ord> Iter<T>`, `it.max()`, the greatest element, the first of
equal ones: an element takes the place of the best so far only when it is greater. The export
gives the function `lt`, `<` at the element type as `Ord` orders it, a closure literal whose row
is empty; the model reads `T: Ord` through it. -/
def FnDecl.iterMax : FnDecl :=
  ⟨fnName "max", [tp "T"], [], [arg "it" (Ty.iter T), arg "lt" (.fn [(.let, T), (.let, T)] .bool
    Row.pure)], Ty.option T, Row.pure,
    Iter.extreme fun best x => apply "lt" [best, x] .bool, {}⟩

/-- views.consumers: in `impl<T: Ord> Iter<T>`, `it.min()`, the least element, the first of
equal ones: an element takes the place of the best so far only when it is less. -/
def FnDecl.iterMin : FnDecl :=
  ⟨fnName "min", [tp "T"], [], [arg "it" (Ty.iter T), arg "lt" (.fn [(.let, T), (.let, T)] .bool
    Row.pure)], Ty.option T, Row.pure,
    Iter.extreme fun best x => apply "lt" [x, best] .bool, {}⟩

end Stilt
