import Stilt.Typing.Shapes

/-!
# Iterators

`std.view`'s `Iter<T>` as the calculus writes it: a record of the library, `Iter<T>`, whose one
field is the function that asks for the next element, giving it with the iterator of the
elements after it, or nothing once the elements end. An iterator is so a value, and asking it
again gives the same element (views.laziness). Each function of `impl<T> Iter<T>` that the
calculus writes is a function that the export declares once, generic over the element types,
written here: the makers and the adapters build an iterator and run nothing, and each adapter's
function asks its source when it is itself asked, as the Reference orders the asking; the
consumers (`Stilt.Typing.IterConsumers`) ask from the first element on.
-/

namespace Stilt

/-- The name the export gives `std.view`'s `Iter<T>`. -/
def iterName : Name := "std.view.Iter"

/-- `Iter<τ>`. -/
abbrev Ty.iter (τ : Ty) : Ty := .record iterName [τ]

/-- An element and the iterator of the elements after it. -/
abbrev Ty.iterPair (τ : Ty) : Ty := .tuple [τ, Ty.iter τ]

/-- What asking an iterator gives: its next element and the rest, or `None` once it ends. -/
abbrev Ty.iterStep (τ : Ty) : Ty := Ty.option (Ty.iterPair τ)

/-- The type of an iterator's field `next`: a function that takes nothing and whose row is
empty. -/
abbrev Ty.iterNext (τ : Ty) : Ty := .fn [] (Ty.iterStep τ) Row.pure

/-- `I` names `Iter<T>`, declared as a record of one type parameter with one field, `next`, the
function that asks for the next element (views.what-view-is: a lazy sequence, whose elements
come only when a consumer asks for them). The record's field is a function, and a function type
implements none of the prelude's traits (`Decls.ImplStep`), so neither does `Iter<T>`: two
iterators can't be compared and one can't be shown, which typing gives as E0318
(`Op.BoundsIn`, views.iterator-traits). Its name is no name a program's declaration can have,
so no program writes an impl for it, and nothing but the functions here reaches its field. -/
def Decls.IsIter (D : Decls) (I : Name) : Prop :=
  I = iterName ∧ ∃ r p, D.record? I = some r ∧ r.typeParams = [p] ∧
    r.fields = [("next", Ty.iterNext (.param p))]

namespace Iter

/-- The type parameters `T`, `U` and `A` of the functions of iterators. -/
abbrev T : Ty := .param "T"
abbrev U : Ty := .param "U"
abbrev A : Ty := .param "A"

/-- A type parameter without bounds. -/
def tp (n : Name) : TypeParam := { name := n, bounds := [] }

/-- A `let` parameter that is not a non-escaping one. -/
def arg (n : Name) (τ : Ty) : Param := ⟨.let, n, τ, none⟩

/-- `fn(τ) -> σ` with an empty row: an adapter's closure, whose parameter is `escaping`
(views.adapters). -/
abbrev fn1 (τ σ : Ty) : Ty := .fn [(.let, τ)] σ Row.pure

/-- `it.next()`: the iterator `it` of `τ`s asked for its next element. -/
def ask (τ : Ty) (it : Expr) : Expr := .call (.field it "next") [] (Ty.iterStep τ)

/-- `Iter { next: || body }`, an iterator of `τ`s that runs `body` when it is asked. -/
def make (τ : Ty) (body : Expr) : Expr :=
  .record iterName [τ] [("next", .closure [] (Ty.iterStep τ) Row.pure body)]

/-- No element: the iterator has ended. -/
def done (τ : Ty) : Expr := .variant optionName [Ty.iterPair τ] "None" []

/-- The element `x`, then the iterator `rest`. -/
def give (τ : Ty) (x rest : Expr) : Expr :=
  .variant optionName [Ty.iterPair τ] "Some" [.op .tuple [x, rest]]

/-- `match s { Some((x, r)) => onSome, None => onNone }`, at the type `σ`. -/
def cases (s : Expr) (σ : Ty) (x r : Name) (onSome onNone : Expr) : Expr :=
  .match s σ [⟨.variant optionName "Some" [.tuple [.bind x, .bind r]], [x, r], none, onSome⟩,
    ⟨.variant optionName "None" [], [], none, onNone⟩]

/-- A call of the function named `f`, at the type arguments `ts`, on the values `args`. -/
def call (f : Name) (ts : List Ty) (args : List Expr) (τ : Ty) : Expr :=
  .call (.fnRef f ts []) (args.map .value) τ

/-- `f(x)` for a function value `f`. -/
def apply (f : Name) (args : List Expr) (τ : Ty) : Expr := .call (.var f) (args.map .value) τ

/-- `a + 1`, `a - 1`, `a < b` and `a <= b` at `i64`. -/
def succ (a : Expr) : Expr := .op (.arith .add .i64) [a, .int 1]
def pred (a : Expr) : Expr := .op (.arith .sub .i64) [a, .int 1]
def lt (a b : Expr) : Expr := .op (.compare .lt .i64) [a, b]
def le (a b : Expr) : Expr := .op (.compare .le .i64) [a, b]

/-- The name the export gives the function of `Iter<T>` named `f`. -/
def fnName (f : String) : Name := "std.view.Iter." ++ f

end Iter

open Iter

/-- views.making-iterator: `Iter.of(xs)` is `of(xs, 0)`, the iterator of the elements of the list
`xs` from the index `i` on, in order. The export writes `Iter.of_view(v)` as `Iter.of` of the
view's `copy`, its part, and `view.of_map(m)` as `Iter.of` of the map's entries, in insertion
order. Each iterates a copy where the Reference's iterator reads its source: the model leaves
out an iterator's sources, so a change of a source while an iterator lives (E0423), and an
iterator that outlives one (E0422), are left out, and an accepted program can't tell the copy
from the source. -/
def FnDecl.iterOf : FnDecl :=
  ⟨fnName "of", [tp "T"], [], [arg "xs" (.list T), arg "i" .i64], Ty.iter T, Row.pure,
    make T (.if (lt (.var "i") (.op (.list .len) [.var "xs"])) (Ty.iterStep T)
      (give T (.index (.var "xs") (.var "i")) (call (fnName "of") [T] [.var "xs", succ (.var "i")]
        (Ty.iter T)))
      (done T)), {}⟩

/-- views.making-iterator: `view.range(start, end)`, the integers from `start` up to but
excluding `end`, with no source. -/
def FnDecl.iterRange : FnDecl :=
  ⟨fnName "range", [], [], [arg "a" .i64, arg "b" .i64], Ty.iter .i64, Row.pure,
    make .i64 (.if (lt (.var "a") (.var "b")) (Ty.iterStep .i64)
      (give .i64 (.var "a") (call (fnName "range") [] [succ (.var "a"), .var "b"] (Ty.iter .i64)))
      (done .i64)), {}⟩

/-- views.adapters and views.laziness: `it.map(f)`, which asks `it` when it is asked and calls
`f` on the element that reaches it. The closure is an `escaping` parameter whose row is empty, so
a closure literal that performs `io` or raises doesn't fit it, nor a function value with a larger
row (E0502 and E0311, a row that doesn't fit); the allocation of the iterator is left out, and so
is E0422 at a closure that captures a view. -/
def FnDecl.iterMap : FnDecl :=
  ⟨fnName "map", [tp "T", tp "U"], [], [arg "it" (Ty.iter T), arg "f" (fn1 T U)], Ty.iter U,
    Row.pure,
    make U (cases (ask T (.var "it")) (Ty.iterStep U) "x" "r"
      (give U (apply "f" [.var "x"] U) (call (fnName "map") [T, U] [.var "r", .var "f"] (Ty.iter U)))
      (done U)), {}⟩

/-- views.adapters and views.laziness: `it.filter(keep)`, which asks `it` and calls `keep` on
every element that reaches it, giving the first it keeps. -/
def FnDecl.iterFilter : FnDecl :=
  let rest := call (fnName "filter") [T] [.var "r", .var "keep"] (Ty.iter T)
  ⟨fnName "filter", [tp "T"], [], [arg "it" (Ty.iter T), arg "keep" (fn1 T .bool)], Ty.iter T,
    Row.pure,
    make T (cases (ask T (.var "it")) (Ty.iterStep T) "x" "r"
      (.if (apply "keep" [.var "x"] .bool) (Ty.iterStep T) (give T (.var "x") rest) (ask T rest))
      (done T)), {}⟩

/-- views.adapters and views.laziness: `it.take(n)`, which gives nothing once `n` elements are
given, so it asks `it` for no element after the `n`th. -/
def FnDecl.iterTake : FnDecl :=
  ⟨fnName "take", [tp "T"], [], [arg "it" (Ty.iter T), arg "n" .i64], Ty.iter T, Row.pure,
    make T (.if (le (.var "n") (.int 0)) (Ty.iterStep T) (done T)
      (cases (ask T (.var "it")) (Ty.iterStep T) "x" "r"
        (give T (.var "x") (call (fnName "take") [T] [.var "r", pred (.var "n")] (Ty.iter T)))
        (done T))), {}⟩

/-- views.adapters and views.laziness: `it.skip(n)`, which, asked, asks `it` and drops the first
`n` elements, then gives the next. -/
def FnDecl.iterSkip : FnDecl :=
  ⟨fnName "skip", [tp "T"], [], [arg "it" (Ty.iter T), arg "n" .i64], Ty.iter T, Row.pure,
    make T (.if (le (.var "n") (.int 0)) (Ty.iterStep T) (ask T (.var "it"))
      (cases (ask T (.var "it")) (Ty.iterStep T) "x" "r"
        (ask T (call (fnName "skip") [T] [.var "r", pred (.var "n")] (Ty.iter T)))
        (done T))), {}⟩

/-- views.adapters and views.laziness: `it.take_while(p)`, which ends at the first element that
`p` rejects, and asks for none after it. -/
def FnDecl.iterTakeWhile : FnDecl :=
  ⟨fnName "take_while", [tp "T"], [], [arg "it" (Ty.iter T), arg "p" (fn1 T .bool)], Ty.iter T,
    Row.pure,
    make T (cases (ask T (.var "it")) (Ty.iterStep T) "x" "r"
      (.if (apply "p" [.var "x"] .bool) (Ty.iterStep T)
        (give T (.var "x") (call (fnName "take_while") [T] [.var "r", .var "p"] (Ty.iter T)))
        (done T))
      (done T)), {}⟩

/-- views.adapters and views.laziness: `it.skip_while(p)`, which asks and drops the elements
that `p` accepts, up to the first it rejects, and then gives the rest as `it` gives them. -/
def FnDecl.iterSkipWhile : FnDecl :=
  ⟨fnName "skip_while", [tp "T"], [], [arg "it" (Ty.iter T), arg "p" (fn1 T .bool)], Ty.iter T,
    Row.pure,
    make T (cases (ask T (.var "it")) (Ty.iterStep T) "x" "r"
      (.if (apply "p" [.var "x"] .bool) (Ty.iterStep T)
        (ask T (call (fnName "skip_while") [T] [.var "r", .var "p"] (Ty.iter T)))
        (give T (.var "x") (.var "r")))
      (done T)), {}⟩

/-- views.adapters: `it.enumerate(start)`, each element with its index, counted from `start`,
whose next index is computed as the element is given, so one past `i64`'s range overflows. -/
def FnDecl.iterEnumerate : FnDecl :=
  let P : Ty := .tuple [.i64, T]
  ⟨fnName "enumerate", [tp "T"], [], [arg "it" (Ty.iter T), arg "i" .i64], Ty.iter P, Row.pure,
    make P (cases (ask T (.var "it")) (Ty.iterStep P) "x" "r"
      (give P (.op .tuple [.var "i", .var "x"])
        (call (fnName "enumerate") [T] [.var "r", succ (.var "i")] (Ty.iter P)))
      (done P)), {}⟩

/-- views.adapters and views.laziness: `a.zip(b)`, which asks `a` and then `b` for each pair,
and ends with the first that ends, asking `b` nothing once `a` has. -/
def FnDecl.iterZip : FnDecl :=
  let P : Ty := .tuple [T, U]
  ⟨fnName "zip", [tp "T", tp "U"], [], [arg "a" (Ty.iter T), arg "b" (Ty.iter U)], Ty.iter P,
    Row.pure,
    make P (cases (ask T (.var "a")) (Ty.iterStep P) "x" "ra"
      (cases (ask U (.var "b")) (Ty.iterStep P) "y" "rb"
        (give P (.op .tuple [.var "x", .var "y"])
          (call (fnName "zip") [T, U] [.var "ra", .var "rb"] (Ty.iter P)))
        (done P))
      (done P)), {}⟩

/-- views.adapters and views.laziness: `a.chain(b)`, which asks `b` once `a` ends. -/
def FnDecl.iterChain : FnDecl :=
  ⟨fnName "chain", [tp "T"], [], [arg "a" (Ty.iter T), arg "b" (Ty.iter T)], Ty.iter T, Row.pure,
    make T (cases (ask T (.var "a")) (Ty.iterStep T) "x" "r"
      (give T (.var "x") (call (fnName "chain") [T] [.var "r", .var "b"] (Ty.iter T)))
      (ask T (.var "b"))), {}⟩

end Stilt
