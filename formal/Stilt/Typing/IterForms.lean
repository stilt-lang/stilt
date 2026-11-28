import Stilt.Typing.IterConsumers
import Stilt.Generics.Commute

/-!
# The forms of iterators

A call of a function of `Iter<T>` as `Expr.form` keeps it: the call of the function that the
export declares for it (`Stilt.Typing.Iters` and `Stilt.Typing.IterConsumers`), which typing
checks as any call, against that function's signature, and which runs as that function's body.
-/

namespace Stilt

/-- The name of the function the export declares for a function of iterators. -/
def IterFn.name : IterFn → Name
  | .of => Iter.fnName "of" | .range => Iter.fnName "range" | .map => Iter.fnName "map"
  | .filter => Iter.fnName "filter" | .take => Iter.fnName "take" | .skip => Iter.fnName "skip"
  | .takeWhile => Iter.fnName "take_while" | .skipWhile => Iter.fnName "skip_while"
  | .enumerate => Iter.fnName "enumerate" | .zip => Iter.fnName "zip" | .chain => Iter.fnName "chain"
  | .collect => Iter.fnName "collect" | .fold => Iter.fnName "fold" | .count => Iter.fnName "count"
  | .any => Iter.fnName "any" | .all => Iter.fnName "all" | .find => Iter.fnName "find"
  | .first => Iter.fnName "first" | .last => Iter.fnName "last" | .nth => Iter.fnName "nth"
  | .max => Iter.fnName "max" | .min => Iter.fnName "min"

/-- The function the export declares for a function of iterators, as the model writes it. -/
def IterFn.decl : IterFn → FnDecl
  | .of => FnDecl.iterOf | .range => FnDecl.iterRange | .map => FnDecl.iterMap
  | .filter => FnDecl.iterFilter | .take => FnDecl.iterTake | .skip => FnDecl.iterSkip
  | .takeWhile => FnDecl.iterTakeWhile | .skipWhile => FnDecl.iterSkipWhile
  | .enumerate => FnDecl.iterEnumerate | .zip => FnDecl.iterZip | .chain => FnDecl.iterChain
  | .collect => FnDecl.iterCollect | .fold => FnDecl.iterFold | .count => FnDecl.iterCount
  | .any => FnDecl.iterAny | .all => FnDecl.iterAll | .find => FnDecl.iterFind
  | .first => FnDecl.iterFirst | .last => FnDecl.iterLast | .nth => FnDecl.iterNth
  | .max => FnDecl.iterMax | .min => FnDecl.iterMin

/-- The functions of iterators by the names the export gives them. -/
def IterFn.every : List IterFn :=
  [.of, .range, .map, .filter, .take, .skip, .takeWhile, .skipWhile, .enumerate, .zip, .chain,
    .collect, .fold, .count, .any, .all, .find, .first, .last, .nth, .max, .min]

/-- The function of iterators that the export declares under a name. -/
def IterFn.named? (n : Name) : Option IterFn := IterFn.every.find? (·.name == n)

/-- A call of the function of iterators `f`, at the type arguments `ts` and the rows `rs`, on the
arguments `args`, of the result type `τ`. -/
def Expr.iterOf (f : IterFn) (ts : List Ty) (rs : List Row) (args : List Arg) (τ : Ty) : Expr :=
  .form (.iter f) (.call (.fnRef f.name ts rs) args τ)

/-- The rule of the forms of iterators beside that of the call each means, which `HasType.task`
types through `TaskForm.iter`: the call is one of the function that the program declares for it,
as the model writes it (`IterFn.decl`), with `Iter<T>` and `Option<T>` declared as the model
writes them. So an iterator is made and adapted by functions that build a record of a closure and
run nothing else, and each consumer asks it from its first element on: nothing runs when an
iterator is made or adapted, and an iterator is a value, which no consumer changes
(views.laziness). -/
inductive IterForm (D : Decls) : Form → Expr → Ty → Prop
  | call {f : IterFn} {ts : List Ty} {rs : List Row} {args : List Arg} {τ : Ty} :
      D.IsIter iterName → D.IsOption optionName → D.fn? f.name = some f.decl →
      IterForm D (.iter f) (.call (.fnRef f.name ts rs) args τ) τ

/-- An instance of a generic body keeps each form of iterators: the call's type arguments, its
arguments and its result type are replaced, its function stays. -/
theorem IterForm.substTys {D : Decls} (s : TySubst) :
    ∀ {k : Form} {m : Expr} {τ : Ty}, IterForm D k m τ → IterForm D k (m.substTys s) (τ.substTys s)
  | _, _, _, .call hI hO hd => by
    simp only [Expr.substTys]
    exact .call hI hO hd

end Stilt
