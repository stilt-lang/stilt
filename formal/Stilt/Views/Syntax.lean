import Stilt.Places

/-!
# The calculus of views

views.what-view-is adds views, windows into part of a value that someone else owns
(views.what-view-is). The core calculus of `Stilt.Syntax` has `List<T>` but no `str`, so
a list is the one viewable type here (views.viewable-types), and views live in a calculus of
their own: the part of the core calculus that a view meets, which is bindings,
places, assignment, list and record literals, field access, indexing, `if` and
`for`, with `View.of`, `view`, `len`, indexing through a view and `copy`
(views.making-view and views.functions-of-views).

A program of this calculus is the body of one function, whose `let`
parameters hold the caller's arguments, so that views.escaping can say which views
may leave it. Calls, closures, iterators and the functions of `str` are
outside it.
-/

namespace Stilt.Views

/-- The types of the calculus: those of the core calculus, and `View<T>`
(views.std-view and views.view-types). A view type is never part of another type, so no
field, payload or element can hold a view, and E0421 (views.view-types) can't arise. -/
inductive VTy where
  | base (type : Ty)
  | view (viewed : Ty)

/-- Whether a view of the type can be made: a list, since the calculus has no
`str` (views.viewable-types). Any other type is E0420. -/
def viewable : Ty → Bool
  | .list _ => true
  | _ => false

/-- Expressions, in elaborated form, as those of `Stilt.Syntax`: every
binder carries its type, and statements are expressions, `letIn`, `varIn` and
`seq` holding the rest of their block (expressions.statements). -/
inductive VExpr where
  /-- Reads a variable, a value or a view. -/
  | var (name : Name)
  | int (value : Int)
  | bool (value : Bool)
  | unit
  /-- `R { f: e, … }`, with the fields in the order they are written
  (expressions.struct-literal-fields). -/
  | record (type : Name) (fields : List (Name × VExpr))
  /-- `[e, …]`, with its element type. -/
  | list (elem : Ty) (elems : List VExpr)
  /-- `e.f` (types.field-access). -/
  | field (base : VExpr) (name : Name)
  /-- `e[i]`, on a list (std.lists) or through a view (views.functions-of-views). -/
  | index (base : VExpr) (index : VExpr)
  /-- `let x: T = e`, followed by the rest of its block (values.let-and-var). -/
  | letIn (name : Name) (type : VTy) (init body : VExpr)
  /-- `var x: T = e`, followed by the rest of its block (values.let-and-var). -/
  | varIn (name : Name) (type : Ty) (init body : VExpr)
  /-- `place = e`, where the target is a variable followed by fields and
  indexes (expressions.assignment; modes.places). -/
  | assign (target value : VExpr)
  /-- A statement followed by the rest of its block (expressions.statements). -/
  | seq (first rest : VExpr)
  /-- `if c { a } else { b }`, with the type of its branches (expressions.if). -/
  | «if» (cond : VExpr) (type : VTy) (thenBranch elseBranch : VExpr)
  /-- `for x in e { body }`, over a list (expressions.for-iterables) or a view of one
  (views.for-over-view). -/
  | «for» (name : Name) (elem : Ty) (iterable body : VExpr)
  /-- `View.of(source, start, end)` (views.making-view). -/
  | viewOf (source start stop : VExpr)
  /-- `v.view(start, end)`, a part of a view, its offsets counted from the
  view's start (views.making-view and views.functions-of-views). -/
  | sub (view start stop : VExpr)
  /-- `v.len()` (views.functions-of-views). -/
  | len (view : VExpr)
  /-- `v.copy()`, the viewed part as an owned value (views.functions-of-views). -/
  | copy (view : VExpr)

/-- The shape of an expression that is a place, a variable followed by fields
and indexes, with its indexes removed (modes.places and modes.overlap). -/
def VExpr.shape? : VExpr → Option Shape
  | .var x => some ⟨x, []⟩
  | .field e f => e.shape?.map fun s => ⟨s.root, s.fields ++ [f]⟩
  | .index e _ => e.shape?
  | _ => none

/-- A function's body, run with its `let` parameters bound to the caller's
arguments, each with its type, and the type of its result. A parameter's
source is the caller's argument (views.across-calls), whose storage outlives the
call; `inout` parameters and view parameters are outside the calculus. -/
structure VProgram where
  decls : Decls
  args : List (Name × Ty × Value)
  result : VTy
  body : VExpr

end Stilt.Views
