import Stilt.Views.Syntax

/-!
# The calculus of writable views

projections.writable-views lets a view write its source: `view.into(inout xs, start, end)` makes a
view that writes `xs` (projections.writable-views), a `var` binding of a view type is writable
(projections.writable-bindings), and `v[i]` through a writable binding is a place (projections.places-through-views). This
calculus states those rules on the part of the calculus of views that they
meet: bindings, places, assignment, list literals and indexing, with
`View.of`, `view.into`, `v.view(a, b)` and `v.len()`. It reuses the types of
`Stilt.Views.Syntax`, and leaves that calculus and its theorems as they were.

A place is a variable followed by indexes, so its shape is its root (modes.overlap): records, fields and the overlap of their places are the views
calculus's. A program is a block with no parameters. Projections, calls,
`view.part`, `view.split`, loops and views of strings are outside it.
-/

namespace Stilt.Writes

open Stilt.Views (VTy)

/-- Expressions, in elaborated form, as those of `Stilt.Views.Syntax`. -/
inductive WExpr where
  /-- Reads a variable: a value, a view, or the view a writable binding
  holds. -/
  | var (name : Name)
  | int (value : Int)
  /-- `[e, …]`, with its element type. -/
  | list (elem : Ty) (elems : List WExpr)
  /-- `e[i]`, on a list (std.lists) or through a view (views.functions-of-views). -/
  | index (base index : WExpr)
  /-- `let x: T = e`, followed by the rest of its block (values.let-and-var). -/
  | letIn (name : Name) (type : VTy) (init body : WExpr)
  /-- `var x: T = e`, followed by the rest of its block. A `var` binding of a
  view type is writable (projections.writable-bindings). -/
  | varIn (name : Name) (type : VTy) (init body : WExpr)
  /-- `place = e`, where the place is a variable followed by indexes (expressions.assignment and expressions.places; modes.places), or `v[i]` through a writable binding (projections.places-through-views). -/
  | assign (target value : WExpr)
  /-- A statement followed by the rest of its block (expressions.statements). -/
  | seq (first rest : WExpr)
  /-- `View.of(source, start, end)`, of a place (views.making-view). -/
  | viewOf (source start stop : WExpr)
  /-- `view.into(inout source, start, end)`, a view that writes the place
  (projections.writable-views). -/
  | into (source start stop : WExpr)
  /-- `v.view(start, end)`, a part of a view, which reads (views.functions-of-views;
  projections.writable-views and projections.places-through-views). -/
  | sub (view start stop : WExpr)
  /-- `v.len()` (views.functions-of-views). -/
  | len (view : WExpr)

/-- The root of an expression that is a place, a variable followed by
indexes, which is its shape (modes.places and modes.overlap). -/
def WExpr.root? : WExpr → Option Name
  | .var x => some x
  | .index e _ => e.root?
  | _ => none

/-- Whether a `var` binding of the type is writable: one of a view type
(projections.writable-bindings). -/
def writable : VTy → Bool
  | .view _ => true
  | .base _ => false

/-- A program: a block with no parameters, and the type of its value. -/
structure WProgram where
  result : VTy
  body : WExpr

end Stilt.Writes
