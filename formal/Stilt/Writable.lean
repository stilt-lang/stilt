import Stilt.Free
import Stilt.Syntax.Forms

/-!
# Writable views in the calculus

A writable binding (projections.writable-bindings), a `var` of a view type that
`view.into(inout xs, a, b)` or `view.part(inout v, a, b)` gives (projections.writable-views), is
a form of the calculus, `Form.writes`, which means the call the binding is: the rest of the
binding's block is the body of a closure literal whose first parameter takes the binding's source
`inout`, a list, and the closure is called with the source's place `inout` first. Its further
parameters take the variables the rest of the block modifies, each `inout` under its own name,
since a closure captures by copy. The binding stands for its source's parameter and two offsets,
its part's start and end in the source, which are `let` bindings around the call.

So the binding writes its source the way an `inout` argument does: copy-in, copy-out in the
reference interpreter's model, the part written back when the scope ends, however it ends; and in
place, and with windows, the source's own storage, written at once (projections.what-view-writes).
Every theorem of the calculus covers it through that call, `inPlaceAgreement` among them: the law
of exclusivity is what makes the two agree.

A place through the binding, `v[i]`, is a place of the source's parameter at the index
`Expr.throughOf` gives (projections.places-through-views), so it can be assigned to, passed
`inout` and be the receiver of a method that takes `inout self`, and a read of `v[i]` reads the
binding's part. `Program.ViewsWrite`, a check of `Program.Accepted`, states the rules of writable
bindings on these forms.
-/

namespace Stilt

/-- The index of a place through a writable binding whose part runs from `start` up to `stop` of
its source: `i` from the part's start, evaluated into `j`, when `0 ≤ i < stop - start`, and `-1`
otherwise, which no list has, so that the access panics with `bounds` where an access of a list
at an index past its end does, after the other operands (projections.places-through-views). -/
def Expr.throughOf (j start stop : Name) (i : Expr) : Expr :=
  .form .through (.letIn j (.int .i64) i
    (.if (.op (.compare .lt .i64) [.var j, .int 0]) (.int .i64) (.int (-1))
      (.if (.op (.compare .lt .i64) [.var j, .op (.arith .sub .i64) [.var stop, .var start]])
        (.int .i64) (.op (.arith .add .i64) [.var start, .var j]) (.int (-1)))))

/-- What a writable binding's form means: a call of a closure literal whose first parameter takes
the binding's source `inout`, a list, as the call's first argument passes it, and whose body
reaches no variable the source's place is rooted in, read or written: while a writable binding
writes a source, nothing else reaches it (projections.reaching-written-source, E0429). Views of
strings are read-only, so the source is a list (projections.writable-views). -/
def Expr.writesShaped : Expr → Bool
  | .call (.closure (⟨.inout, src, .list _, _⟩ :: ps) _ _ body) (.inout ⟨x, _⟩ :: _) _ =>
    !Expr.captures (⟨.inout, src, .list .unit, none⟩ :: ps) body x
  | _ => false

mutual

/-- Whether code keeps the rules of writable bindings: each writable binding's form is the call
it means (`Expr.writesShaped`), whose body reaches no variable its source is rooted in (E0429),
and no `var` binding has a view type unless it is a writable binding's form: a view given to a
`var` must write every source it has, which a view that reads doesn't
(projections.writable-bindings, E0428). -/
def Expr.writesChecked : Expr → Bool
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method .. => true
  | .form .writes m => m.writesShaped && m.writesChecked
  | .varIn _ (.view _) _ _ => false
  | .form _ e | .field e _ | .raise e | .try e | .return e | .loop e | .perform _ e =>
    e.writesChecked
  | .record _ _ fields => fieldsWritesChecked fields
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => exprsWritesChecked es
  | .index a b | .seq a b | .while a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b
  | .for _ _ a b | .tryCatch a _ _ b _ => a.writesChecked && b.writesChecked
  | .closure _ _ _ body => body.writesChecked
  | .call callee args _ => callee.writesChecked && argsWritesChecked args
  | .assign ⟨_, path⟩ value => pathWritesChecked path && value.writesChecked
  | .if c _ a b => c.writesChecked && a.writesChecked && b.writesChecked
  | .match e _ arms => e.writesChecked && armsWritesChecked arms
  | .held _ hs body => exprsWritesChecked hs && body.writesChecked

def exprsWritesChecked : List Expr → Bool
  | [] => true
  | e :: es => e.writesChecked && exprsWritesChecked es

def fieldsWritesChecked : List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fields => e.writesChecked && fieldsWritesChecked fields

def argsWritesChecked : List Arg → Bool
  | [] => true
  | .value e :: args => e.writesChecked && argsWritesChecked args
  | .inout ⟨_, path⟩ :: args => pathWritesChecked path && argsWritesChecked args

def pathWritesChecked : List Projection → Bool
  | [] => true
  | .field _ :: path => pathWritesChecked path
  | .index i :: path => i.writesChecked && pathWritesChecked path

def armsWritesChecked : List Arm → Bool
  | [] => true
  | ⟨_, _, guard, body⟩ :: arms =>
    (match guard with | none => true | some g => g.writesChecked) && body.writesChecked &&
      armsWritesChecked arms

end

/-- The checks of writable bindings on a program: every body and `main` keep them
(`Expr.writesChecked`). -/
def Program.viewsWritten (p : Program) : Bool :=
  p.decls.fns.all (·.body.writesChecked) && p.main.writesChecked

/-- A program keeps the rules of writable bindings: while one writes a source, nothing else
reaches it (projections.reaching-written-source, E0429), and a view given to a `var` writes every
source it has (projections.writable-bindings, E0428). -/
def Program.ViewsWrite (p : Program) : Prop := p.viewsWritten = true

end Stilt
