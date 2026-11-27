import Stilt.Declarations
import Stilt.Typing.Shapes

/-!
# What written forms know

Every form that a program's bodies write, at any depth, those in closure literals and
handlers' bodies included, with the expression it means (`Expr.forms`). A form's typing
(`HasType.shaped`) holds of its instances too, whose type parameters a call has replaced;
`Program.FormsKnown` checks what the Reference decides by the written body's own types
(`Form.Known`).
-/

namespace Stilt

mutual

/-- The forms that `e` writes, at any depth, each with its meaning. -/
def Expr.forms : Expr → List (Form × Expr)
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _
  | .method _ _ _ => []
  | .form k m => (k, m) :: m.forms
  | .closure _ _ _ body => body.forms
  | .record _ _ fields => fieldsForms fields
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => exprsForms es
  | .field e _ | .raise e | .try e | .return e | .loop e | .perform _ e => e.forms
  | .index a b | .seq a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b | .while a b
  | .tryCatch a _ _ b _ | .withH _ _ a b => a.forms ++ b.forms
  | .held _ hs body => exprsForms hs ++ body.forms
  | .call callee args _ => callee.forms ++ argsForms args
  | .assign ⟨_, path⟩ value => pathForms path ++ value.forms
  | .if c _ a b => c.forms ++ a.forms ++ b.forms
  | .match e _ arms => e.forms ++ armsForms arms

def exprsForms : List Expr → List (Form × Expr)
  | [] => []
  | e :: es => e.forms ++ exprsForms es

def fieldsForms : List (Name × Expr) → List (Form × Expr)
  | [] => []
  | (_, e) :: fields => e.forms ++ fieldsForms fields

def argsForms : List Arg → List (Form × Expr)
  | [] => []
  | .value e :: args => e.forms ++ argsForms args
  | .inout ⟨_, path⟩ :: args => pathForms path ++ argsForms args

def pathForms : List Projection → List (Form × Expr)
  | [] => []
  | .field _ :: path => pathForms path
  | .index i :: path => i.forms ++ pathForms path

def armsForms : List Arm → List (Form × Expr)
  | [] => []
  | ⟨_, _, guard, body⟩ :: arms => guardForms guard ++ body.forms ++ armsForms arms

def guardForms : Option Expr → List (Form × Expr)
  | none => []
  | some g => g.forms

end

/-- The forms of every body of a program, and of `main`. -/
def Program.forms (p : Program) : List (Form × Expr) :=
  p.decls.fns.flatMap (·.body.forms) ++ p.main.forms

/-- Each form that the program writes is what its written types make it (`Form.Known`): a
field read through an `Option` adds a level of `Option` only at a field whose type is no
`Option` (types.option-field-types and types.option-field-known). -/
def Program.FormsKnown (p : Program) : Prop :=
  ∀ k ∈ p.forms, Form.Known k.1 k.2

end Stilt
