import Stilt.Declarations

/-!
# The `when`s of a program

Every `when` that code writes, at any depth, those in closure literals and handlers'
bodies included: its names, each with the type of the value its handle reaches, and its
block (shared.when). The checks that a `when` asks of its block read them: E0430
(`Program.Locks`) and the law of exclusivity for names that may be one place
(`Program.HeldNames`).
-/

namespace Stilt

/-- A `when` as the checks read it: its names with their values' types, and its block. -/
abbrev When := List (Name × Ty) × Expr

mutual

/-- The `when`s that `e` writes, at any depth, those in closure literals included. -/
def Expr.whens : Expr → List When
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _
  | .method _ _ _ => []
  | .held ns hs body => exprsWhens hs ++ (ns, body) :: body.whens
  | .closure _ _ _ body => body.whens
  | .record _ _ fields => fieldsWhens fields
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => exprsWhens es
  | .field e _ | .raise e | .try e | .form _ e | .return e | .loop e | .perform _ e => e.whens
  | .index a b | .seq a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b | .while a b
  | .tryCatch a _ _ b _ | .withH _ _ a b => a.whens ++ b.whens
  | .call callee args _ => callee.whens ++ argsWhens args
  | .assign ⟨_, path⟩ value => pathWhens path ++ value.whens
  | .if c _ a b => c.whens ++ a.whens ++ b.whens
  | .match e _ arms => e.whens ++ armsWhens arms

def exprsWhens : List Expr → List When
  | [] => []
  | e :: es => e.whens ++ exprsWhens es

def fieldsWhens : List (Name × Expr) → List When
  | [] => []
  | (_, e) :: fields => e.whens ++ fieldsWhens fields

def argsWhens : List Arg → List When
  | [] => []
  | .value e :: args => e.whens ++ argsWhens args
  | .inout ⟨_, path⟩ :: args => pathWhens path ++ argsWhens args

def pathWhens : List Projection → List When
  | [] => []
  | .field _ :: path => pathWhens path
  | .index i :: path => i.whens ++ pathWhens path

def armsWhens : List Arm → List When
  | [] => []
  | ⟨_, _, guard, body⟩ :: arms => guardWhens guard ++ body.whens ++ armsWhens arms

def guardWhens : Option Expr → List When
  | none => []
  | some g => g.whens

end

/-- The `when`s of every body of a program, and of `main`. -/
def Program.whens (p : Program) : List When :=
  p.decls.fns.flatMap (·.body.whens) ++ p.main.whens

end Stilt
