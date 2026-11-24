import Stilt.Handling

/-!
# The check that a body resumes at most once

handlers.resume-at-most-once: a body resumes at most once on each path, and a
`resume` is E0514 in a loop, in a closure literal, after another `resume` in
sequence, or in a branch that runs after another that resumed.
`Expr.resumes` counts the most `resume`s that a path through code may run: a
sequence of parts runs each, a branch runs its condition and one of its arms,
a `catch` may run its handler after its operand, and a loop that holds a
`resume` may run it again, so it counts two. A closure literal runs nothing
when it is made. `Expr.oneShot` checks every closure literal: its body may
resume once when its row holds `resume`, as the body of an operation of a
handler that takes control does (handlers.resuming), and never otherwise
(handlers.resume-outside-operation); a `with` names an effect other than the
reserved one of `resume`.
-/

namespace Stilt

/-- The `resume`s a body whose row holds `ρ` may run: one in the body of an
operation of a handler that takes control, none elsewhere. -/
def Row.resumes (ρ : Row) : Nat := if ρ.resume.isSome then 1 else 0

/-- A loop runs its body again and again: one that may resume counts two. -/
def loopResumes (n : Nat) : Nat := if n = 0 then 0 else 2

mutual

/-- The most `resume`s that a path through `e` may run (handlers.resume-at-most-once). -/
def Expr.resumes : Expr → Nat
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _
  | .method _ _ _ | .closure _ _ _ _ => 0
  | .record _ fields => fieldsResumes fields
  | .variant _ _ es | .list _ es | .op _ es | .view es => exprsResumes es
  | .field e _ | .raise e | .try e | .return e => e.resumes
  | .index e i => e.resumes + i.resumes
  | .call callee args _ => callee.resumes + argsResumes args
  | .letIn _ _ init body | .varIn _ _ init body => init.resumes + body.resumes
  | .held _ hs body => exprsResumes hs + body.resumes
  | .assign ⟨_, path⟩ value => pathResumes path + value.resumes
  | .seq a b => a.resumes + b.resumes
  | .if c _ a b => c.resumes + max a.resumes b.resumes
  | .match e _ arms => e.resumes + armsResumes arms
  | .for _ _ e body => e.resumes + loopResumes body.resumes
  | .tryCatch e _ _ handler _ => e.resumes + handler.resumes
  | .while c body => loopResumes (c.resumes + body.resumes)
  | .loop body => loopResumes body.resumes
  | .perform op e => e.resumes + if op = Operation.resume then 1 else 0
  | .withH _ _ h b => h.resumes + b.resumes

def exprsResumes : List Expr → Nat
  | [] => 0
  | e :: es => e.resumes + exprsResumes es

def fieldsResumes : List (Name × Expr) → Nat
  | [] => 0
  | (_, e) :: fields => e.resumes + fieldsResumes fields

def argsResumes : List Arg → Nat
  | [] => 0
  | .value e :: args => e.resumes + argsResumes args
  | .inout ⟨_, path⟩ :: args => pathResumes path + argsResumes args

def pathResumes : List Projection → Nat
  | [] => 0
  | .field _ :: path => pathResumes path
  | .index i :: path => i.resumes + pathResumes path

/-- One arm of a `match` runs: the most of any. -/
def armsResumes : List Arm → Nat
  | [] => 0
  | ⟨_, _, body⟩ :: arms => max body.resumes (armsResumes arms)

end

mutual

/-- Whether every closure literal of `e` resumes as often as its row allows, at
most once, and every `with` names an effect other than that of `resume`
(handlers.resume-at-most-once and handlers.resume-outside-operation). -/
def Expr.oneShot : Expr → Bool
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _
  | .method _ _ _ => true
  | .closure _ _ ρ body => body.oneShot && decide (body.resumes ≤ ρ.resumes)
  | .record _ fields => fieldsOneShot fields
  | .variant _ _ es | .list _ es | .op _ es | .view es => exprsOneShot es
  | .field e _ | .raise e | .try e | .return e | .loop e | .perform _ e => e.oneShot
  | .index a b | .seq a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b | .while a b
  | .tryCatch a _ _ b _ => a.oneShot && b.oneShot
  | .call callee args _ => callee.oneShot && argsOneShot args
  | .assign ⟨_, path⟩ value => pathOneShot path && value.oneShot
  | .if c _ a b => c.oneShot && a.oneShot && b.oneShot
  | .match e _ arms => e.oneShot && armsOneShot arms
  | .withH E _ h b => decide (E ≠ Operation.resume.effect) && h.oneShot && b.oneShot
  | .held _ hs body => exprsOneShot hs && body.oneShot

def exprsOneShot : List Expr → Bool
  | [] => true
  | e :: es => e.oneShot && exprsOneShot es

def fieldsOneShot : List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fields => e.oneShot && fieldsOneShot fields

def argsOneShot : List Arg → Bool
  | [] => true
  | .value e :: args => e.oneShot && argsOneShot args
  | .inout ⟨_, path⟩ :: args => pathOneShot path && argsOneShot args

def pathOneShot : List Projection → Bool
  | [] => true
  | .field _ :: path => pathOneShot path
  | .index i :: path => i.oneShot && pathOneShot path

def armsOneShot : List Arm → Bool
  | [] => true
  | ⟨_, _, body⟩ :: arms => body.oneShot && armsOneShot arms

end

/-- A body whose row holds `ρ` passes the check: it resumes at most as often as
the row allows. -/
def Expr.bodyOneShot (body : Expr) (ρ : Row) : Bool := body.oneShot && decide (body.resumes ≤ ρ.resumes)

/-- Every body of a program passes the check, and `main`, which no handler's
operation is, never resumes (handlers.resume-at-most-once and
handlers.resume-outside-operation). -/
def Program.OneShot (p : Program) : Prop :=
  (∀ d ∈ p.decls.fns, d.body.bodyOneShot d.row = true) ∧ p.main.oneShot = true ∧ p.main.resumes = 0

end Stilt
