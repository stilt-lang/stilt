import Stilt.NoEscape
import Stilt.Typing.Tasks

/-!
# Scopes that escape

tasks.scope-that-escapes: a binding of type `Scope<E>` is used only as the receiver of `spawn`
or as an argument given to a parameter of type `Scope<E>`. Any other use, a capture in a task's
function included, is a scope that escapes (E0434), so a scope never outlives the call of
`task.scope` that made it. The check is the one for a non-escaping parameter (effects.no-escape,
`Stilt.NoEscape`), with a parameter of type `Scope<E>` among the places a scope may go:
`Expr.scopesKept` reads it as `Expr.noEscape` does, the bindings of a scope's type for the
non-escaping parameters, and `Program.ScopesKept` asks it of every body of a program and of
`main`. Scopes are the calculus's records of `Scope<E>` (`Stilt.Typing.Tasks`), so the check
reads a binding's type where its binder writes it.

The model checks the rule and leaves out what it is for: a scope holds nothing a run reads, so no
run can tell a scope that outlives its `task.scope`.
-/

namespace Stilt

/-- Whether a type is a scope's, `Scope<E>`. -/
def Ty.isScope : Ty → Bool
  | .record R _ => R == scopeName
  | _ => false

/-- The names of the parameters whose types are scopes'. -/
def scopeParams (ps : List Param) : List Name := (ps.filter (·.type.isScope)).map Param.name

/-- The scopes `N` once `x` is bound at the type `τ`: `x` among them when `τ` is a scope's, and
hidden otherwise (expressions.shadowing). -/
def bindScope (x : Name) (τ : Ty) (N : List Name) : List Name :=
  if τ.isScope then x :: N.removeAll [x] else N.removeAll [x]

/-- For each parameter of the function that a callee names, whether a scope may be given to
it: a non-escaping parameter, or one whose type is a scope's. A callee that isn't a declared
function's name has none, as for `Decls.passing`. -/
def Decls.scopePassing (D : Decls) : Expr → List Bool
  | .fnRef f _ _ => (D.fn? f).elim [] fun d => d.params.map fun p => p.implicit.isSome || p.type.isScope
  | _ => []

mutual

/-- No scope among `N` escapes from `e`. `allowed` says that `e` is the receiver of `s.spawn`, a
callee, or an argument given to a non-escaping parameter or to one of a scope's type of the
function a call names: there `e` may be one of `N`, or a closure literal that names them
(tasks.scope-that-escapes). Elsewhere neither may occur, so a task's function that captures a
scope keeps it. -/
def Expr.scopesKept (D : Decls) (N : List Name) (allowed : Bool) : Expr → Bool
  | .var x | .move x => allowed || !N.contains x
  | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _ | .method _ _ _ => true
  | .record _ _ fields => fieldsScopesKept D N fields
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => exprsScopesKept D N es
  | .form .scopeSpawn (.letIn r _ s rest) =>
    s.scopesKept D N true && rest.scopesKept D (N.removeAll [r]) false
  | .field e _ | .raise e | .perform _ e | .try e | .form _ e | .loop e | .return e =>
    e.scopesKept D N false
  | .index a b | .seq a b | .withH _ _ a b | .while a b =>
    a.scopesKept D N false && b.scopesKept D N false
  | .closure ps _ _ body =>
    let N' := N.removeAll (ps.map Param.name)
    (allowed || !body.names N') && body.scopesKept D (scopeParams ps ++ N') false
  | .call f args _ => f.scopesKept D N true && argsScopesKept D N (D.scopePassing f) args
  | .letIn x τ init body | .varIn x τ init body =>
    init.scopesKept D N false && body.scopesKept D (bindScope x τ N) false
  | .held ns hs body =>
    exprsScopesKept D N hs && body.scopesKept D (N.removeAll (ns.map (·.1))) false
  | .assign ⟨x, path⟩ v => !N.contains x && pathScopesKept D N path && v.scopesKept D N false
  | .if c _ a b => c.scopesKept D N false && a.scopesKept D N false && b.scopesKept D N false
  | .match e _ arms => e.scopesKept D N false && armsScopesKept D N arms
  | .for x τ e body => e.scopesKept D N false && body.scopesKept D (bindScope x τ N) false
  | .tryCatch e τ x h _ => e.scopesKept D N false && h.scopesKept D (bindScope x τ N) false

/-- No scope of `N` escapes from the expressions of a list. -/
def exprsScopesKept (D : Decls) (N : List Name) : List Expr → Bool
  | [] => true
  | e :: es => e.scopesKept D N false && exprsScopesKept D N es

/-- No scope of `N` escapes from the fields of a record literal. -/
def fieldsScopesKept (D : Decls) (N : List Name) : List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fields => e.scopesKept D N false && fieldsScopesKept D N fields

/-- No scope of `N` escapes from the arguments of a call, given for each of the callee's
parameters, in order, whether a scope may be given to it. -/
def argsScopesKept (D : Decls) (N : List Name) : List Bool → List Arg → Bool
  | _, [] => true
  | passing, .value e :: args =>
    e.scopesKept D N (passing.headD false) && argsScopesKept D N passing.tail args
  | passing, .inout ⟨x, path⟩ :: args =>
    !N.contains x && pathScopesKept D N path && argsScopesKept D N passing.tail args

/-- No scope of `N` escapes from the indexes of a place. -/
def pathScopesKept (D : Decls) (N : List Name) : List Projection → Bool
  | [] => true
  | .field _ :: path => pathScopesKept D N path
  | .index i :: path => i.scopesKept D N false && pathScopesKept D N path

/-- No scope of `N` escapes from the arms of a `match`, whose binders hide it. -/
def armsScopesKept (D : Decls) (N : List Name) : List Arm → Bool
  | [] => true
  | ⟨_, binders, guard, body⟩ :: arms =>
    guardScopesKept D (N.removeAll binders) guard && body.scopesKept D (N.removeAll binders) false &&
      armsScopesKept D N arms

/-- No scope of `N` escapes from an arm's guard. -/
def guardScopesKept (D : Decls) (N : List Name) : Option Expr → Bool
  | none => true
  | some g => g.scopesKept D N false

end

/-- E0434 (tasks.scope-that-escapes): no scope escapes from a body of the program, its
parameters of a scope's type and every binding of one inside it among the scopes, nor from
`main`. -/
def Program.ScopesKept (p : Program) : Prop :=
  (∀ d ∈ p.decls.fns, d.body.scopesKept p.decls (scopeParams d.params) false = true) ∧
    p.main.scopesKept p.decls [] false = true

end Stilt
