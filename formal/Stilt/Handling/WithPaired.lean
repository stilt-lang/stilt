import Stilt.Declarations
import Stilt.Rows.Types

/-!
# Handlers around a caller's effects

handlers.with-pairing, E0516: a `with` handles every performance of its effect that reaches it,
so a call in its block whose callee's row holds a row variable of the enclosing function, which
the caller instantiates, could hand the handler a performance that belongs to the caller. The
call is allowed only when that row also holds the handler's effect and the enclosing signature
pairs the variable with it, as effects.catch-around-row-variables allows a call in a `catch`'s
operand. The check is one pass over a body, which follows the types of its variables, written at
their binders, to find a callee's row as the call instantiates it.
-/

namespace Stilt

/-- A row of the signature of `d` holds the row variable `v` beside the effect `E`: the signature
pairs `v` with `E` (handlers.with-pairing). -/
def FnDecl.pairsEffect (d : FnDecl) (v E : Name) : Bool :=
  (paramRows (d.params.map Param.sig) ++ [d.row]).any fun ρ => ρ.vars.contains v && ρ.effects.contains E

/-- The row of a callee as the call instantiates it, where the pass follows its type: a variable
of a function type, a function named at row arguments, a closure literal, and a call whose result
is a function. Another callee, a field or a pattern's binding, gives none. -/
def Expr.calleeRow (D : Decls) (Γ : List (Name × Ty)) : Expr → Option Row
  | .var x | .move x => match Γ.lookup x with
    | some (.fn _ _ ρ) => some ρ
    | _ => none
  | .fnRef f _ rs => (D.fn? f).map fun d => d.row.substRows (d.rowParams.zip rs)
  | .closure _ _ ρ _ => some ρ
  | .call _ _ (.fn _ _ ρ) => some ρ
  | _ => none

/-- A call through the row `σ` inside the block of a `with` of `E`, in the body of `d`: each row
variable of `d` that `σ` holds comes with `E` in `σ`, and `d`'s signature pairs it with `E`. -/
def FnDecl.withAllows (d : FnDecl) (E : Name) (σ : Row) : Bool :=
  σ.vars.all fun v => !d.rowParams.contains v || (σ.effects.contains E && d.pairsEffect v E)

mutual

/-- No call in `e`, in the body of `d`, breaks handlers.with-pairing, where `E` is the effect of
the nearest `with` whose block holds `e`, outside every closure literal in that block. A closure
literal's body is outside every `with` around it, and a `with` inside the block checks the calls
of its own block: the exceptions that effects.catch-around-row-variables gives a `catch`. -/
def Expr.withPaired (D : Decls) (d : FnDecl) (Γ : List (Name × Ty)) (E : Option Name) :
    Expr → Bool
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _
  | .method _ _ _ => true
  | .record _ _ fields => fieldsWithPaired D d Γ E fields
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => exprsWithPaired D d Γ E es
  | .field e _ | .raise e | .perform _ e | .try e | .form _ e | .loop e | .return e =>
    e.withPaired D d Γ E
  | .index a b | .seq a b | .while a b => a.withPaired D d Γ E && b.withPaired D d Γ E
  | .withH eff _ h b => h.withPaired D d Γ E && b.withPaired D d Γ (some eff)
  | .closure ps _ _ body => body.withPaired D d (ps.map (fun p => (p.name, p.type)) ++ Γ) none
  | .call f args _ =>
    (match E, f.calleeRow D Γ with
      | some eff, some σ => d.withAllows eff σ
      | _, _ => true) &&
      f.withPaired D d Γ E && argsWithPaired D d Γ E args
  | .letIn x τ init body | .varIn x τ init body | .for x τ init body =>
    init.withPaired D d Γ E && body.withPaired D d ((x, τ) :: Γ) E
  | .held ns hs body => exprsWithPaired D d Γ E hs && body.withPaired D d (ns ++ Γ) E
  | .assign ⟨_, path⟩ v => pathWithPaired D d Γ E path && v.withPaired D d Γ E
  | .if c _ a b => c.withPaired D d Γ E && a.withPaired D d Γ E && b.withPaired D d Γ E
  | .match e _ arms => e.withPaired D d Γ E && armsWithPaired D d Γ E arms
  | .tryCatch e τ x h _ => e.withPaired D d Γ E && h.withPaired D d ((x, τ) :: Γ) E

def exprsWithPaired (D : Decls) (d : FnDecl) (Γ : List (Name × Ty)) (E : Option Name) :
    List Expr → Bool
  | [] => true
  | e :: es => e.withPaired D d Γ E && exprsWithPaired D d Γ E es

def fieldsWithPaired (D : Decls) (d : FnDecl) (Γ : List (Name × Ty)) (E : Option Name) :
    List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fields => e.withPaired D d Γ E && fieldsWithPaired D d Γ E fields

def argsWithPaired (D : Decls) (d : FnDecl) (Γ : List (Name × Ty)) (E : Option Name) :
    List Arg → Bool
  | [] => true
  | .value e :: args => e.withPaired D d Γ E && argsWithPaired D d Γ E args
  | .inout ⟨_, path⟩ :: args => pathWithPaired D d Γ E path && argsWithPaired D d Γ E args

def pathWithPaired (D : Decls) (d : FnDecl) (Γ : List (Name × Ty)) (E : Option Name) :
    List Projection → Bool
  | [] => true
  | .field _ :: path => pathWithPaired D d Γ E path
  | .index i :: path => i.withPaired D d Γ E && pathWithPaired D d Γ E path

/-- A pattern's bindings hide the variables of their names, whose types the pass doesn't follow. -/
def armsWithPaired (D : Decls) (d : FnDecl) (Γ : List (Name × Ty)) (E : Option Name) :
    List Arm → Bool
  | [] => true
  | ⟨_, binders, guard, body⟩ :: arms =>
    let Γ' := binders.map (·, Ty.unit) ++ Γ
    guardWithPaired D d Γ' E guard && body.withPaired D d Γ' E && armsWithPaired D d Γ E arms

def guardWithPaired (D : Decls) (d : FnDecl) (Γ : List (Name × Ty)) (E : Option Name) :
    Option Expr → Bool
  | none => true
  | some g => g.withPaired D d Γ E

end

/-- handlers.with-pairing, E0516: no call in the body of a function of the program, inside the
block of a `with`, has a callee whose row, as the call instantiates it, holds a row variable of
the function, unless that row holds the `with`'s effect too and the function's signature pairs
the variable with it. The pass finds the row of a callee that is a variable, a named function, a
closure literal or a call's result; a call of a field or of a pattern's binding is left out. No
promise rests on the check: the calculus's effects are nominal, so a performance that a handler
takes from a caller's row variable has the operation's types, and runs as the Reference runs it.
`main` has no row variable. -/
def Program.WithPaired (p : Program) : Prop :=
  ∀ d ∈ p.decls.fns, d.body.withPaired p.decls d (d.params.map fun q => (q.name, q.type)) none = true

end Stilt
