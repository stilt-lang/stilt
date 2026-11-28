import Stilt.Declarations

/-!
# A body's count

The count that decides whether the analysis keeps only each term's bounds in a body
(facts.large-bodies): the `let` and `var` bindings of integer types and of lists that the body
writes in its own text, outside its closure literals, three for each `for` over a range, one
for each `for` over another iterable whose variable is an integer or a list, and one, for zero.
-/

namespace Stilt

/-- Whether a binding of the type `τ` counts: an integer or a list. -/
def Ty.counts : Ty → Bool
  | .int _ | .list _ => true
  | _ => false

/-- What a `for` over the iterable `e` with a variable of the type `τ` adds to the count. -/
def forCount (τ : Ty) : Expr → Nat
  | .op (.list (.range _)) _ => 3
  | _ => if τ.counts then 1 else 0

mutual

/-- The bindings of integers and lists that `e` writes outside its closure literals, and three
for each `for` over a range. -/
def Expr.bindCount : Expr → Nat
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _
  | .method _ _ _ | .closure _ _ _ _ => 0
  | .held _ hs body => exprsBindCount hs + body.bindCount
  | .record _ _ fields => fieldsBindCount fields
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => exprsBindCount es
  | .field e _ | .raise e | .try e | .form _ e | .return e | .loop e | .perform _ e => e.bindCount
  | .index a b | .seq a b | .while a b | .tryCatch a _ _ b _ | .withH _ _ a b =>
    a.bindCount + b.bindCount
  | .letIn _ τ a b | .varIn _ τ a b => (if τ.counts then 1 else 0) + a.bindCount + b.bindCount
  | .for _ τ a b => forCount τ a + a.bindCount + b.bindCount
  | .call callee args _ => callee.bindCount + argsBindCount args
  | .assign ⟨_, path⟩ value => pathBindCount path + value.bindCount
  | .if c _ a b => c.bindCount + a.bindCount + b.bindCount
  | .match e _ arms => e.bindCount + armsBindCount arms

def exprsBindCount : List Expr → Nat
  | [] => 0
  | e :: es => e.bindCount + exprsBindCount es

def fieldsBindCount : List (Name × Expr) → Nat
  | [] => 0
  | (_, e) :: fields => e.bindCount + fieldsBindCount fields

def argsBindCount : List Arg → Nat
  | [] => 0
  | .value e :: args => e.bindCount + argsBindCount args
  | .inout ⟨_, path⟩ :: args => pathBindCount path + argsBindCount args

def pathBindCount : List Projection → Nat
  | [] => 0
  | .field _ :: path => pathBindCount path
  | .index i :: path => i.bindCount + pathBindCount path

def armsBindCount : List Arm → Nat
  | [] => 0
  | ⟨_, _, guard, body⟩ :: arms => guardBindCount guard + body.bindCount + armsBindCount arms

def guardBindCount : Option Expr → Nat
  | none => 0
  | some g => g.bindCount

end

/-- Whether a body is large: its count, one for zero among it, is above 64 (facts.large-bodies). -/
def Expr.large (e : Expr) : Bool := decide (64 < e.bindCount + 1)

end Stilt
