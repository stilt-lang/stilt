import Stilt.Div.Syntax

/-!
# The check of descending self-calls

facts.div and facts.descending-self-calls as a check of each body. A body may call a function of
the program declared before it, which is never in its recursive group, and
itself only when the argument in its descending parameter's position names a
variable that holds a strict part of that parameter. The check follows which
variables hold the parameter itself and which a strict part: matching either
binds two strict parts.
-/

namespace Stilt.Div

/-- What a variable holds, as far as the check knows. -/
inductive Role where
  | other
  | whole
  | part
  deriving DecidableEq, Repr

/-- The role of a variable, `other` past the known ones. -/
def roleOf (R : List Role) (i : Nat) : Role := R.getD i .other

/-- What a variable that a match binds holds: a strict part when the matched
variable holds the parameter or a strict part of it. -/
def partOf : Role → Role
  | .other => .other
  | _ => .part

/-- Whether the argument at position `k` names a variable that holds a strict
part of the descending parameter. -/
def argPart (R : List Role) : Nat → Args → Bool
  | 0, .cons (.var y) _ => roleOf R y == .part
  | 0, _ => false
  | j + 1, .cons _ as => argPart R j as
  | _ + 1, .nil => false

mutual
/-- Whether a body's expression passes the check of facts.descending-self-calls, in function
`self`, whose descending parameter is at position `k`. -/
def ok (self k : Nat) : List Role → Expr → Bool
  | _, .var _ => true
  | _, .num _ => true
  | R, .add a b => ok self k R a && ok self k R b
  | _, .leaf => true
  | R, .node a b => ok self k R a && ok self k R b
  | R, .case i e₁ e₂ =>
      ok self k R e₁ && ok self k (partOf (roleOf R i) :: partOf (roleOf R i) :: R) e₂
  | R, .call f as =>
      okArgs self k R as && (decide (f < self) || (f == self && argPart R k as))

/-- Whether every argument passes the check. -/
def okArgs (self k : Nat) : List Role → Args → Bool
  | _, .nil => true
  | R, .cons e as => ok self k R e && okArgs self k R as
end

/-- The roles of a body's parameters: the descending one is the whole value
whose strict parts the self-calls pass. -/
def roles (arity k : Nat) : List Role :=
  (List.range arity).map fun j => if j = k then .whole else .other

/-- A program whose every body passes the check (facts.without-div). -/
def Checked (P : Prog) : Prop :=
  ∀ i (h : i < P.length), ok i P[i].desc (roles P[i].arity P[i].desc) P[i].body = true

end Stilt.Div
