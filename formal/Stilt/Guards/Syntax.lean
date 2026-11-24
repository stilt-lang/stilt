/-!
# The calculus of guards and list patterns

The patterns that the core calculus leaves out, and the guards of arms
(patterns.pattern-forms and patterns.guards): constants, the three forms of
list patterns, `[p₁, …, pₙ]`, `[p₁, …, pₙ, ..]` and `[p₁, …, pₙ, ..rest]`, and
an arm `p if c`, whose guard is tried with each way its pattern matches. Its
values are integers, Booleans, `()`, tuples, lists and `Option`; its expressions,
which guards and arm bodies are, read variables, add and compare integers, and
print, so that a run shows each time a guard runs (a guard may run more than
once, with its effects each time).

The theorems (`Stilt.Guards.Theorem`) say that a `match` takes the first arm
and the first way of its pattern whose guard is true, that an exhaustiveness
check which counts no arm with a guard or a constant
(patterns.guards-and-constants) is sound, so a checked `match` never falls
through, and that an irrefutable pattern (patterns.irrefutable-positions), the
pattern of a `let` without `else` and of a `for` head, matches every value of
its type.
-/

namespace Stilt.Guards

/-- A name of a variable. -/
abbrev Name := String

/-- A value: an integer, a Boolean, `()`, a tuple, a list, or an `Option`. -/
inductive Val where
  | int : Int → Val
  | bool : Bool → Val
  | unit : Val
  | tuple : List Val → Val
  | list : List Val → Val
  | none : Val
  | some : Val → Val
  deriving Repr, Inhabited

mutual

/-- Structural equality of values, which a constant pattern tests
(patterns.constants). -/
def Val.beq : Val → Val → Bool
  | .int a, .int b => a == b
  | .bool a, .bool b => a == b
  | .unit, .unit | .none, .none => true
  | .tuple as, .tuple bs | .list as, .list bs => Val.beqAll as bs
  | .some a, .some b => a.beq b
  | _, _ => false

def Val.beqAll : List Val → List Val → Bool
  | [], [] => true
  | a :: as, b :: bs => a.beq b && Val.beqAll as bs
  | _, _ => false

end

/-- A type. -/
inductive Ty where
  | int
  | bool
  | unit
  | tuple : List Ty → Ty
  | list : Ty → Ty
  | option : Ty → Ty
  deriving Repr, Inhabited

/-- A pattern (patterns.pattern-forms). A constant names its value, which a
constant pattern matches when the value is structurally equal
(patterns.constants); it is kept apart from a literal because exhaustiveness
reads the two differently. -/
inductive Pat where
  /-- `_`. -/
  | wild
  /-- A name, which binds what it matches. -/
  | bind : Name → Pat
  /-- An integer literal. -/
  | int : Int → Pat
  /-- `true` or `false`. -/
  | bool : Bool → Pat
  /-- `()`. -/
  | unit
  /-- A constant `C` of the given value. -/
  | const : Name → Val → Pat
  /-- `(p₁, …, pₙ)`. -/
  | tuple : List Pat → Pat
  /-- `None`. -/
  | none
  /-- `Some(p)`. -/
  | some : Pat → Pat
  /-- `[p₁, …, pₙ]`: lists of exactly `n` elements. -/
  | list : List Pat → Pat
  /-- `[p₁, …, pₙ, ..]`, and `[p₁, …, pₙ, ..rest]` with `rest`: lists of at
  least `n` elements, `rest` bound to the remaining ones as a list. -/
  | prefix : List Pat → Option Name → Pat
  /-- `p | q`. -/
  | or : Pat → Pat → Pat
  deriving Repr, Inhabited

/-- An expression of a guard or a body. -/
inductive Expr where
  | num : Int → Expr
  | bool : Bool → Expr
  | unit : Expr
  | var : Name → Expr
  /-- `a + b`, of integers. -/
  | add : Expr → Expr → Expr
  /-- `a < b`, of integers. -/
  | lt : Expr → Expr → Expr
  /-- `print(a)` followed by `b`, whose value it has. -/
  | print : Expr → Expr → Expr
  deriving Repr, Inhabited

/-- An arm, `p => body` or `p if g => body` (patterns.match). -/
structure Arm where
  pat : Pat
  guard : Option Expr
  body : Expr
  deriving Repr, Inhabited

/-- The variables in scope, innermost first, each with its value. -/
abbrev Env := List (Name × Val)

mutual

/-- Whether a pattern holds a constant, at any depth. -/
def Pat.hasConst : Pat → Bool
  | .const _ _ => true
  | .tuple ps | .list ps | .prefix ps _ => Pat.anyConst ps
  | .some p => p.hasConst
  | .or p q => p.hasConst || q.hasConst
  | _ => false

def Pat.anyConst : List Pat → Bool
  | [] => false
  | p :: ps => p.hasConst || Pat.anyConst ps

end

/-- Whether an arm counts for exhaustiveness: it has no guard and its pattern no
constant (patterns.guards-and-constants). -/
def Arm.counts (a : Arm) : Bool := a.guard.isNone && !a.pat.hasConst

mutual

/-- Whether a pattern is irrefutable by its form alone
(patterns.irrefutable-positions): `_`, a binding, `()`, a tuple of irrefutable
patterns, `[..]` and `[..rest]`, and an or-pattern with an irrefutable
alternative. -/
def Pat.irrefutable : Pat → Bool
  | .wild | .bind _ | .unit => true
  | .tuple ps => Pat.allIrrefutable ps
  | .prefix [] _ => true
  | .or p q => p.irrefutable || q.irrefutable
  | _ => false

def Pat.allIrrefutable : List Pat → Bool
  | [] => true
  | p :: ps => p.irrefutable && Pat.allIrrefutable ps

end

end Stilt.Guards
