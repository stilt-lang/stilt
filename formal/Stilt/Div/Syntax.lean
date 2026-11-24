/-!
# The calculus of descending recursion

facts.descending-self-calls lets a function call itself under `without div` when, at every
self-call, the argument in one parameter's position holds a strict part of
that parameter: a part reached through at least one step, a field, a tuple
element or a variant's payload, as a pattern binds it. facts.descending-self-calls rests on values
being finite trees, so that a chain of strict parts ends.

This calculus states that rule on first-order functions over binary trees, the
smallest values with parts: an integer, a leaf, or a node of two trees. A body
reads its variables, adds integers, builds leaves and nodes, matches a variable
against a node, binding its two parts, and calls a function of the program by
its index. The other sites of facts.div, `while` and calls through stored
function values, are left out of the calculus: they are sites in every case,
so no checked program holds one. A `for` loop over a finite list is left out
as well.

Variables are de Bruijn indexes into the environment: a call's environment is
its arguments, the first at index 0, and matching a node pushes its left part,
then its right, in front, so that the left part is variable 0.
-/

namespace Stilt.Div

/-- A value: an integer, a leaf, or a node of two values. Nothing holds a
reference to the value that holds it, so every value is a finite tree. -/
inductive Val where
  | num : Int → Val
  | leaf : Val
  | node : Val → Val → Val
  deriving Repr, DecidableEq

/-- The size of a value: its count of constructors. A part of a node is
smaller than the node. -/
def Val.size : Val → Nat
  | .num _ => 1
  | .leaf => 1
  | .node l r => l.size + r.size + 1

mutual
/-- An expression of a body. -/
inductive Expr where
  | var : Nat → Expr
  | num : Int → Expr
  | add : Expr → Expr → Expr
  | leaf : Expr
  | node : Expr → Expr → Expr
  /-- `case x e₁ e₂` is `e₂`, with the two parts of `x` bound, when `x`
  holds a node, and `e₁` otherwise. -/
  | case : Nat → Expr → Expr → Expr
  /-- A call of the program's function of this index. -/
  | call : Nat → Args → Expr

/-- The arguments of a call. -/
inductive Args where
  | nil : Args
  | cons : Expr → Args → Args
end

/-- A function: how many parameters it takes, the parameter whose strict
parts its self-calls pass (facts.descending-self-calls), and its body. -/
structure Fn where
  arity : Nat
  desc : Nat
  body : Expr

/-- A program: its functions, called by their indexes. -/
abbrev Prog := List Fn

/-- The value a missing variable reads, which no checked program reads. -/
def dflt : Val := .num 0

/-- The sum of two integers; any other operand counts as 0. -/
def plus : Val → Val → Val
  | .num a, .num b => .num (a + b)
  | .num a, _ => .num a
  | _, .num b => .num b
  | _, _ => .num 0

mutual
/-- Evaluation with fuel: `none` when the fuel runs out, as a call that never
ends does for every fuel. -/
def eval (P : Prog) : Nat → List Val → Expr → Option Val
  | 0, _, _ => none
  | _ + 1, ρ, .var i => some (ρ.getD i dflt)
  | _ + 1, _, .num k => some (.num k)
  | n + 1, ρ, .add a b => do
      let x ← eval P n ρ a
      let y ← eval P n ρ b
      some (plus x y)
  | _ + 1, _, .leaf => some .leaf
  | n + 1, ρ, .node a b => do
      let x ← eval P n ρ a
      let y ← eval P n ρ b
      some (.node x y)
  | n + 1, ρ, .case i e₁ e₂ =>
      match ρ.getD i dflt with
      | .node l r => eval P n (l :: r :: ρ) e₂
      | _ => eval P n ρ e₁
  | n + 1, ρ, .call f as => do
      let vs ← evalArgs P n ρ as
      let fn ← P[f]?
      eval P n vs fn.body

/-- The values of a call's arguments, in order. -/
def evalArgs (P : Prog) : Nat → List Val → Args → Option (List Val)
  | 0, _, _ => none
  | _ + 1, _, .nil => some []
  | n + 1, ρ, .cons e as => do
      let v ← eval P n ρ e
      let vs ← evalArgs P n ρ as
      some (v :: vs)
end

/-- A call of the function `f` on the values `vs`, with fuel `n`. -/
def evalCall (P : Prog) (n : Nat) (f : Nat) (vs : List Val) : Option Val := do
  let fn ← P[f]?
  eval P n vs fn.body

end Stilt.Div
