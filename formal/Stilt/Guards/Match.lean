import Stilt.Guards.Syntax

/-!
# Matching with guards

`Pat.ways p v` lists every way in which `p` matches `v`, each as the bindings
it makes, in the order a guard tries them (patterns.guards): an or-pattern's
first alternative's ways come before its second's, and of the parts of a tuple
or a list, the leftmost part's ways vary slowest. A pattern without an
or-pattern has at most one way. A `match` tries its arms in order, and an arm
with a guard tries the guard with each way until it is true, printing what the
guard prints each time; the first arm and way that pass are taken
(patterns.match).
-/

namespace Stilt.Guards

/-- What `..rest` binds: the remaining elements, as a list, or nothing for a
bare `..`. -/
def Pat.rest : Option Name → List Val → Env
  | Option.some r, vs => [(r, .list vs)]
  | Option.none, _ => []

mutual

/-- Every way in which a pattern matches a value, in order. -/
def Pat.ways : Pat → Val → List Env
  | .wild, _ => [[]]
  | .bind x, v => [[(x, v)]]
  | .int n, .int m => if n = m then [[]] else []
  | .bool b, .bool c => if b = c then [[]] else []
  | .unit, .unit => [[]]
  | .const _ c, v => if c.beq v then [[]] else []
  | .tuple ps, .tuple vs => Pat.waysAll ps vs
  | .none, .none => [[]]
  | .some p, .some v => p.ways v
  | .list ps, .list vs => Pat.waysAll ps vs
  | .prefix ps r, .list vs =>
    if ps.length ≤ vs.length then
      (Pat.waysAll ps (vs.take ps.length)).map (· ++ Pat.rest r (vs.drop ps.length))
    else []
  | .or p q, v => p.ways v ++ q.ways v
  | _, _ => []

/-- The ways in which patterns match values position by position. -/
def Pat.waysAll : List Pat → List Val → List Env
  | [], [] => [[]]
  | p :: ps, v :: vs => (p.ways v).flatMap fun w => (Pat.waysAll ps vs).map (w ++ ·)
  | _, _ => []

end

/-- Evaluates an expression: its value, and what it prints, in order; `none`
for an evaluation gone wrong, which typing rules out. -/
def eval (ρ : Env) : Expr → Option (Val × List Val)
  | .num k => some (.int k, [])
  | .bool b => some (.bool b, [])
  | .unit => some (.unit, [])
  | .var x => (ρ.lookup x).map (·, [])
  | .add a b =>
    match eval ρ a, eval ρ b with
    | some (.int x, oa), some (.int y, ob) => some (.int (x + y), oa ++ ob)
    | _, _ => none
  | .lt a b =>
    match eval ρ a, eval ρ b with
    | some (.int x, oa), some (.int y, ob) => some (.bool (decide (x < y)), oa ++ ob)
    | _, _ => none
  | .print a b =>
    match eval ρ a, eval ρ b with
    | some (va, oa), some (vb, ob) => some (vb, oa ++ va :: ob)
    | _, _ => none

/-- Tries a guard with each way in turn: the first way for which it is true,
or `none` when it is true for none, with what it printed; `none` outside for a
guard gone wrong. -/
def tryWays (ρ : Env) (g : Expr) : List Env → Option (Option Env × List Val)
  | [] => some (none, [])
  | w :: ws =>
    match eval (w ++ ρ) g with
    | some (.bool true, out) => some (some w, out)
    | some (.bool false, out) => (tryWays ρ g ws).map fun (r, out') => (r, out ++ out')
    | _ => none

/-- The way an arm takes a value, if it does, with what its guard printed. An
arm without a guard takes the first way its pattern matches. -/
def Arm.take (ρ : Env) (a : Arm) (v : Val) : Option (Option Env × List Val) :=
  match a.guard with
  | none => some ((a.pat.ways v).head?, [])
  | some g => tryWays ρ g (a.pat.ways v)

/-- The first arm that takes the value, with the way it takes it, or `none`
when no arm does, with what the guards printed. -/
def select (ρ : Env) : List Arm → Val → Option (Option (Arm × Env) × List Val)
  | [], _ => some (none, [])
  | a :: arms, v =>
    match a.take ρ v with
    | some (some w, out) => some (some (a, w), out)
    | some (none, out) => (select ρ arms v).map fun (r, out') => (r, out ++ out')
    | none => none

/-- How a `match`, a `let` or a `for` ends: with a value and what it printed,
with no arm that takes the value, or gone wrong. -/
inductive Out where
  | done : Val → List Val → Out
  | noArm : List Val → Out
  | stuck : Out
  deriving Repr

/-- `match v { arms }`: the body of the arm taken, in the bindings of its way. -/
def runMatch (ρ : Env) (v : Val) (arms : List Arm) : Out :=
  match select ρ arms v with
  | some (some (a, w), out) =>
    match eval (w ++ ρ) a.body with
    | some (r, out') => .done r (out ++ out')
    | none => .stuck
  | some (none, out) => .noArm out
  | none => .stuck

/-- `let p = v` followed by `body`: the body in the bindings of the first way. -/
def runLet (ρ : Env) (p : Pat) (v : Val) (body : Expr) : Out :=
  match (p.ways v).head? with
  | some w =>
    match eval (w ++ ρ) body with
    | some (r, out) => .done r out
    | none => .stuck
  | none => .noArm []

/-- `for p in vs { body }`: the body for each element, in the bindings of its
first way, ending with `()`. -/
def runFor (ρ : Env) (p : Pat) (body : Expr) : List Val → Out
  | [] => .done .unit []
  | v :: vs =>
    match runLet ρ p v body, runFor ρ p body vs with
    | .done _ out, .done r out' => .done r (out ++ out')
    | .done _ out, .noArm out' => .noArm (out ++ out')
    | .noArm out, _ => .noArm out
    | _, _ => .stuck

end Stilt.Guards
