import Stilt.Panics.Guards

/-!
# Counting loops

A `while` ends, and adds no `div`, when it counts (facts.counting-loops): its
condition compares a variable, the loop's **counter**, with a **bound**, by
`<`, `<=`, `>` or `>=`, alone or as the first conjunct of an `&&` chain; the
bound is made of literals, variables and lengths of lists, by `+`, `-` and `*`;
the body steps the counter toward the bound by a positive literal, as a
statement of its own block, with no `continue` before it; and neither the
body nor the condition writes the counter elsewhere or anything the bound
reads.

In the calculus `v += 2` is written `v = v + 2`, and a block is a chain of
`seq`s, whose statements are the expressions it chains.
-/

namespace Stilt

mutual

/-- Whether `e` can't end with a `continue` of a loop around it: every `continue`
it holds is in a loop of its own, or in a closure literal's body. -/
def Expr.contFree : Expr → Bool
  | .continue => false
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .fnRef _ _ _ | .method _ _ _
  | .closure _ _ _ _ | .loop _ => true
  | .record _ _ fields => fieldsContFree fields
  | .variant _ _ _ es => exprsContFree es
  | .list _ es => exprsContFree es
  | .op _ es | .view es => exprsContFree es
  | .field e _ => e.contFree
  | .index e i => e.contFree && i.contFree
  | .call callee args _ => callee.contFree && argsContFree args
  | .letIn _ _ init body => init.contFree && body.contFree
  | .varIn _ _ init body => init.contFree && body.contFree
  | .assign ⟨_, path⟩ value => pathContFree path && value.contFree
  | .seq a b => a.contFree && b.contFree
  | .if c _ a b => c.contFree && a.contFree && b.contFree
  | .match e _ arms => e.contFree && armsContFree arms
  | .for _ _ e _ => e.contFree
  | .raise e => e.contFree
  | .try e | .form _ e => e.contFree
  | .tryCatch e _ _ handler _ => e.contFree && handler.contFree
  | .while c _ => c.contFree
  | .return e => e.contFree
  | .perform _ e => e.contFree
  | .withH _ _ h b => h.contFree && b.contFree
  | .held _ hs body => exprsContFree hs && body.contFree

def exprsContFree : List Expr → Bool
  | [] => true
  | e :: es => e.contFree && exprsContFree es

def fieldsContFree : List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fields => e.contFree && fieldsContFree fields

def argsContFree : List Arg → Bool
  | [] => true
  | .value e :: args => e.contFree && argsContFree args
  | .inout ⟨_, path⟩ :: args => pathContFree path && argsContFree args

def pathContFree : List Projection → Bool
  | [] => true
  | .field _ :: path => pathContFree path
  | .index i :: path => i.contFree && pathContFree path

def armsContFree : List Arm → Bool
  | [] => true
  | ⟨_, _, body⟩ :: arms => body.contFree && armsContFree arms

end

/-- A bound: a literal, a variable, the length of a list a variable holds, or two
bounds by `+`, `-` or `*`. -/
inductive Bound where
  | lit (k : Int)
  | var (x : Name)
  | len (xs : Name)
  | arith (o : Arith) (k : IntTy) (a b : Bound)

/-- The expression a bound is. -/
def Bound.toExpr : Bound → Expr
  | .lit k => .int k
  | .var x => .var x
  | .len xs => .op (.list .len) [.var xs]
  | .arith o k a b => .op (.arith o k) [a.toExpr, b.toExpr]

/-- The variables a bound reads. -/
def Bound.reads : Bound → List Name
  | .lit _ => []
  | .var x | .len x => [x]
  | .arith _ _ a b => a.reads ++ b.reads

/-- The integer a bound has in a frame, as evaluating it gives. -/
def Bound.val (s : Copy.Frame) : Bound → Option Int
  | .lit k => some k
  | .var x => match s.lookup x with
    | some (.int k) => some k
    | _ => none
  | .len xs => match s.lookup xs with
    | some (.list vs) => (IntTy.i64.check vs.length).toOption
    | _ => none
  | .arith o k a b => match a.val s, b.val s with
    | some x, some y => (k.arith o x y).toOption
    | _, _ => none

/-- The bound an expression is, if it is one. -/
def Expr.bound? : Expr → Option Bound
  | .int k => some (.lit k)
  | .var x => some (.var x)
  | .op (.list .len) [.var xs] => some (.len xs)
  | .op (.arith o k) [a, b] =>
    if o == .add || o == .sub || o == .mul then
      match a.bound?, b.bound? with
      | some a', some b' => some (.arith o k a' b')
      | _, _ => none
    else none
  | _ => none

/-- Whether a comparison counts: whether the counter grows toward the bound, for
`<` and `<=`, or shrinks, for `>` and `>=`. -/
def Cmp.counts : Cmp → Option Bool
  | .lt | .le => some true
  | .gt | .ge => some false
  | _ => none

/-- The readings of a condition that counts: its counter, the comparison with the
counter on the left, and its bound. A comparison of two variables has two, one
for each side as the counter. -/
def Expr.countings : Expr → List (Name × Cmp × Bound)
  | .op (.compare c _) [l, r] =>
    (match l.readVar?, r.bound?, c.counts with
      | some v, some b, some _ => [(v, c, b)]
      | _, _, _ => []) ++
    (match r.readVar?, l.bound?, c.mirror.counts with
      | some v, some b, some _ => [(v, c.mirror, b)]
      | _, _, _ => [])
  | .if a _ _ y => if y.isBool false then a.countings else []
  | _ => []

/-- Whether a value moves `v` toward a bound it grows to, or shrinks to: `v + k`
or `v - k`, with `k` a positive literal. -/
def Expr.movesBy (v : Name) (grow : Bool) : Expr → Bool
  | .op (.arith o _) [l, r] =>
    l.readVar? == some v && (r.intLit?.any fun k => decide (0 < k)) && o == (if grow then .add else .sub)
  | _ => false

/-- Whether `e` is a step of `v`: `v = v + k` or `v = v - k`. -/
def Expr.isStep (v : Name) (grow : Bool) : Expr → Bool
  | .assign ⟨x, p⟩ value => x == v && p.isEmpty && value.movesBy v grow
  | _ => false

/-- Whether a block steps `v`: one of its statements is the step, no `continue`
comes before it, and no other statement writes `v`. -/
def Expr.steps (v : Name) (grow : Bool) : Expr → Bool
  | .seq a b =>
    (a.steps v grow && decide (v ∉ b.writes)) ||
      (a.contFree && decide (v ∉ a.writes) && b.steps v grow)
  | e => e.isStep v grow

/-- Whether `while c { body }` counts, by one reading of its condition (facts.counting-loops):
the condition compares a variable, its counter, with a bound, by `<`, `<=`, `>` or `>=`,
alone or as the first conjunct of an `&&` chain, mirrored or not; the bound is made of
literals, variables and lengths of variables' lists by `+`, `-` and `*`, none of which the
body or the condition writes; and the body steps the counter toward the bound as a statement
of its own block, with no `continue` before it, and writes it nowhere else (`Expr.steps`).
Narrower than the Reference: a step is by a positive literal, not by a name known positive,
a bound holds no constant, and a length is of a variable that the body doesn't write at all,
not of a place whose length it doesn't change. -/
def Expr.countsIn (c body : Expr) : Bool :=
  c.countings.any fun (v, cmp, b) => match cmp.counts with
    | some grow => body.steps v grow && decide (v ∉ c.writes) &&
        b.reads.all (fun x => decide (x ∉ body.writes ∧ x ∉ c.writes))
    | none => false

end Stilt
