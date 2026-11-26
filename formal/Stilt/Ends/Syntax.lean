import Stilt.Ends.Counting
import Stilt.Ends.Roles

/-!
# Code without `div`

Whether code holds no site of `div` (facts.div): no `loop`, no `while` but one
that counts (facts.counting-loops, `Stilt.Ends.Counting`), and
every call made of a function that the program names, `f(…)`, or of a closure
literal where it is written, `(|x| …)(…)`, never of a function value that
anything else gives, and no performance, which calls the handler's clause
(handlers.implicit-effects-and-capabilities); a `with` adds nothing, and neither does a
`when` (shared.when-on-value-already-held). Naming a function adds `div` unless it is one
of the functions a limit covers (`Limited`). The functions it covers are **ranked**
(`Decls.Ranked`): a body names only functions ranked below its own, so no two of them are
in one recursive group, and calls its own function only when the call goes down as the
function's `Descent` says: its argument at the position of the descending parameter holds a
strict part of that parameter (facts.descending-self-calls), or it steps the function's
counter toward its bound under a test that shows the counter short of it
(facts.shrinking-recursion), as the roles of the body's variables say (`Stilt.Ends.Roles`).

`main` is ranked above every function, so it names any that the limit covers.
-/

namespace Stilt

/-- Whether a call of `e` adds no `div` of its own: `e` names a function, or is a closure
literal, which the call runs where it is written (facts.div). -/
def Expr.callable : Expr → Bool
  | .fnRef _ _ _ | .closure _ _ _ _ => true
  | _ => false

/-- The descending argument of a call: whether the argument at position `k` gives a strict
part of the descending parameter (facts.descending-self-calls). -/
def argPart (R : Roles) : Nat → List Arg → Bool
  | 0, .value e :: _ => e.roleIn R == .part
  | k + 1, _ :: args => argPart R k args
  | _, _ => false

/-- Whether the argument at position `k` meets `ok`. -/
def argWith (ok : Expr → Bool) : Nat → List Arg → Bool
  | 0, .value e :: _ => ok e
  | k + 1, _ :: args => argWith ok k args
  | _, _ => false

/-- The bound of a function's counter (facts.shrinking-recursion): a literal, or the
parameter at a position, which every self-call passes unchanged. -/
inductive ShrinkBound where
  | lit (c : Int)
  | param (j : Nat)
  deriving DecidableEq, Repr

/-- How a function's self-calls go down: on strict parts of the parameter at position `k`
(facts.descending-self-calls), or, for the integer parameter at `k`, toward its bound, up when
`grow` and down otherwise (facts.shrinking-recursion). -/
inductive Descent where
  | parts (k : Nat)
  | shrinks (k : Nat) (grow : Bool) (bound : ShrinkBound)
  deriving DecidableEq, Repr

/-- Whether an argument steps a guarded counter toward its bound: `p + s` or `p - s`, with
`s` a positive literal. -/
def Expr.shrinksIn (R : Roles) (grow : Bool) : Expr → Bool
  | .op (.arith o t) [l, r] =>
    l.readVar?.any fun p => R.of p == .guarded && (Expr.op (.arith o t) [l, r]).movesBy p grow
  | _ => false

/-- Whether a self-call passes its bound unchanged, when the bound is a parameter. -/
def ShrinkBound.passedIn (R : Roles) : ShrinkBound → List Arg → Bool
  | .lit _, _ => true
  | .param j, args => argWith (fun e => e.roleIn R == .limit) j args

/-- Whether a self-call goes down as its function's self-calls do: its argument at the
descending position holds a strict part of the descending parameter, or it steps the
counter, short of its bound, toward it, and passes the bound unchanged. -/
def Descent.calls (R : Roles) : Descent → List Arg → Bool
  | .parts k, args => argPart R k args
  | .shrinks k grow b, args => argWith (Expr.shrinksIn R grow) k args && b.passedIn R args

/-- Whether a reading of a test shows a counter short of its bound: it compares a counter
with the function's bound, by `<` or `<=` when the counter grows and by `>` or `>=` when it
shrinks, mirrored or not; the bound is the function's literal, or a variable that holds the
parameter its bound is. -/
def guardReading (R : Roles) (grow : Bool) (b : ShrinkBound) : Name × Cmp × Bound → Bool
  | (v, cmp, bnd) => (R.of v == .counter || R.of v == .guarded) && cmp.counts == some grow &&
    match b, bnd with
    | .lit c, .lit c' => c == c'
    | .param _, .var q => R.of q == .limit
    | _, _ => false

/-- The test that holds when a comparison doesn't, `false` for any other test. -/
def Expr.negated : Expr → Expr
  | .op (.compare cmp t) [l, r] => .op (.compare cmp.negate t) [l, r]
  | _ => .bool false

section

-- Where code is: in the body of the function `f`, whose self-calls go down as `d` says,
-- when `me = some (f, d)`, and in `main`'s when `me = none`.
variable (lim : Limited) (B : Name → Nat) (me : Option (Name × Descent))

/-- The roles where a test held: a counter that a reading of the test shows short of its
bound is guarded. Of the tests that guard code (facts.guarding-tests), the model reads a
comparison alone, mirrored or as the first conjunct of an `&&` chain, in the branch where it
held, and the negation of a comparison in the branch where it failed (`Expr.negated`). -/
def Roles.held (R : Roles) (c : Expr) : Roles :=
  match me with
  | some (_, .shrinks _ grow b) =>
    match c.countings.find? (guardReading R grow b) with
    | some (v, _, _) => (v, .guarded) :: R
    | none => R
  | _ => R

/-- Whether code where `me` says may name `g` with no `div`: `lim` covers it, and, in a
function's body, `g` is ranked below that function, so that it isn't in its recursive
group (facts.div). -/
def Limited.names (g : Name) : Bool := lim.fn g && me.all fun (f, _) => decide (B g < B f)

/-- Whether `e` names the function whose body the code is. -/
def Expr.isSelf : Expr → Bool
  | .fnRef g _ _ => me.any (·.1 == g)
  | _ => false

/-- Whether a self-call's arguments go down as the function's self-calls do
(facts.descending-self-calls and facts.shrinking-recursion). -/
def descends (R : Roles) (args : List Arg) : Bool := me.any fun (_, d) => d.calls R args

mutual

/-- Whether `e`, whose variables have the roles `R`, holds no site of `div`: no loop but
`for` and a `while` that counts, and calls only of a named function or of a closure literal
where it is written. A performance is a site of `div`, as a call through a stored function
value, the handler's clause, is; a `with` and a `when` add nothing of their own
(handlers.implicit-effects-and-capabilities). Naming a function, to call it or as a value,
adds `div` unless `lim` covers it, a function limited by `without div` counting as one
without `div` wherever it is named (facts.without), and, in a function's body, unless it is
ranked below that function. A call of the function itself adds nothing when it goes down as
`me` says, descending or shrinking (facts.descending-self-calls and facts.shrinking-recursion);
a use of it as a value is a site. So a counting loop, and the self-calls of a function that
shrink, add no `div`, and a caller that names the function inherits none
(facts.what-proofs-change, whose half on `panic` is `Op.panicFreeOn`'s; the calculus has no
analysis, no release build and no package API). A `let` binding gives its name the role of
its value when its body doesn't write it, a `match` arm its binders the role of what they
hold (`Arm.role`), and a test the counter it shows short of its bound the role `guarded` in
its branch (`Roles.held`); every other binder has none, and in a closure literal's body, a
loop, a `catch` handler and a `when` block no variable has one. The sites are facts.div's,
and a few more: every call through a function value is one, as through a stored one
(facts.calls-through-function-values), a parameter not marked `escaping` and a bound in
generic code included, and so is every recursive call that goes down in no way the model
knows. -/
def Expr.divFree : Roles → Expr → Bool
  | _, .var _ | _, .move _ | _, .int _ | _, .bool _ | _, .unit | _, .break | _, .continue => true
  | _, .fnRef f _ _ => lim.names B me f
  | _, .method t m _ => lim.method t m
  | R, .record _ _ fields => fieldsDivFree R fields
  | R, .variant _ _ _ es => exprsDivFree R es
  | R, .list _ es => exprsDivFree R es
  | R, .op _ es | R, .view es => exprsDivFree R es
  | R, .field e _ => e.divFree R
  | R, .index e i => e.divFree R && i.divFree R
  | _, .closure _ _ _ body => body.divFree []
  | R, .call callee args _ =>
    callee.callable && (if callee.isSelf me then descends me R args else callee.divFree R) &&
      argsDivFree R args
  | R, .letIn x _ init body =>
    init.divFree R &&
      body.divFree ((x, if decide (x ∉ body.writes) then init.roleIn R else .other) :: R)
  | R, .varIn x _ init body => init.divFree R && body.divFree ((x, .other) :: R)
  | R, .assign ⟨_, path⟩ value => pathDivFree R path && value.divFree R
  | R, .seq a b => a.divFree R && b.divFree R
  | R, .if c _ a b =>
    c.divFree R && a.divFree (R.held me c) && b.divFree (R.held me c.negated)
  | R, .match e _ arms => e.divFree R && armsDivFree R (e.roleIn R) arms
  | R, .for _ _ e body => e.divFree R && body.divFree []
  | R, .raise e => e.divFree R
  | R, .try e | R, .form _ e => e.divFree R
  | R, .tryCatch e _ _ handler _ => e.divFree R && handler.divFree []
  | _, .while c body => c.divFree [] && body.divFree [] && Expr.countsIn c body
  | _, .loop _ => false
  | R, .return e => e.divFree R
  | _, .perform _ _ => false
  | R, .withH _ _ h b => h.divFree R && b.divFree R
  | R, .held _ hs body => exprsDivFree R hs && body.divFree []

def exprsDivFree : Roles → List Expr → Bool
  | _, [] => true
  | R, e :: es => e.divFree R && exprsDivFree R es

def fieldsDivFree : Roles → List (Name × Expr) → Bool
  | _, [] => true
  | R, (_, e) :: fields => e.divFree R && fieldsDivFree R fields

def argsDivFree : Roles → List Arg → Bool
  | _, [] => true
  | R, .value e :: args => e.divFree R && argsDivFree R args
  | R, .inout ⟨_, path⟩ :: args => pathDivFree R path && argsDivFree R args

def pathDivFree : Roles → List Projection → Bool
  | _, [] => true
  | R, .field _ :: path => pathDivFree R path
  | R, .index i :: path => i.divFree R && pathDivFree R path

/-- Whether each arm's body holds no site of `div`, its binders with the role `Arm.role`
gives them, of a scrutinee of role `r`. -/
def armsDivFree : Roles → Role → List Arm → Bool
  | _, _, [] => true
  | R, r, ⟨p, xs, body⟩ :: arms =>
    body.divFree (R.bindAll xs (Arm.role r ⟨p, xs, body⟩)) && armsDivFree R r arms

end

end

mutual

/-- The depth of `e`'s text: one more than its parts', a closure literal called where it is
written counting its body. Running code free of `div` goes by induction on it. -/
def Expr.depth : Expr → Nat
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _
  | .method _ _ _ | .closure _ _ _ _ => 1
  | .record _ _ fields => fieldsDepth fields + 1
  | .variant _ _ _ es => exprsDepth es + 1
  | .list _ es => exprsDepth es + 1
  | .op _ es | .view es => exprsDepth es + 1
  | .field e _ => e.depth + 1
  | .index e i => max e.depth i.depth + 1
  | .call callee args _ => max callee.depth (max (argsDepth args) callee.bodyDepth) + 1
  | .letIn _ _ init body => max init.depth body.depth + 1
  | .varIn _ _ init body => max init.depth body.depth + 1
  | .assign ⟨_, path⟩ value => max (pathDepth path) value.depth + 1
  | .seq a b => max a.depth b.depth + 1
  | .if c _ a b => max c.depth (max a.depth b.depth) + 1
  | .match e _ arms => max e.depth (armsDepth arms) + 1
  | .for _ _ e body => max e.depth body.depth + 1
  | .raise e => e.depth + 1
  | .try e | .form _ e => e.depth + 1
  | .tryCatch e _ _ handler _ => max e.depth handler.depth + 1
  | .while c body => max c.depth body.depth + 1
  | .loop body => body.depth + 1
  | .return e => e.depth + 1
  | .perform _ e => e.depth + 1
  | .withH _ _ h b => max h.depth b.depth + 1
  | .held _ hs body => max (exprsDepth hs) body.depth + 1

/-- The depth of the body that a call of `e` runs where it is written: a closure literal's. -/
def Expr.bodyDepth : Expr → Nat
  | .closure _ _ _ body => body.depth
  | _ => 0

def exprsDepth : List Expr → Nat
  | [] => 0
  | e :: es => max e.depth (exprsDepth es)

def fieldsDepth : List (Name × Expr) → Nat
  | [] => 0
  | (_, e) :: fields => max e.depth (fieldsDepth fields)

def argsDepth : List Arg → Nat
  | [] => 0
  | .value e :: args => max e.depth (argsDepth args)
  | .inout ⟨_, path⟩ :: args => max (pathDepth path) (argsDepth args)

def pathDepth : List Projection → Nat
  | [] => 0
  | .field _ :: path => pathDepth path
  | .index i :: path => max i.depth (pathDepth path)

def armsDepth : List Arm → Nat
  | [] => 0
  | ⟨_, _, body⟩ :: arms => max body.depth (armsDepth arms)

end

/-- The name of the parameter at position `k`, when it is a `let` parameter, the only
parameter of its name, that the body never writes. -/
def FnDecl.letParam? (d : FnDecl) (k : Nat) : Option Name :=
  match d.params[k]? with
  | some p =>
    if p.mode = .let ∧ (d.params.map Param.name).Nodup ∧ p.name ∉ d.body.writes then some p.name
    else none
  | none => none

/-- The roles a body starts with: its descending parameter holds the whole of itself
(facts.descending-self-calls), or its counter is a counter and the parameter its bound is a
limit (facts.shrinking-recursion), each when `FnDecl.letParam?` finds it; with no such
parameter, no variable has a role. -/
def FnDecl.entryRoles (d : FnDecl) : Descent → Roles
  | .parts k => match d.letParam? k with
    | some x => [(x, .whole)]
    | none => []
  | .shrinks k _ b => match d.letParam? k with
    | some x => (x, .counter) :: match b with
      | .param j => (match d.letParam? j with
        | some q => if q = x then [] else [(q, .limit)]
        | none => [])
      | .lit _ => []
    | none => []

/-- A ranking of the functions that `lim` covers, with the way `desc f` that each function's
self-calls go down: each body is free of `div`, naming only functions that `lim` covers and
ranks below it, and calling itself only on a strict part of its descending parameter
(facts.descending-self-calls) or with its counter stepped toward its bound
(facts.shrinking-recursion), all its self-calls the same way. So the functions of one
recursive group are one function, whose self-calls all descend or all shrink. -/
def Decls.Ranked (D : Decls) (lim : Limited) (B : Name → Nat) (desc : Name → Descent) : Prop :=
  ∀ name d, D.fn? name = some d → lim.fn name = true →
    d.body.divFree lim B (some (name, desc name)) (d.entryRoles (desc name)) = true

/-- Every function of the program and `main` hold no site of `div`, and the functions call
each other without recursion but self-calls that descend or shrink (facts.without-div). -/
def Program.DivFree (p : Program) : Prop :=
  ∃ B desc, p.decls.Ranked Limited.all B desc ∧ p.main.divFree Limited.all B none [] = true

/-- The rank of each function: its position among the declarations, so that each may name
those declared before it. -/
def Decls.rank (D : Decls) (f : Name) : Nat := D.fns.findIdx (·.name == f)

/-- The ways a function's self-calls may go down that `Decls.desc` tries: on strict parts of
each parameter, and with each parameter shrinking or growing toward `0` or toward another
parameter. -/
def FnDecl.descents (d : FnDecl) : List Descent :=
  (List.range d.params.length).flatMap fun k => .parts k :: [true, false].flatMap fun g =>
    .shrinks k g (.lit 0) :: (List.range d.params.length).map fun j => .shrinks k g (.param j)

/-- How a function's self-calls go down: the first of `FnDecl.descents` with which its body
passes the check. -/
def Decls.desc (D : Decls) (f : Name) : Descent :=
  match D.fn? f with
  | some d => (d.descents.find? fun k =>
      d.body.divFree Limited.all D.rank (some (f, k)) (d.entryRoles k)).getD (.parts 0)
  | none => .parts 0

/-- Whether every function's body is free of `div` under the ranking and the positions. -/
def Decls.rankedBy (D : Decls) (B : Name → Nat) (desc : Name → Descent) : Bool :=
  D.fns.all fun d => d.body.divFree Limited.all B (some (d.name, desc d.name)) (d.entryRoles (desc d.name))

/-- The check of `Program.DivFree` for a program whose functions call only those
declared before them, and themselves when the calls descend. -/
def Program.divFree (p : Program) : Bool :=
  p.decls.rankedBy p.decls.rank p.decls.desc && p.main.divFree Limited.all p.decls.rank none []

theorem Decls.ranked_of_rankedBy {D : Decls} {B : Name → Nat} {desc : Name → Descent}
    (h : D.rankedBy B desc = true) : D.Ranked Limited.all B desc := by
  intro name d hd _
  have hmem := List.mem_of_find?_eq_some hd
  have hname : d.name = name := by simpa using List.find?_some hd
  have := List.all_eq_true.1 h d hmem
  exact hname ▸ this

theorem Program.divFree_spec {p : Program} (h : p.divFree = true) : p.DivFree := by
  simp only [Program.divFree, Bool.and_eq_true] at h
  exact ⟨_, _, Decls.ranked_of_rankedBy h.1, h.2⟩

end Stilt
