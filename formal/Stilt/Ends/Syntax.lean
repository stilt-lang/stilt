import Stilt.Ends.Counting

/-!
# Code without `div`

Whether code holds no site of `div` (facts.div): no `loop`, no `while` but one
that counts (facts.counting-loops, `Stilt.Ends.Counting`), and
every call made of a function that the program names, `f(…)`, or of a closure
literal where it is written, `(|x| …)(…)`, never of a function value that
anything else gives, and no performance, which calls the handler's clause
(handlers.implicit-effects-and-capabilities); a `with` adds nothing, and neither does a
`when` (shared.when-on-value-already-held). A program has no recursion when its functions have a
**ranking**: a bound on the fuel each body needs, which is at least what the
calls it makes need, so that no function calls itself, directly or through
others (`Decls.Ranked`). Such code needs, to end, no more fuel than its text
bounds (`Expr.needs`) and the turns of its counting loops: a `for` loop runs
its body at the fuel of the loop, so the number of turns, which the list gives,
costs nothing, and a `while` takes one more for each turn.
-/

namespace Stilt

/-- Whether a call of `e` adds no `div`: `e` names a function, or is a closure
literal, which the call runs where it is written (facts.div). -/
def Expr.callable : Expr → Bool
  | .fnRef _ _ _ | .closure _ _ _ _ => true
  | _ => false

section

variable (lim : Limited)

mutual

/-- Whether `e` holds no site of `div`: no loop but `for` and a `while` that counts,
and calls only of a named function or of a closure literal where it is written. A
performance is a site of `div`, as a call through a stored function value, the
handler's clause, is; a `with` and a `when` add nothing of their own
(handlers.implicit-effects-and-capabilities). Naming a function, to call it or as a
value, adds `div` unless `lim` covers it: a function limited by `without div` counts as
one without `div` wherever it is named (facts.without). -/
def Expr.divFree : Expr → Bool
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue => true
  | .fnRef f _ _ => lim.fn f
  | .method t m _ => lim.method t m
  | .record _ fields => fieldsDivFree fields
  | .variant _ _ es => exprsDivFree es
  | .list _ es => exprsDivFree es
  | .op _ es | .view es => exprsDivFree es
  | .field e _ => e.divFree
  | .index e i => e.divFree && i.divFree
  | .closure _ _ _ body => body.divFree
  | .call callee args _ => callee.callable && callee.divFree && argsDivFree args
  | .letIn _ _ init body => init.divFree && body.divFree
  | .varIn _ _ init body => init.divFree && body.divFree
  | .assign ⟨_, path⟩ value => pathDivFree path && value.divFree
  | .seq a b => a.divFree && b.divFree
  | .if c _ a b => c.divFree && a.divFree && b.divFree
  | .match e _ arms => e.divFree && armsDivFree arms
  | .for _ _ e body => e.divFree && body.divFree
  | .raise e => e.divFree
  | .try e => e.divFree
  | .tryCatch e _ _ handler _ => e.divFree && handler.divFree
  | .while c body => c.divFree && body.divFree && Expr.countsIn c body
  | .loop _ => false
  | .return e => e.divFree
  | .perform _ _ => false
  | .withH _ _ h b => h.divFree && b.divFree
  | .held _ hs body => exprsDivFree hs && body.divFree

def exprsDivFree : List Expr → Bool
  | [] => true
  | e :: es => e.divFree && exprsDivFree es

def fieldsDivFree : List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fields => e.divFree && fieldsDivFree fields

def argsDivFree : List Arg → Bool
  | [] => true
  | .value e :: args => e.divFree && argsDivFree args
  | .inout ⟨_, path⟩ :: args => pathDivFree path && argsDivFree args

def pathDivFree : List Projection → Bool
  | [] => true
  | .field _ :: path => pathDivFree path
  | .index i :: path => i.divFree && pathDivFree path

def armsDivFree : List Arm → Bool
  | [] => true
  | ⟨_, _, body⟩ :: arms => body.divFree && armsDivFree arms

end

end

section

variable (B : Name → Nat)

mutual

/-- The fuel that `e` needs to end, when each function `f` that it calls needs
`B f` for its body: one step more than its parts, and than the body of what it
calls. -/
def Expr.needs : Expr → Nat
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _
  | .method _ _ _ | .closure _ _ _ _ => 1
  | .record _ fields => fieldsNeeds fields + 1
  | .variant _ _ es => exprsNeeds es + 1
  | .list _ es => exprsNeeds es + 1
  | .op _ es | .view es => exprsNeeds es + 1
  | .field e _ => e.needs + 1
  | .index e i => max e.needs i.needs + 1
  | .call callee args _ => max callee.needs (max (argsNeeds args) callee.bodyNeeds) + 1
  | .letIn _ _ init body => max init.needs body.needs + 1
  | .varIn _ _ init body => max init.needs body.needs + 1
  | .assign ⟨_, path⟩ value => max (pathNeeds path) value.needs + 1
  | .seq a b => max a.needs b.needs + 1
  | .if c _ a b => max c.needs (max a.needs b.needs) + 1
  | .match e _ arms => max e.needs (armsNeeds arms) + 1
  | .for _ _ e body => max e.needs body.needs + 1
  | .raise e => e.needs + 1
  | .try e => e.needs + 1
  | .tryCatch e _ _ handler _ => max e.needs handler.needs + 1
  | .while c body => max c.needs body.needs + 1
  | .loop body => body.needs + 1
  | .return e => e.needs + 1
  | .perform _ e => e.needs + 1
  | .withH _ _ h b => max h.needs b.needs + 1
  | .held _ hs body => max (exprsNeeds hs) body.needs + 1

/-- The fuel that the body a call of `e` runs needs: the function's bound, or the
closure literal's body's. -/
def Expr.bodyNeeds : Expr → Nat
  | .fnRef f _ _ => B f
  | .closure _ _ _ body => body.needs
  | _ => 0

def exprsNeeds : List Expr → Nat
  | [] => 0
  | e :: es => max e.needs (exprsNeeds es)

def fieldsNeeds : List (Name × Expr) → Nat
  | [] => 0
  | (_, e) :: fields => max e.needs (fieldsNeeds fields)

def argsNeeds : List Arg → Nat
  | [] => 0
  | .value e :: args => max e.needs (argsNeeds args)
  | .inout ⟨_, path⟩ :: args => max (pathNeeds path) (argsNeeds args)

def pathNeeds : List Projection → Nat
  | [] => 0
  | .field _ :: path => pathNeeds path
  | .index i :: path => max i.needs (pathNeeds path)

def armsNeeds : List Arm → Nat
  | [] => 0
  | ⟨_, _, body⟩ :: arms => max body.needs (armsNeeds arms)

end

end

/-- A ranking of the functions that `lim` covers: each body is free of `div`, naming
only functions that `lim` covers, and needs no more fuel than its function's bound, the
bounds of what it calls included. A function that calls itself, directly or through
others, has none: its body would need more than its own bound. -/
def Decls.Ranked (D : Decls) (lim : Limited) (B : Name → Nat) : Prop :=
  ∀ name d, D.fn? name = some d → lim.fn name = true → d.body.divFree lim = true ∧ d.body.needs B ≤ B name

/-- Every function of the program and `main` hold no site of `div`, and the
functions call each other without recursion (facts.without-div). -/
def Program.DivFree (p : Program) : Prop :=
  ∃ B, p.decls.Ranked Limited.all B ∧ p.main.divFree Limited.all = true

/-- The bounds of functions that call only those declared before them: each
function's, in order, the fuel its body needs with the bounds before it. -/
def Decls.rank (D : Decls) : Name → Nat :=
  D.fns.foldl (fun B d => fun f => if f = d.name then d.body.needs B else B f) fun _ => 0

/-- Whether every function's body is free of `div` and within its bound. -/
def Decls.rankedBy (D : Decls) (B : Name → Nat) : Bool :=
  D.fns.all fun d => d.body.divFree Limited.all && decide (d.body.needs B ≤ B d.name)

/-- The check of `Program.DivFree` for a program whose functions call only those
declared before them. -/
def Program.divFree (p : Program) : Bool := p.decls.rankedBy p.decls.rank && p.main.divFree Limited.all

theorem Decls.ranked_of_rankedBy {D : Decls} {B : Name → Nat} (h : D.rankedBy B = true) :
    D.Ranked Limited.all B := by
  intro name d hd _
  have hmem := List.mem_of_find?_eq_some hd
  have hname : d.name = name := by simpa using List.find?_some hd
  have := List.all_eq_true.1 h d hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1, hname ▸ this.2⟩

theorem Program.divFree_spec {p : Program} (h : p.divFree = true) : p.DivFree := by
  simp only [Program.divFree, Bool.and_eq_true] at h
  exact ⟨_, Decls.ranked_of_rankedBy h.1, h.2⟩

end Stilt
