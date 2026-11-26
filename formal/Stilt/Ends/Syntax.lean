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
in one recursive group, and calls its own function only when the call descends
(facts.descending-self-calls): its argument at the position of the function's descending
parameter holds a strict part of that parameter, as the roles of the body's variables say
(`Stilt.Ends.Roles`).

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

section

-- Where code is: in the body of the function `f`, whose descending parameter is at
-- position `k`, when `me = some (f, k)`, and in `main`'s when `me = none`.
variable (lim : Limited) (B : Name → Nat) (me : Option (Name × Nat))

/-- Whether code where `me` says may name `g` with no `div`: `lim` covers it, and, in a
function's body, `g` is ranked below that function, so that it isn't in its recursive
group (facts.div). -/
def Limited.names (g : Name) : Bool := lim.fn g && me.all fun (f, _) => decide (B g < B f)

/-- Whether `e` names the function whose body the code is. -/
def Expr.isSelf : Expr → Bool
  | .fnRef g _ _ => me.any (·.1 == g)
  | _ => false

/-- Whether a self-call's arguments descend: the one at the descending position holds a
strict part of the descending parameter (facts.descending-self-calls). -/
def descends (R : Roles) (args : List Arg) : Bool := me.any fun (_, k) => argPart R k args

mutual

/-- Whether `e`, whose variables have the roles `R`, holds no site of `div`: no loop but
`for` and a `while` that counts, and calls only of a named function or of a closure literal
where it is written. A performance is a site of `div`, as a call through a stored function
value, the handler's clause, is; a `with` and a `when` add nothing of their own
(handlers.implicit-effects-and-capabilities). Naming a function, to call it or as a value,
adds `div` unless `lim` covers it, a function limited by `without div` counting as one
without `div` wherever it is named (facts.without), and, in a function's body, unless it is
ranked below that function. A call of the function itself adds nothing when it descends
(facts.descending-self-calls); a use of it as a value is a site. A `let` binding gives its
name the role of its value when its body doesn't write it, and a `match` arm its binders
the role of what they hold (`Arm.role`); every other binder has none, and in a closure
literal's body, a loop, a `catch` handler and a `when` block no variable has one. The
sites are facts.div's, and a few more: every call through a function value is one, as
through a stored one (facts.calls-through-function-values), a parameter not marked
`escaping` included, and so is every recursive call that doesn't descend. -/
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
  | R, .if c _ a b => c.divFree R && a.divFree R && b.divFree R
  | R, .match e _ arms => e.divFree R && armsDivFree R (e.roleIn R) arms
  | R, .for _ _ e body => e.divFree R && body.divFree []
  | R, .raise e => e.divFree R
  | R, .try e => e.divFree R
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
  | .try e => e.depth + 1
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

/-- The roles a body starts with: its parameter at position `k` holds the whole descending
parameter when it is a `let` parameter, the only parameter of its name, that the body never
writes (facts.descending-self-calls); with no such parameter, no variable has a role. -/
def FnDecl.entryRoles (d : FnDecl) (k : Nat) : Roles :=
  match d.params[k]? with
  | some p =>
    if p.mode = .let ∧ (d.params.map Param.name).Nodup ∧ p.name ∉ d.body.writes then
      [(p.name, .whole)]
    else []
  | none => []

/-- A ranking of the functions that `lim` covers, with the position `desc f` of each
function's descending parameter: each body is free of `div`, naming only functions that
`lim` covers and ranks below it, and calling itself only on a strict part of its descending
parameter (facts.descending-self-calls). So the functions of one recursive group are one
function, whose self-calls descend. -/
def Decls.Ranked (D : Decls) (lim : Limited) (B : Name → Nat) (desc : Name → Nat) : Prop :=
  ∀ name d, D.fn? name = some d → lim.fn name = true →
    d.body.divFree lim B (some (name, desc name)) (d.entryRoles (desc name)) = true

/-- Every function of the program and `main` hold no site of `div`, and the
functions call each other without recursion but self-calls that descend (facts.without-div). -/
def Program.DivFree (p : Program) : Prop :=
  ∃ B desc, p.decls.Ranked Limited.all B desc ∧ p.main.divFree Limited.all B none [] = true

/-- The rank of each function: its position among the declarations, so that each may name
those declared before it. -/
def Decls.rank (D : Decls) (f : Name) : Nat := D.fns.findIdx (·.name == f)

/-- The position of a function's descending parameter: the first at which its body passes
the check, `0` when none does. -/
def Decls.desc (D : Decls) (f : Name) : Nat :=
  match D.fn? f with
  | some d => ((List.range d.params.length).find? fun k =>
      d.body.divFree Limited.all D.rank (some (f, k)) (d.entryRoles k)).getD 0
  | none => 0

/-- Whether every function's body is free of `div` under the ranking and the positions. -/
def Decls.rankedBy (D : Decls) (B : Name → Nat) (desc : Name → Nat) : Bool :=
  D.fns.all fun d => d.body.divFree Limited.all B (some (d.name, desc d.name)) (d.entryRoles (desc d.name))

/-- The check of `Program.DivFree` for a program whose functions call only those
declared before them, and themselves when the calls descend. -/
def Program.divFree (p : Program) : Bool :=
  p.decls.rankedBy p.decls.rank p.decls.desc && p.main.divFree Limited.all p.decls.rank none []

theorem Decls.ranked_of_rankedBy {D : Decls} {B : Name → Nat} {desc : Name → Nat}
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
