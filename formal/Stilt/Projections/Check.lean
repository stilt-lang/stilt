import Stilt.Projections

/-!
# The checks of projections

`Expr.once res k caught n e` follows the paths through code of a projection's body, whose kept
values are in `res` and whose access is `k`, from `n` `yield`s run, inside the operand of a
`catch` when `caught` (projections.once-on-every-path, projections.yield and
projections.cannot-raise). The paths through the branches of an `if` and the arms of a
`match` and of a `catch` are followed one by one, and code that ends no path normally, a
`return`, a `raise`, a `break`, a `continue` or a panic, ends its paths. The check is
syntactic, as the Reference's is. It reads less than the Reference in two ways, each
rejecting more: a branch ends its paths only when it ends them by its form, not by its type
`Never` alone, as a call of a function whose result is `Never` does; and a `yield` is a
statement of the body, its blocks and its branches, so one inside an operand, an argument or a
`when`'s or a `with`'s block is rejected too.

`Expr.namesProjectionsOnlyByCall` is projections.not-a-value, and `Program.Projections` the
checks of a whole program.
-/

namespace Stilt

/-- Code that runs no `yield` and ends normally with `n`, or breaks a rule. -/
def Yields.kept (n : Nat) (ok : Bool) : Yields := if ok then some (some n) else none

mutual

/-- The paths through `e`, in a projection's body that keeps the access's values in `res` and
whose access is `k`, from `n` `yield`s run (projections.once-on-every-path). Only a `yield`
names `res` or `k`; a binder of either name, a closure literal that uses either and a `yield`
inside a closure literal break the rules, as do a second `yield` on a path and a `return` on a
path that has run none. A `raise`, and a call marked by a `try`, are allowed only inside the
operand of a `catch`, `caught` (projections.cannot-raise). -/
def Expr.once (res k : Name) (caught : Bool) (n : Nat) : Expr → Yields
  | .var x | .move x => Yields.kept n (x != res && x != k)
  | .int _ | .bool _ | .unit | .fnRef .. | .method .. => some (some n)
  | .break | .continue => some none
  | .closure ps r ρ body =>
    Yields.kept n (!(Expr.closure ps r ρ body).free res && !(Expr.closure ps r ρ body).free k &&
      !body.yields)
  | .record _ _ fields => Yields.kept n (fieldsOnce res k caught n fields)
  | .variant _ _ _ es | .list _ es | .view es => Yields.kept n (exprsOnce res k caught n es)
  | .op (.panic _) es => if exprsOnce res k caught n es then some none else none
  | .op _ es => Yields.kept n (exprsOnce res k caught n es)
  | .field e _ | .perform _ e => Yields.kept n ((e.once res k caught n).keeps n)
  | .index a b => Yields.kept n ((a.once res k caught n).keeps n && (b.once res k caught n).keeps n)
  | .call callee args _ =>
    Yields.kept n ((callee.once res k caught n).keeps n && argsOnce res k caught n args)
  | .assign ⟨x, path⟩ value =>
    Yields.kept n (x != res && x != k && pathOnce res k caught n path &&
      (value.once res k caught n).keeps n)
  | .seq a b => (a.once res k caught n).andThen fun m => b.once res k caught m
  | .letIn x _ init body | .varIn x _ init body =>
    if x != res && x != k then (init.once res k caught n).andThen fun m => body.once res k caught m
    else none
  | .if c _ a b =>
    if (c.once res k caught n).keeps n then (a.once res k caught n).join (b.once res k caught n)
    else none
  | .match e _ arms => if (e.once res k caught n).keeps n then armsOnce res k caught n arms else none
  | .for x _ e body =>
    Yields.kept n (x != res && x != k && (e.once res k caught n).keeps n &&
      (body.once res k caught n).keeps n)
  | .while c body => Yields.kept n ((c.once res k caught n).keeps n && (body.once res k caught n).keeps n)
  | .loop body => Yields.kept n ((body.once res k caught n).keeps n)
  | .tryCatch e _ x h _ =>
    if x != res && x != k && (e.once res k true n).keeps n then
      (e.once res k true n).join (h.once res k caught n)
    else none
  | .raise e => if caught && (e.once res k caught n).keeps n then some none else none
  | .try e => if caught then e.once res k caught n else none
  | .return (.form .yielded (.index (.var x) (.int 0))) =>
    if x == res && n == 1 then some none else none
  | .return _ => none
  | .withH _ _ h b => Yields.kept n ((h.once res k caught n).keeps n && (b.once res k caught n).keeps n)
  | .held ns hs body =>
    Yields.kept n (!(ns.any fun p => p.1 == res || p.1 == k) && exprsOnce res k caught n hs &&
      (body.once res k caught n).keeps n)
  | .form .yield (.assign ⟨x, []⟩ (.op (.list .push) [.var y, .try a])) =>
    if x == res && y == res && n == 0 && a.accessOnce res k caught n then some (some 1) else none
  | .form .project e | .form .letElse e | .form .orElse e => e.once res k caught n
  | .form .yield _ | .form .yielded _ | .form .projection _ => none

/-- The call of a `yield`'s access, `k`, once: the call itself, or bindings of what the call
reads and of what it gives, as a place through a map's element is passed `inout`, and the
code after it, none of which runs a `yield`; or, when the operand of the `yield` is a
projection's call, that call, whose access calls `k` once (projections.yield,
projections.when-projection-runs and projections.nested). -/
def Expr.accessOnce (res k : Name) (caught : Bool) (n : Nat) : Expr → Bool
  | .call (.var z) args _ => z == k && yieldArgsOnce res k caught n args
  | .form .project (.call (.fnRef ..) args _) => projectAccessOnce res k caught n args
  | .letIn x _ init body =>
    x != res && x != k &&
      ((init.callsAccess res k caught n && (body.once res k caught n).keeps n) ||
        ((init.once res k caught n).keeps n && body.accessOnce res k caught n))
  | _ => false

/-- The arguments of a projection's call that a `yield`'s operand is: they run no `yield`, and
the last, the inner projection's access, calls `k` once. -/
def projectAccessOnce (res k : Name) (caught : Bool) (n : Nat) : List Arg → Bool
  | [] => false
  | [.value (.closure _ _ _ body)] => body.accessOnce res k caught n
  | .value e :: args => (e.once res k caught n).keeps n && projectAccessOnce res k caught n args
  | .inout ⟨x, path⟩ :: args =>
    x != res && x != k && pathOnce res k caught n path && projectAccessOnce res k caught n args

/-- Whether `e` is the call of the access `k` with places. -/
def Expr.callsAccess (res k : Name) (caught : Bool) (n : Nat) : Expr → Bool
  | .call (.var z) args _ => z == k && yieldArgsOnce res k caught n args
  | _ => false

/-- Every expression runs no `yield`. -/
def exprsOnce (res k : Name) (caught : Bool) (n : Nat) : List Expr → Bool
  | [] => true
  | e :: es => (e.once res k caught n).keeps n && exprsOnce res k caught n es

def fieldsOnce (res k : Name) (caught : Bool) (n : Nat) : List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fields => (e.once res k caught n).keeps n && fieldsOnce res k caught n fields

/-- Every argument runs no `yield`, and no `inout` argument is rooted in `res` or `k`. -/
def argsOnce (res k : Name) (caught : Bool) (n : Nat) : List Arg → Bool
  | [] => true
  | .value e :: args => (e.once res k caught n).keeps n && argsOnce res k caught n args
  | .inout ⟨x, path⟩ :: args =>
    x != res && x != k && pathOnce res k caught n path && argsOnce res k caught n args

/-- The arguments of a `yield`'s access: places, rooted in neither `res` nor `k`, whose indexes
run no `yield` (projections.yield). -/
def yieldArgsOnce (res k : Name) (caught : Bool) (n : Nat) : List Arg → Bool
  | [] => true
  | .value _ :: _ => false
  | .inout ⟨x, path⟩ :: args =>
    x != res && x != k && pathOnce res k caught n path && yieldArgsOnce res k caught n args

def pathOnce (res k : Name) (caught : Bool) (n : Nat) : List Projection → Bool
  | [] => true
  | .field _ :: path => pathOnce res k caught n path
  | .index i :: path => (i.once res k caught n).keeps n && pathOnce res k caught n path

/-- The arms of a `match`, one of which runs: guards run no `yield`, since a guard may run more
than once (patterns.guards), and binders bind neither `res` nor `k`. With no arm left, no path
goes on. -/
def armsOnce (res k : Name) (caught : Bool) (n : Nat) : List Arm → Yields
  | [] => some none
  | ⟨_, binders, guard, body⟩ :: arms =>
    if !binders.contains res && !binders.contains k && guardOnce res k caught n guard then
      (body.once res k caught n).join (armsOnce res k caught n arms)
    else none

def guardOnce (res k : Name) (caught : Bool) (n : Nat) : Option Expr → Bool
  | none => true
  | some g => (g.once res k caught n).keeps n

end

/-- What a function's body is when it is a projection's: the name of the list of kept values,
their type and the body the projection was declared with. -/
def Expr.projection? : Expr → Option (Name × Ty × Expr)
  | .form .projection (.varIn res (.list R) (.list _ []) (.seq b (.index (.var res') (.int 0)))) =>
    if res == res' then some (res, R, b) else none
  | _ => none

/-- Whether a function is a projection, written for one type of its access. -/
def FnDecl.isProjection (d : FnDecl) : Bool :=
  match d.body with
  | .form .projection _ => true
  | _ => false

/-- A projection's function passes the checks of projections: its body is a projection's, its
last parameter, the access, a `let` parameter of a function type, and every path through the
body it was declared with runs exactly one `yield` from its start to its end or to a `return`,
at most one to a raise or a panic (projections.once-on-every-path). -/
def FnDecl.projectionChecked (d : FnDecl) : Bool :=
  match d.body.projection?, d.params.getLast? with
  | some (res, _, b), some ⟨.let, k, .fn .., none⟩ =>
    res != k && (b.once res k false 0 == some (some 1) || b.once res k false 0 == some none)
  | _, _ => false

mutual

/-- Whether `e` names a projection, one that `isProjection` holds, only as the callee of a call
where a place is (projections.not-a-value, E0426): a projection isn't a value. -/
def Expr.namesProjectionsOnlyByCall (isProjection : Name → Bool) : Expr → Bool
  | .fnRef f _ _ => !isProjection f
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .method .. => true
  | .form .project (.call (.fnRef f _ _) args _) =>
    isProjection f && argsNameProjectionsOnlyByCall isProjection args
  | .form .project _ => false
  | .form _ e | .field e _ | .raise e | .try e | .return e | .loop e | .perform _ e =>
    e.namesProjectionsOnlyByCall isProjection
  | .record _ _ fields => fieldsNameProjectionsOnlyByCall isProjection fields
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => exprsNameProjectionsOnlyByCall isProjection es
  | .index a b | .seq a b | .while a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b
  | .for _ _ a b | .tryCatch a _ _ b _ =>
    a.namesProjectionsOnlyByCall isProjection && b.namesProjectionsOnlyByCall isProjection
  | .closure _ _ _ body => body.namesProjectionsOnlyByCall isProjection
  | .call callee args _ =>
    callee.namesProjectionsOnlyByCall isProjection && argsNameProjectionsOnlyByCall isProjection args
  | .assign ⟨_, path⟩ value =>
    pathNamesProjectionsOnlyByCall isProjection path && value.namesProjectionsOnlyByCall isProjection
  | .if c _ a b =>
    c.namesProjectionsOnlyByCall isProjection && a.namesProjectionsOnlyByCall isProjection &&
      b.namesProjectionsOnlyByCall isProjection
  | .match e _ arms =>
    e.namesProjectionsOnlyByCall isProjection && armsNameProjectionsOnlyByCall isProjection arms
  | .held _ hs body =>
    exprsNameProjectionsOnlyByCall isProjection hs && body.namesProjectionsOnlyByCall isProjection

def exprsNameProjectionsOnlyByCall (isProjection : Name → Bool) : List Expr → Bool
  | [] => true
  | e :: es => e.namesProjectionsOnlyByCall isProjection && exprsNameProjectionsOnlyByCall isProjection es

def fieldsNameProjectionsOnlyByCall (isProjection : Name → Bool) : List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fields =>
    e.namesProjectionsOnlyByCall isProjection && fieldsNameProjectionsOnlyByCall isProjection fields

def argsNameProjectionsOnlyByCall (isProjection : Name → Bool) : List Arg → Bool
  | [] => true
  | .value e :: args =>
    e.namesProjectionsOnlyByCall isProjection && argsNameProjectionsOnlyByCall isProjection args
  | .inout ⟨_, path⟩ :: args =>
    pathNamesProjectionsOnlyByCall isProjection path && argsNameProjectionsOnlyByCall isProjection args

def pathNamesProjectionsOnlyByCall (isProjection : Name → Bool) : List Projection → Bool
  | [] => true
  | .field _ :: path => pathNamesProjectionsOnlyByCall isProjection path
  | .index i :: path =>
    i.namesProjectionsOnlyByCall isProjection && pathNamesProjectionsOnlyByCall isProjection path

def armsNameProjectionsOnlyByCall (isProjection : Name → Bool) : List Arm → Bool
  | [] => true
  | ⟨_, _, guard, body⟩ :: arms =>
    guardNamesProjectionsOnlyByCall isProjection guard && body.namesProjectionsOnlyByCall isProjection &&
      armsNameProjectionsOnlyByCall isProjection arms

def guardNamesProjectionsOnlyByCall (isProjection : Name → Bool) : Option Expr → Bool
  | none => true
  | some g => g.namesProjectionsOnlyByCall isProjection

end

/-- Whether a function of the declarations is a projection. -/
def Decls.isProjection (D : Decls) (f : Name) : Bool := (D.fn? f).any FnDecl.isProjection

/-- The checks of projections on a program: each projection's function passes them, every
other body and `main` hold no `yield` (projections.yield, E0425), and projections are named only
as the callees of calls where a place is (projections.not-a-value, E0426). -/
def Program.projectionsChecked (p : Program) : Bool :=
  p.decls.fns.all (fun d =>
      (if d.isProjection then d.projectionChecked else !d.body.yields) &&
        d.body.namesProjectionsOnlyByCall p.decls.isProjection) &&
    !p.main.yields && p.main.namesProjectionsOnlyByCall p.decls.isProjection

/-- A program passes the checks of projections (projections.declaring-projection,
projections.yield, projections.once-on-every-path, projections.cannot-raise and
projections.not-a-value). -/
def Program.Projections (p : Program) : Prop := p.projectionsChecked = true

end Stilt
