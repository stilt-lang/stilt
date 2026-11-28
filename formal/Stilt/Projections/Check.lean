import Stilt.Projections
import Stilt.Projections.Exits
import Stilt.Panics.Writes

/-!
# The checks of projections

`Expr.once res k caught n e` follows the paths through code of a projection's body, whose kept
values are in `res` and whose access is `k`, from `n` `yield`s run, inside the operand of a
`catch` when `caught` (projections.once-on-every-path, projections.yield and
projections.cannot-raise). A `yield` is a statement: the paths are followed through the
statements of the body's blocks, the branches of an `if` and the arms of a `match` and of a
`catch`, one by one, and code that ends no path normally, a `return`, a `raise` or a panic,
ends its paths. Any other code runs no `yield` (`Expr.keeps`): one inside a loop, a guard, the
operand of a `catch`, a closure literal, an operand or an argument breaks the rule, as do a
second `yield` on a path and a path to the end or to a `return` that has run none. The check is
syntactic, as the Reference's is, and reads less than the Reference in two ways, each rejecting
more: a branch ends its paths only when it ends them by its form, not by its type `Never`
alone, as a call of a function whose result is `Never` does; and a `yield` inside an operand, an
argument, or the block of a `when` or a `with`, which the Reference follows, is rejected too.

`Expr.namesProjectionsOnlyByCall` is projections.not-a-value, and `Program.Projections` the
checks of a whole program.
-/

namespace Stilt

mutual

/-- Whether `e` raises an error of its own: a `raise`, or a call marked by a `try`, outside the
operand of a `catch` and every closure literal (projections.cannot-raise). -/
def Expr.raisesOwn : Expr → Bool
  | .raise _ | .try _ => true
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .closure .. => false
  | .tryCatch _ _ _ h _ => h.raisesOwn
  | .record _ _ fields => fieldsRaiseOwn fields
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => exprsRaiseOwn es
  | .field e _ | .form _ e | .return e | .loop e | .perform _ e => e.raisesOwn
  | .index a b | .seq a b | .while a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b
  | .for _ _ a b => a.raisesOwn || b.raisesOwn
  | .call callee args _ => callee.raisesOwn || argsRaiseOwn args
  | .assign ⟨_, path⟩ value => pathRaisesOwn path || value.raisesOwn
  | .if c _ a b => c.raisesOwn || a.raisesOwn || b.raisesOwn
  | .match e _ arms => e.raisesOwn || armsRaiseOwn arms
  | .held _ hs body => exprsRaiseOwn hs || body.raisesOwn

def exprsRaiseOwn : List Expr → Bool
  | [] => false
  | e :: es => e.raisesOwn || exprsRaiseOwn es

def fieldsRaiseOwn : List (Name × Expr) → Bool
  | [] => false
  | (_, e) :: fields => e.raisesOwn || fieldsRaiseOwn fields

def argsRaiseOwn : List Arg → Bool
  | [] => false
  | .value e :: args => e.raisesOwn || argsRaiseOwn args
  | .inout ⟨_, path⟩ :: args => pathRaisesOwn path || argsRaiseOwn args

def pathRaisesOwn : List Projection → Bool
  | [] => false
  | .field _ :: path => pathRaisesOwn path
  | .index i :: path => i.raisesOwn || pathRaisesOwn path

def armsRaiseOwn : List Arm → Bool
  | [] => false
  | ⟨_, _, guard, body⟩ :: arms => guardRaisesOwn guard || body.raisesOwn || armsRaiseOwn arms

def guardRaisesOwn : Option Expr → Bool
  | none => false
  | some g => g.raisesOwn

end

/-- Code of a projection's body, whose kept values are in `res` and whose access is `k`, that
runs no `yield` and that the paths pass through whole, from `n` `yield`s run: it holds no
`yield` (projections.yield), writes no `res`, uses no `k`, ends with no `break` or `continue` of
a loop around it, with a `return` only once a `yield` has run, and raises nothing of its own
outside the operand of a `catch`, `caught` (projections.cannot-raise). -/
def Expr.keeps (res k : Name) (caught : Bool) (n : Nat) (e : Expr) : Bool :=
  !e.yields && !e.writes.contains res && !e.free k && e.exits false (n == 1) &&
    (caught || !e.raisesOwn)

/-- Code that runs no `yield` and ends normally with `n`, or breaks a rule. -/
def Yields.kept (n : Nat) (ok : Bool) : Yields := if ok then some (some n) else none

/-- The indexes of a place run no `yield`. -/
def pathKeeps (res k : Name) (caught : Bool) (n : Nat) : List Projection → Bool
  | [] => true
  | .field _ :: path => pathKeeps res k caught n path
  | .index i :: path => i.keeps res k caught n && pathKeeps res k caught n path

/-- The arguments of a `yield`'s access: places, rooted in neither `res` nor `k`, whose indexes
run no `yield` (projections.yield), and variables, which a yielded view that writes its source
passes beside its source's place, its part's start and end (`Stilt.Writable`). -/
def yieldArgsOnce (res k : Name) (caught : Bool) (n : Nat) : List Arg → Bool
  | [] => true
  | .value (.var y) :: args => y != res && y != k && yieldArgsOnce res k caught n args
  | .value _ :: _ => false
  | .inout ⟨x, path⟩ :: args =>
    x != res && x != k && pathKeeps res k caught n path && yieldArgsOnce res k caught n args

/-- Whether `e` is the call of the access `k` with places. -/
def Expr.callsAccess (res k : Name) (caught : Bool) (n : Nat) : Expr → Bool
  | .call (.var z) args _ => z == k && yieldArgsOnce res k caught n args
  | _ => false

mutual

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
      ((init.callsAccess res k caught n && body.keeps res k caught n) ||
        (init.keeps res k caught n && body.accessOnce res k caught n))
  | _ => false

/-- The arguments of a projection's call that a `yield`'s operand is: they run no `yield`, and
the last, the inner projection's access, calls `k` once. -/
def projectAccessOnce (res k : Name) (caught : Bool) (n : Nat) : List Arg → Bool
  | [] => false
  | [.value (.closure _ _ _ body)] => body.accessOnce res k caught n
  | .value e :: args => e.keeps res k caught n && projectAccessOnce res k caught n args
  | .inout ⟨x, path⟩ :: args =>
    x != res && x != k && pathKeeps res k caught n path && projectAccessOnce res k caught n args

end

/-- Every expression runs no `yield`. -/
def exprsKeep (res k : Name) (caught : Bool) (n : Nat) : List Expr → Bool
  | [] => true
  | e :: es => e.keeps res k caught n && exprsKeep res k caught n es

/-- `yield p`'s operand, the call of the access: it calls `k` once, and writes no `res` and ends
with no jump. -/
def Expr.yieldOperand (res k : Name) (caught : Bool) (a : Expr) : Bool :=
  a.accessOnce res k caught 0 && !a.writes.contains res && a.exits false false && !a.yields

/-- Whether an operation is `panic(msg)` or `unreachable()`, which ends its paths. -/
def Op.isPanic : Op → Bool
  | .panic _ => true
  | _ => false

/-- Whether `e` is the value a projection's `return` gives, the first of those `res` keeps: the
body has type `()`, and a `return` in it takes no value (projections.yield). -/
def Expr.isYielded (res : Name) : Expr → Bool
  | .form .yielded (.index (.var x) (.int 0)) => x == res
  | _ => false

/-- The operand of `yield p`, the call of the access, when `e` is what the `yield` means: the
access's value added to `res`. The access, the caller's, takes the place `p`, rooted in a `var`
binding or an `inout` parameter of the body, and the places it threads, all `inout`, whose
indexes are evaluated when the statement runs (projections.yield). So the projection's call runs
its body to the `yield`, the access happens on the yielded place, and the body resumes after it
and runs to its end, when the call writes its `inout` arguments back
(projections.when-projection-runs). The access is a call in the body: one that raises leaves the
body as a raise leaves any call, the statements after the `yield` not run and no `catch` of the
body's seeing the error, and the projection's `inout` arguments are written back holding what
was written before the `yield` and through the place, as `Outcome.leaveCall` states. So does a
performance in the access whose handler ends it: the statements after the `yield` are in the
performance's rest, which the handler never resumes. The model doesn't state that a `without`
on the projection leaves the access's effects out of what it limits. -/
def Expr.yieldOperand? (res : Name) : Expr → Option Expr
  | .assign ⟨x, []⟩ (.op (.list .push) [.var y, .try a]) => if x == res && y == res then some a else none
  | _ => none

mutual

/-- The paths through `e`, in a projection's body that keeps the access's values in `res` and
whose access is `k`, from `n` `yield`s run (projections.once-on-every-path). The statements of
a block, the branches of an `if`, the arms of a `match` and the handler of a `catch` are
followed; any other code runs no `yield` (`Expr.keeps`). A binder of `res` or `k` breaks the
rules, as do a second `yield` on a path, a `return` on a path that has run none and, outside
the operand of a `catch`, `caught`, a `raise` (projections.cannot-raise). -/
def Expr.once (res k : Name) (caught : Bool) (n : Nat) : Expr → Yields
  | .seq a b => (a.once res k caught n).andThen fun m => b.once res k caught m
  | .letIn x _ init body | .varIn x _ init body =>
    if x != res && x != k then (init.once res k caught n).andThen fun m => body.once res k caught m
    else none
  | .if c _ a b =>
    if c.keeps res k caught n then (a.once res k caught n).join (b.once res k caught n) else none
  | .match e _ arms => if e.keeps res k caught n then armsOnce res k caught n arms else none
  | .tryCatch e _ x h _ =>
    if x != res && x != k && e.keeps res k true n then Yields.join (some (some n)) (h.once res k caught n)
    else none
  | .raise e => if caught && e.keeps res k caught n then some none else none
  | .try e => if caught then e.once res k caught n else none
  | .return e => if e.isYielded res && n == 1 then some none else none
  | .break | .continue => none
  | .op o es =>
    if o.isPanic then (if (Expr.op o es).keeps res k caught n then some none else none)
    else Yields.kept n ((Expr.op o es).keeps res k caught n)
  | .form f m =>
    match f with
    | .yield =>
      match m.yieldOperand? res with
      | some a => if n == 0 && a.yieldOperand res k caught then some (some 1) else none
      | none => none
    | .letElse | .orElse | .compound | .intFloat | .optionField | .update | .element
    | .spawn | .await | .scope | .scopeSpawn | .async | .lazyNew | .lazyGet
    | .parMap | .parEach | .parBoth | .parFold | .viewIndex | .iter _ | .traitConst _ =>
      m.once res k caught n
    | .project | .writes | .through => Yields.kept n ((Expr.form f m).keeps res k caught n)
    | .yielded | .projection => none
  | e => Yields.kept n (e.keeps res k caught n)

/-- The arms of a `match`, one of which runs: guards run no `yield`, since a guard may run more
than once (patterns.guards), and binders bind neither `res` nor `k`. With no arm left, no path
goes on. -/
def armsOnce (res k : Name) (caught : Bool) (n : Nat) : List Arm → Yields
  | [] => some none
  | ⟨_, binders, guard, body⟩ :: arms =>
    if !binders.contains res && !binders.contains k &&
        (match guard with | none => true | some g => g.keeps res k caught n) then
      (body.once res k caught n).join (armsOnce res k caught n arms)
    else none

end

/-- What a function's body is when it is a projection's: the name of the list of kept values,
their type and the body the projection was declared with. A projection, a declared function or
method whose result is written `inout T`, is a function of its own for each type of its
caller's access, whose last parameter takes the access, and whose body is this form; no closure
literal is one (projections.declaring-projection). -/
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
where a place is (projections.not-a-value, E0426): a projection isn't a value. A call where a
place is is the call with the projection's arguments, evaluated first, in their turn, and then
the access, a closure literal that takes the yielded place `inout` and does with it what the
caller does with the place the call is: assigns to it, passes it `inout`, or reads it, which
copies the yielded place's value out (projections.call-is-place). -/
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
