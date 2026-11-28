import Stilt.Free
import Stilt.Generics.Commute
import Stilt.Handling
import Stilt.Holding
import Stilt.Matching
import Stilt.Memory
import Stilt.Ops
import Stilt.Scope

/-!
# Semantics

A big-step semantics with fuel, written as an evaluator. Evaluation is a
function, so it is deterministic by construction, and fuel makes it total: an
evaluation that needs more steps than its fuel allows ends with `outOfFuel`.

The evaluator is generic in a model of memory, `Memory`, which says how
variables are read, written and bound, and how a call passes its arguments. A
program runs in either model of `Stilt.Memory`: `Copy`, the reference interpreter's, or
`InPlace`.
-/

namespace Stilt

/-- Pairs each parameter with its argument, if their number and their modes
agree: an `inout` parameter takes a place, and a `let` parameter a value. -/
def bindArgs : List Param → List Passed → Option (List (Name × Passed))
  | [], [] => some []
  | p :: ps, a :: args =>
    match p.mode, a with
    | .inout, .place _ _ | .let, .value _ | .let, .moved _ _ =>
      (bindArgs ps args).map ((p.name, a) :: ·)
    | _, _ => none
  | _, _ => none

namespace Eval

variable {σ : Type}

/-- A callee's outcome as its call's, from the caller's state `s`: a value, a
raise, a `return` and a panic leave the call, writing its `inout` arguments
back (values.inout-arguments). A performance leaves it as a raise does, for a
handler that ends the `with` (handlers.call-that-handler-ends), and its rest,
once resumed, leaves it when it ends. A projection's call is a call whose body calls the access
at its `yield` (`Expr.yieldOperand?`), so an access that raises leaves the projection's body as
any raise leaves a call, its `inout` arguments written back holding what was written before
the `yield` and through the place (projections.raising-during-access), and an access whose
performance a handler ends leaves each call the same way, the place holding what the access
wrote before the performance (handlers.ended-projections). -/
def _root_.Stilt.Outcome.leaveCall (M : Memory σ) (bound : List (Name × Passed)) (s : σ) :
    Outcome σ Value → Outcome σ Value
  | .done v s' =>
    match M.leave s s' bound with
    | .ok s'' => .done v s''
    | .error f => .fault f (M.setWorld s (M.world s'))
  | .raised e s' =>
    match M.leave s s' bound with
    | .ok s'' => .raised e s''
    | .error f => .fault f (M.setWorld s (M.world s'))
  | .jumped (.ret v) s' =>
    match M.leave s s' bound with
    | .ok s'' => .done v s''
    | .error f => .fault f (M.setWorld s (M.world s'))
  | .jumped _ _ => .stuck
  | .panicked k s' =>
    match M.leave s s' bound with
    | .ok s'' => .panicked k s''
    | .error f => .fault f (M.setWorld s (M.world s'))
  | .performed op v s' k =>
    match M.leave s s' bound with
    | .ok s'' => .performed op v s'' fun w x => (k w x).leaveCall M bound s
    | .error f => .fault f (M.setWorld s (M.world s'))
  | .outOfFuel => .outOfFuel
  | .stuck => .stuck

/-- Runs a function's body as a call (values.inout-arguments and values.inout-argument-order). The call starts
once every argument is evaluated, then the body runs, and the call ends the
same way whether the body returns, raises or panics. A `return` in the body ends the
call with its value (expressions.closure-boundaries); a `break` or a `continue`
can't cross the body's boundary (E0216), so one that reaches it is stuck. -/
def invoke (M : Memory σ) (captured : List (Name × Value)) (params : List Param)
    (args : List Passed) (body : Eval σ Value) : Eval σ Value := fun s =>
  match bindArgs params args with
  | none => .stuck
  | some bound =>
    match M.enter s captured bound with
    | .error f => .fault f s
    | .ok callee => (body callee).leaveCall M bound s

/-- Calls a function value. `run` evaluates a body. A function declared at the
top level runs its body with its type parameters and row variables
instantiated. -/
def call (D : Decls) (M : Memory σ) (run : Expr → Eval σ Value) (f : Value)
    (args : List Passed) : Eval σ Value :=
  match f with
  | .closure captured params _ _ body => invoke M captured params args (run body)
  | .function name types rows =>
    match D.fn? name with
    | some d =>
      invoke M [] d.params args
        (run ((d.body.substTys (d.typeArgs types)).substRows (d.rowParams.zip rows)))
    | none => fail .stuck
  | _ => fail .stuck

/-- Whether a function value is the clause of a handler that takes control: its
row holds `resume` (handlers.resuming). -/
def _root_.Stilt.Value.takesControl (D : Decls) : Value → Bool
  | .closure _ _ _ ρ _ => ρ.resume.isSome
  | .function f _ _ => (D.fn? f).any fun d => d.row.resume.isSome
  | _ => false

/-- Calls a function value where `control` says whether it may be the clause of a
handler that takes control: only a `with` of such a handler calls one, since no
code but an operation's body names `resume` and no closure holds one
(handlers.resume-outside-operation and handlers.resume-at-most-once), so any
other call of one is stuck. -/
def callAs (D : Decls) (M : Memory σ) (run : Expr → Eval σ Value) (control : Bool) (f : Value)
    (args : List Passed) : Eval σ Value :=
  if !control && f.takesControl D then fail .stuck else call D M run f args

/-- `Trait.m` at a type: the function `m` of the impl of the trait for the
type's head, the one impl it has (traits.qualified-calls and traits.coherence), at the type's
arguments, which the impl's parameters take. -/
def method (D : Decls) (trait m : Name) (τ : Ty) : Eval σ Value :=
  match τ.head? with
  | some h =>
    match D.traitImpl? trait h with
    | some _ => pure (.function (implName trait h m) τ.args [])
    | none => fail .stuck
  | none => fail .stuck

/-- The impls of declarations whose functions are changed are where they were. -/
theorem _root_.Stilt.Decls.traitImpl?_mapFns (f : FnDecl → FnDecl) (D : Decls) (trait : Name)
    (h : Head) : (D.mapFns f).traitImpl? trait h =
      (D.traitImpl? trait h).map fun i => { i with fns := i.fns.map f } := by
  simp [Decls.traitImpl?, Decls.mapFns, List.find?_map, Function.comp_def]

/-- `Trait.m` finds the same function once the functions are changed. -/
theorem method_mapFns (f : FnDecl → FnDecl) (D : Decls) (trait m : Name) (τ : Ty) :
    (method (D.mapFns f) trait m τ : Eval σ Value) = method D trait m τ := by
  unfold method
  cases τ.head? with
  | none => rfl
  | some h =>
    dsimp only
    rw [Decls.traitImpl?_mapFns]
    cases D.traitImpl? trait h <;> rfl

/-- The integer a value is: an index (std.lists). -/
def asInt : Value → Eval σ Int
  | .int k => pure k
  | _ => fail .stuck

/-- The Boolean a value is: a condition (expressions.conditions). -/
def asBool : Value → Eval σ Bool
  | .bool b => pure b
  | _ => fail .stuck

/-- The elements of a list: the iterable of a `for` (expressions.for-iterables). -/
def asList : Value → Eval σ (List Value)
  | .list vs => pure vs
  | _ => fail .stuck

/-- A record of type `R` built from fields given in any order, which it keeps
in the order they are declared (values.left-to-right). -/
def declare (D : Decls) (R : Name) (written : List (Name × Value)) : Eval σ Value :=
  match D.record? R with
  | some r =>
    match r.fields.mapM (fun (f, _) => (written.lookup f).map (f, ·)) with
    | some fields => pure (.record R fields)
    | none => fail .stuck
  | none => fail .stuck

/-- Evaluates expressions from left to right (values.left-to-right). -/
def list (run : Expr → Eval σ Value) : List Expr → Eval σ (List Value)
  | [] => pure []
  | e :: es => do
    let v ← run e
    let vs ← list run es
    pure (v :: vs)

/-- Evaluates the fields of a record literal in the order they are written
(values.left-to-right). -/
def fields (run : Expr → Eval σ Value) : List (Name × Expr) → Eval σ (List (Name × Value))
  | [] => pure []
  | (f, e) :: rest => do
    let v ← run e
    let vs ← fields run rest
    pure ((f, v) :: vs)

/-- Evaluates the indexes of a place, from left to right. -/
def path (run : Expr → Eval σ Value) : List Projection → Eval σ Path
  | [] => pure []
  | .field f :: rest => do
    let p ← path run rest
    pure (.field f :: p)
  | .index i :: rest => do
    let k ← run i >>= asInt
    let p ← path run rest
    pure (.index k :: p)

/-- What a value argument passes: its value, and the variable it reads at its
last use, if it is one (values.passing-values). -/
def _root_.Stilt.Passed.ofArg : Expr → Value → Passed
  | .move x, v => .moved x v
  | _, v => .value v

/-- Evaluates the arguments of a call from left to right, a method call's
receiver first (modes.durations). An `inout` argument's indexes are evaluated
in its turn (values.left-to-right and values.index-reads). -/
def args (run : Expr → Eval σ Value) : List Arg → Eval σ (List Passed)
  | [] => pure []
  | .value e :: rest => do
    let v ← run e
    let vs ← args run rest
    pure (Passed.ofArg e v :: vs)
  | .inout ⟨x, projections⟩ :: rest => do
    let p ← path run projections
    let vs ← args run rest
    pure (.place x p :: vs)

/-- Runs an arm's guard `g` with the parts `us` of one way bound to the names `bs`, then its
body if the guard is true, or `next` if it is false (patterns.guards). -/
def tryWay (M : Memory σ) (run : Expr → Eval σ Value) (bs : List Name) (g body : Expr)
    (us : List Value) (next : Eval σ Value) : Eval σ Value := do
  if ← withVars M (bs.zip us) (run g >>= asBool) then withVars M (bs.zip us) (run body) else next

/-- Runs an arm's guard `g` with each way in turn that its pattern matches, the parts the
way binds bound to the names `bs`, and its body with the first way the guard is true, or
`next` when the guard is true with none (patterns.guards). The names are bound again for
the body, to the same parts: they are immutable (patterns.var-bindings), so the guard has
left them as they were. -/
def guarded (M : Memory σ) (run : Expr → Eval σ Value) (bs : List Name) (g body : Expr)
    (next : Eval σ Value) : List (List Value) → Eval σ Value
  | [] => next
  | us :: ways =>
    if bs.length = us.length then tryWay M run bs g body us (guarded M run bs g body next ways)
    else fail .stuck

/-- Runs the first arm of a `match` whose pattern matches the value and whose guard, if it
has one, is true, with the parts its pattern binds bound to its names (expressions.match and
patterns.match; patterns.bindings-are-copies). -/
def select (M : Memory σ) (run : Expr → Eval σ Value) : List Arm → Value → Eval σ Value
  | [], _ => fail .stuck
  | arm :: arms, v =>
    match arm.guard with
    | none =>
      match arm.pattern.matchOn v with
      | some us =>
        if arm.binders.length = us.length then withVars M (arm.binders.zip us) (run arm.body)
        else fail .stuck
      | none => select M run arms v
    | some g => guarded M run arm.binders g arm.body (select M run arms v) (arm.pattern.ways v)

/-- Assigns the value of an expression to the place that `x` and its
projections name. -/
def assign (M : Memory σ) (run : Expr → Eval σ Value) (x : Name)
    (projections : List Projection) (value : Expr) : Eval σ Value := do
  -- The indexes, then the value, then the store (values.assignment-order).
  let p ← path run projections
  let v ← run value
  update fun s => M.write s x p v
  pure .unit

/-- Reads and writes the world: a value and the world `f` gives from the state's world, or a
fault (std.io). -/
def world (M : Memory σ) (f : World → Except Fault (Value × World)) : Eval σ Value := fun s =>
  match M.inWorld s f with
  | .ok (a, s') => .done a s'
  | .error e => .fault e s

theorem world_ok {τ : Type} {F : Frames τ} {f : World → Except Fault (Value × World)} {fr : τ}
    {w x : World} {v : Value} (h : f w = .ok (v, x)) :
    Eval.world F.withWorld f (fr, w) = .done v (fr, x) := by
  simp [Eval.world, Frames.withWorld, h]

theorem world_error {τ : Type} {F : Frames τ} {f : World → Except Fault (Value × World)} {fr : τ}
    {w : World} {e : Fault} (h : f w = .error e) :
    Eval.world F.withWorld f (fr, w) = .fault e (fr, w) := by
  simp [Eval.world, Frames.withWorld, h]

/-- A `when` on the cells the handles name: holds them, or panics with `deadlock` before it
holds anything if one is held (shared.when-on-value-already-held), then runs the block with
each name a variable of its cell's value, which it puts back however the block ends
(shared.when). A `when` names one variable for each handle. -/
def held (M : Memory σ) (block : Eval σ Value) (names : List Name) (handles : List Value) :
    Eval σ Value := do
  let cells ← ofExcept (handles.mapM Value.cellOf)
  let vs ← world M (fun w => (World.take cells w).map fun p => (.list p.1, p.2)) >>= asList
  if names.length = vs.length then withVars M (names.zip vs) (release M (names.zip cells) block)
  else fail .stuck

/-- An operation other than one on the world runs as its value, in the world it found. -/
theorem world_of_ne {τ : Type} (F : Frames τ) {o : Op} (ho : ∀ k, o ≠ .world k) (vs : List Value) :
    Eval.world F.withWorld (o.run vs) = Eval.ofExcept (o.apply vs) := by
  funext s
  obtain ⟨fr, x⟩ := s
  cases h : o.apply vs with
  | ok v => rw [world_ok (by rw [Op.run_of_ne ho, h]; rfl)]; rfl
  | error e => rw [world_error (by rw [Op.run_of_ne ho, h]; rfl)]; rfl

theorem world_memoryWith_of_ne (w : WriteBack) {o : Op} (ho : ∀ k, o ≠ .world k) (vs : List Value) :
    Eval.world (Copy.memoryWith w) (o.run vs) = Eval.ofExcept (o.apply vs) :=
  world_of_ne _ ho vs

/-- Runs the body of a `for` loop with `x` bound to each element of its
iterable in turn (expressions.for-iterables). -/
def loop (M : Memory σ) (run : Expr → Eval σ Value) (x : Name) (iterable body : Expr) :
    Eval σ Value := do
  -- The loop reads the value its iterable had when the loop started, as
  -- copy-on-write makes it do (modes.change-while-iterating). E0404 makes a change to
  -- that place during the loop an error anyway.
  let vs ← run iterable >>= asList
  forEach (fun v => withVar M x v (turn (run body))) vs
  pure .unit

end Eval

section

variable {σ : Type} (D : Decls) (M : Memory σ)

/-- Evaluates an expression, with at most `fuel` nested steps. Each case
follows the rule its constructor cites in `Stilt.Syntax`. -/
def eval : Nat → Expr → Eval σ Value
  | 0, _ => Eval.outOfFuel
  | n + 1, e =>
    let run := eval n
    match e with
    | .var x | .move x => Eval.inspect fun s => M.read s x []
    | .int k => pure (.int k)
    | .bool b => pure (.bool b)
    | .unit => pure .unit
    | .record R _ fields => do
      let written ← Eval.fields run fields
      Eval.declare D R written
    | .variant T _ C payload => do
      let vs ← Eval.list run payload
      pure (.variant T C vs)
    | .list _ es => do
      let vs ← Eval.list run es
      pure (.list vs)
    | .op o es => do
      let vs ← Eval.list run es
      Eval.world M (o.run vs)
    | .view es => do
      let vs ← Eval.list run es
      Eval.ofExcept (Op.view.apply vs)
    | .field e f => do
      let v ← run e
      Eval.ofExcept (v.get [.field f])
    | .index e i => do
      let v ← run e
      let k ← run i >>= Eval.asInt
      Eval.ofExcept (v.get [.index k])
    | .fnRef f types rows => pure (.function f types rows)
    | .method trait m τ => Eval.method D trait m τ
    | .closure ps result ρ body => do
      let captured ← Eval.inspect (M.capture · (Expr.captures ps body))
      pure (.closure captured ps result ρ body)
    | .call callee args _ => do
      let f ← run callee
      let passed ← Eval.args run args
      Eval.callAs D M run false f passed
    | .letIn x _ init body => do
      let v ← run init
      Eval.withInit M x init v (run body)
    | .varIn x _ init body => do
      let v ← run init
      Eval.withInit M x init v (run body)
    | .assign ⟨x, projections⟩ value => Eval.assign M run x projections value
    | .seq a b => do
      let _ ← run a
      run b
    | .if c _ a b => do
      let v ← run c >>= Eval.asBool
      if v then run a else run b
    | .match e _ arms => do
      let v ← run e
      Eval.select M run arms v
    | .for x _ e body => Eval.loop M run x e body
    | .raise e => do
      let v ← run e
      Eval.throw v
    | .try e | .form _ e => run e
    | .tryCatch e _ x handler _ => Eval.handle (run e) fun err => Eval.withVar M x err (run handler)
    | .while c body => do
      if ← run c >>= Eval.asBool then
        if ← Eval.turn (run body) then run (.while c body) else pure .unit
      else pure .unit
    | .loop body => do
      if ← Eval.turn (run body) then run (.loop body) else pure .unit
    | .break => Eval.jump .brk
    | .continue => Eval.jump .cont
    | .return e => do
      let v ← run e
      Eval.jump (.ret v)
    | .perform op e => do
      let v ← run e
      Eval.perform M op v
    | .withH E c h b => do
      let hv ← run h
      Eval.letGo M (Eval.handleWith M E c hv (fun f v => Eval.callAs D M run c f [.value v]) (run b))
    | .held names handles body => do
      let hs ← Eval.list run handles
      Eval.held M (run body) (names.map Prod.fst) hs

end

/-! ## Programs -/

/-- How a function's body ends is how the function does: a `return` ends it
with its value (expressions.closure-boundaries). A performance that reaches the
end of `main` has no handler, which type soundness rules out
(handlers.no-effect-reaches-main), so it is stuck. -/
def Outcome.leaveBody {σ : Type} : Outcome σ Value → Outcome σ Value
  | .jumped (.ret v) s => .done v s
  | .performed .. => .stuck
  | o => o

/-- Runs `main` in a model of memory, from an initial state: its body, which a
`return` ends (program.main). -/
def Program.run {σ : Type} (M : Memory σ) (init : σ) (p : Program) (fuel : Nat) :
    Outcome σ Value :=
  (eval p.decls M fuel p.main init).leaveBody

/-- Runs `main` as the reference interpreter does, on an input (std.io). -/
def Program.runCopy (p : Program) (fuel : Nat) (input : String := "") : Outcome Copy.State Value :=
  p.run Copy.memory ([], World.start input) fuel

/-- Runs `main` with copy-in, copy-out, writing `inout` arguments back in the
order `w`. With values.inout-argument-order's's order, it is the reference interpreter's run. -/
def Program.runCopyWith (w : WriteBack) (p : Program) (fuel : Nat) (input : String := "") :
    Outcome Copy.State Value :=
  p.run (Copy.memoryWith w) ([], World.start input) fuel

theorem Program.runCopyWith_leftToRight (p : Program) (fuel : Nat) (input : String) :
    p.runCopyWith .leftToRight fuel input = p.runCopy fuel input := rfl

/-- Runs `main` with `inout` arguments passed by reference. -/
def Program.runInPlace (p : Program) (fuel : Nat) (input : String := "") :
    Outcome (InPlace.State × World) Value :=
  p.run InPlace.memory (⟨[], []⟩, World.start input) fuel

/-- What a run shows of its outcome: everything but the final state. -/
inductive Observation where
  | returned (v : Value)
  | raised (error : Value)
  | jumped (jump : Jump)
  | panicked (kind : PanicKind)
  | outOfFuel
  | stuck

/-- What an outcome shows. -/
def Outcome.observe {σ : Type} : Outcome σ Value → Observation
  | .done v _ => .returned v
  | .raised e _ => .raised e
  | .jumped j _ => .jumped j
  | .panicked k _ => .panicked k
  | .performed .. => .stuck
  | .outOfFuel => .outOfFuel
  | .stuck => .stuck

/-- The output and standard error that an outcome's world holds, when it ends in a state. -/
def Outcome.output {σ α : Type} : Outcome (σ × World) α → Option Output
  | .done _ s | .raised _ s | .jumped _ s | .panicked _ s | .performed _ _ s _ => some s.2.output
  | .outOfFuel | .stuck => none

/-- What a run shows: its observation, and what it wrote to its output and standard error,
however it ends; `Stilt.Run.Program` gives the exit status it makes. -/
def Outcome.shows {σ : Type} (o : Outcome (σ × World) Value) : Observation × Option Output :=
  (o.observe, o.output)

end Stilt
