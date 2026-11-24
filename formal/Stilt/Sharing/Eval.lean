import Stilt.Sharing.Memory
import Stilt.Sharing.Names

/-!
# The evaluator of sharing

The evaluator of `Stilt.Semantics` in the model `Sharing.memory`, but where a `let` or a `var`
binds, where an assignment writes and where a call starts. A program's bindings get the
uniqueness that the inference of modes.shared-writes gives them (`Program.isShared`), by
name: the inference reads each body once, as `stilt show` prints its facts
(modes.bindings-and-axes), and a binding is `shared` when its name is that of a binding the
inference calls shared, so in a program whose bindings have distinct names, as the reference
interpreter's export gives them, each binding has its own verdict; in any other program, every
binding is shared.

* A `let` or a `var` whose initializer is a place, at a copy-on-write type, shares that place's
  storage (modes.copies).
* An assignment to a place with a path is a modification of its root (modes.kinds-of-access);
  one to the whole of a binding replaces its value.
* A closure literal reads the bindings it captures, and no other (expressions.capture): a
  binding that a write in place reached is one that nothing reads after it.
* A call's `inout` arguments are modifications of their roots when the call starts
  (modes.kinds-of-access): a root that is `shared` gets its own copy then, before the callee's
  parameters refer to its place.
-/

namespace Stilt

namespace Sharing

/-- Gives each root of an `inout` argument that is `shared` its own copy, when the call starts
(modes.kinds-of-access and modes.shared-writes). A root that names no binding is left to the
call's start, which reads the arguments in order and fails there as copies do. -/
def unshareArgs : List Passed → Eval (State × World) Unit
  | [] => pure ()
  | .place x _ :: rest => do
    Eval.update fun s => match s.1.env.lookup x with
      | some e => if e.unique then .ok s else (·, s.2) <$> unshare s.1 x
      | none => .ok s
    unshareArgs rest
  | _ :: rest => unshareArgs rest

/-- Runs `m` with `x` bound to the value `v` of its initializer `init`, sharing the place
`init` names when it names one and `τ` is a copy-on-write type (modes.copies), `unique` unless
`shared` names it, and ends the binding however `m` ends (expressions.scope). -/
def bindIn (D : Decls) (shared : Name → Bool) (x : Name) (τ : Ty) (init : Expr) (v : Value)
    (m : Eval (State × World) Value) : Eval (State × World) Value := fun s =>
  let unique := !shared x
  let fr := match aliasRef? s.1 init with
    | some r => if D.cow τ then bindAlias s.1 x v r unique else bindWith s.1 x v unique (D.cow τ)
    | none => bindWith s.1 x v unique (D.cow τ)
  (m (fr, s.2)).unbind (memory shared)

/-- Assigns a value to the place `x` and `path`: a modification when the path isn't empty,
and otherwise a replacement of the whole binding, by the place `value` when it names one. -/
def assign (run : Expr → Eval (State × World) Value) (x : Name)
    (projections : List Projection) (value : Expr) : Eval (State × World) Value := do
  let path ← Eval.path run projections
  let v ← run value
  Eval.update fun s => (·, s.2) <$>
    if projections.isEmpty then assignWhole s.1 x v (aliasRef? s.1 value)
    else modify s.1 x path v
  pure .unit

/-- A step of the evaluator of sharing on a form that builds or reads a value, `run`
evaluating its parts. -/
def evalValue (D : Decls) (shared : Name → Bool) (run : Expr → Eval (State × World) Value) :
    Expr → Eval (State × World) Value
  | .var x | .move x => Eval.inspect fun s => (memory shared).read s x []
  | .int n => pure (.int n)
  | .bool b => pure (.bool b)
  | .unit => pure .unit
  | .record R fields => do
    let written ← Eval.fields run fields
    Eval.declare D R written
  | .variant T C payload => do
    let vs ← Eval.list run payload
    pure (.variant T C vs)
  | .list _ es => do
    let vs ← Eval.list run es
    pure (.list vs)
  | .op o es => do
    let vs ← Eval.list run es
    Eval.world (memory shared) (o.run vs)
  | .view es => do
    let vs ← Eval.list run es
    Eval.ofExcept (Op.view.apply vs)
  | .field e f => do
    let v ← run e
    Eval.ofExcept (v.get [.field f])
  | .index e i => do
    let v ← run e
    let n ← run i >>= Eval.asInt
    Eval.ofExcept (v.get [.index n])
  | .fnRef f types rows => pure (.function f types rows)
  | .method trait m τ => Eval.method D trait m τ
  | .closure ps result ρ body => do
    let captured ← Eval.inspect fun s => readCaptured s.1 (captureOf ps body s.1.env)
    pure (.closure captured ps result ρ body)
  | .call callee args _ => do
    let f ← run callee
    let passed ← Eval.args run args
    unshareArgs passed
    Eval.callAs D (memory shared) run false f passed
  | _ => Eval.fail .stuck

/-- A step of the evaluator of sharing, `run` evaluating its parts: on a form that binds,
assigns, chooses, loops, jumps, raises, performs or holds, and on the others as `evalValue`. -/
def evalControl (D : Decls) (shared : Name → Bool) (run : Expr → Eval (State × World) Value) :
    Expr → Eval (State × World) Value
  | .letIn x τ init body => do
    let v ← run init
    bindIn D shared x τ init v (run body)
  | .varIn x τ init body => do
    let v ← run init
    bindIn D shared x τ init v (run body)
  | .assign ⟨x, projections⟩ value => assign run x projections value
  | .seq a b => do
    let _ ← run a
    run b
  | .if c _ a b => do
    let v ← run c >>= Eval.asBool
    if v then run a else run b
  | .match e _ arms => do
    let v ← run e
    Eval.select (memory shared) run arms v
  | .for x _ e body => Eval.loop (memory shared) run x e body
  | .raise e => do
    let v ← run e
    Eval.throw v
  | .try e => run e
  | .tryCatch e _ x handler _ =>
    Eval.handle (run e) fun err => Eval.withVar (memory shared) x err (run handler)
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
    Eval.perform (memory shared) op v
  | .withH E c h b => do
    let hv ← run h
    Eval.letGo (memory shared) (Eval.handleWith (memory shared) E c hv
      (fun f v => Eval.callAs D (memory shared) run c f [.value v]) (run b))
  | .held names handles body => do
    let hs ← Eval.list run handles
    Eval.held (memory shared) (run body) (names.map Prod.fst) hs
  | e => evalValue D shared run e

end Sharing

/-- Evaluates an expression in the model of sharing, where the bindings that `shared` names are
`shared`, with at most `fuel` nested steps. Each case is `eval`'s in `Sharing.memory`, but for
the bindings it makes, the assignments it makes, the closures it captures and the calls it
starts. -/
def Sharing.eval (D : Decls) (shared : Name → Bool) :
    Nat → Expr → Eval (Sharing.State × World) Value
  | 0, _ => Eval.outOfFuel
  | n + 1, e => Sharing.evalControl D shared (Sharing.eval D shared n) e

/-- Runs `main` with copies into bindings that share storage, and writes that copy first only
where the inference of modes.shared-writes calls them shared, on an input. -/
def Program.runSharing (p : Program) (fuel : Nat) (input : String := "") :
    Outcome (Sharing.State × World) Value :=
  (Sharing.eval p.decls p.isShared fuel p.main (⟨[], #[]⟩, World.start input)).leaveBody

end Stilt
