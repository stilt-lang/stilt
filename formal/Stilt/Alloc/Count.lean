import Stilt.Alloc.Sites
import Stilt.Semantics

/-!
# Counting allocations

The reference interpreter's evaluator with a count of the allocations it makes beside its
state: `Count.eval` is `eval` in copy-in, copy-out, step for step, but that each operation that
makes a value needing storage of its own adds one to the count when it makes it
(facts.allocation and facts.native-allocation): a list literal, a closure literal, a record
literal of a recursive type, a variant's constructor with a payload of one, a native that
allocates, a `with` and a performance. A call's count goes on in its callee, and comes back
with it.

What the count leaves out is the copy that a write through an index makes when the list it
writes is shared, and the copy that a call makes for an in-place parameter
(facts.writes-in-place and facts.copy-at-call): the model's values are trees that no two
bindings share, so no step of its evaluator copies a list, and whether one would is the
question of storage that facts.in-place-promise answers.
-/

namespace Stilt

namespace Count

/-- A frame with the count of allocations made so far. -/
abbrev Frame := Copy.Frame × Nat

/-- A state: a frame with its count, and the world. -/
abbrev State := Frame × World

/-- The frames of copy-in, copy-out with a count that reading, writing, binding and calling
leave as it is, a call ending with its callee's count. -/
def frames : Frames Frame where
  read fr x p := Copy.read fr.1 x p
  write fr x p v := (·, fr.2) <$> Copy.write fr.1 x p v
  bind fr x v := ((x, v) :: fr.1, fr.2)
  bindMoved fr y _ v := ((y, v) :: fr.1, fr.2)
  unbind fr := (fr.1.tail, fr.2)
  capture fr keep := pure (newestOf keep fr.1)
  enter fr captured params := (·, fr.2) <$> Copy.enter fr.1 captured params
  leave caller callee params := (·, callee.2) <$> Copy.leave caller.1 callee.1 params

/-- Copy-in, copy-out with a count of allocations. -/
def memory : Memory State := frames.withWorld

/-- A state of copy-in, copy-out with the count `c`. -/
def lift (c : Nat) (s : Copy.State) : State := ((s.1, c), s.2)

/-- One more allocation. -/
def tick : Eval State Unit := fun s => .done () ((s.1.1, s.1.2 + 1), s.2)

/-- An allocation when `b` says so. -/
def tickIf (b : Bool) : Eval State Unit := if b then tick else pure ()

section

variable (D : Decls)

/-- `eval`, with a count of the allocations made (facts.allocation). -/
def eval : Nat → Expr → Eval State Value
  | 0, _ => Eval.outOfFuel
  | n + 1, e =>
    let run := eval n
    match e with
    | .var x | .move x => Eval.inspect fun s => memory.read s x []
    | .int k => pure (.int k)
    | .bool b => pure (.bool b)
    | .unit => pure .unit
    | .record R _ fields => do
      let written ← Eval.fields run fields
      tickIf (D.recursive R)
      Eval.declare D R written
    | .variant T args C payload => do
      let vs ← Eval.list run payload
      tickIf (D.payloadRecursive T args C)
      pure (.variant T C vs)
    | .list _ es => do
      let vs ← Eval.list run es
      tick
      pure (.list vs)
    | .op o es => do
      let vs ← Eval.list run es
      tickIf o.allocates
      Eval.world memory (o.run vs)
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
      tick
      let captured ← Eval.inspect (memory.capture · (Expr.captures ps body))
      pure (.closure captured ps result ρ body)
    | .call callee args _ => do
      let f ← run callee
      let passed ← Eval.args run args
      Eval.callAs D memory run false f passed
    | .letIn x _ init body => do
      let v ← run init
      Eval.withInit memory x init v (run body)
    | .varIn x _ init body => do
      let v ← run init
      Eval.withInit memory x init v (run body)
    | .assign ⟨x, projections⟩ value => Eval.assign memory run x projections value
    | .seq a b => do
      let _ ← run a
      run b
    | .if c _ a b => do
      let v ← run c >>= Eval.asBool
      if v then run a else run b
    | .match e _ arms => do
      let v ← run e
      Eval.select memory run arms v
    | .for x _ e body => Eval.loop memory run x e body
    | .raise e => do
      let v ← run e
      Eval.throw v
    | .try e | .form _ e => run e
    | .tryCatch e _ x handler _ =>
      Eval.handle (run e) fun err => Eval.withVar memory x err (run handler)
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
      tick
      Eval.perform memory op v
    | .withH E c h b => do
      let hv ← run h
      tick
      Eval.letGo memory
        (Eval.handleWith memory E c hv (fun f v => Eval.callAs D memory run c f [.value v]) (run b))
    | .held names handles body => do
      let hs ← Eval.list run handles
      Eval.held memory (run body) (names.map Prod.fst) hs

end

end Count

/-- An outcome of copy-in, copy-out with the count `c` beside each of its states. -/
def Outcome.atCount {α : Type} (c : Nat) : Outcome Copy.State α → Outcome Count.State α
  | .done a s => .done a (Count.lift c s)
  | .raised e s => .raised e (Count.lift c s)
  | .jumped j s => .jumped j (Count.lift c s)
  | .panicked k s => .panicked k (Count.lift c s)
  | .performed op v s k => .performed op v (Count.lift c s) fun w x => (k w x).atCount c
  | .outOfFuel => .outOfFuel
  | .stuck => .stuck

end Stilt
