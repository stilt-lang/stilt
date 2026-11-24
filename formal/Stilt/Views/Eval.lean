import Stilt.Views.Semantics

/-!
# The evaluator of views

The steps of the evaluator, written in the monad of `Stilt.Eval`, and the
evaluator, generic in the model of a view. Only `View.of` reads the model:
every other operation does the same to a window and to a copy, as their
functions in `Stilt.Views.Semantics` say.
-/

namespace Stilt.Views

namespace Run

variable {α β : Type}

/-- The value a run-time value is, if it isn't a view. A view is no value of
the core calculus: it can't be stored (views.view-types). -/
def asVal : RVal → Eval VState Value
  | .val v => pure v
  | _ => Eval.fail .stuck

/-- The integer a run-time value is: an index or an offset. -/
def asInt : RVal → Eval VState Int
  | .val (.int k) => pure k
  | _ => Eval.fail .stuck

/-- The Boolean a run-time value is: a condition (expressions.conditions). -/
def asBool : RVal → Eval VState Bool
  | .val (.bool b) => pure b
  | _ => Eval.fail .stuck

/-- Runs `m` with `x` bound to `r`, and ends the binding however `m` ends
(expressions.scope). No step of the views' calculus performs an operation, so
a performance is stuck. -/
def within (x : Name) (r : RVal) (m : Eval VState α) : Eval VState α := fun s =>
  match m (s.bind x r) with
  | .done a s' => .done a s'.unbind
  | .raised e s' => .raised e s'.unbind
  | .jumped j s' => .jumped j s'.unbind
  | .panicked k s' => .panicked k s'.unbind
  | .performed .. => .stuck
  | .outOfFuel => .outOfFuel
  | .stuck => .stuck

/-- Runs `m` and drops its value. -/
def discard (m : Eval VState α) : Eval VState Unit := do
  let _ ← m
  pure ()

/-- Stores a temporary in a new location that no variable names, which lasts
as long as the view made from it (views.making-view). -/
def temp (v : Value) : Eval VState Nat := fun s =>
  .done s.store.length { s with store := s.store ++ [some v] }

/-- Runs `step` on each element of a list, in order. -/
def each (step : β → Eval VState Unit) : List β → Eval VState Unit
  | [] => pure ()
  | b :: bs => do
    step b
    each step bs

/-- The offsets of a view's part of length `n`, in order. -/
def indices (n : Int) : List Int := (List.range n.toNat).map Int.ofNat

/-- Evaluates a place, a variable followed by fields and indexes: its root and
its path, with its indexes evaluated from left to right (values.index-reads). -/
def place (run : VExpr → Eval VState RVal) : VExpr → Eval VState (Name × Path)
  | .var x => pure (x, [])
  | .field e f => do
    let p ← place run e
    pure (p.1, p.2 ++ [.field f])
  | .index e i => do
    let p ← place run e
    let k ← run i >>= asInt
    pure (p.1, p.2 ++ [.index k])
  | _ => Eval.fail .stuck

/-- Evaluates expressions from left to right, each to a value (values.left-to-right). -/
def vals (run : VExpr → Eval VState RVal) : List VExpr → Eval VState (List Value)
  | [] => pure []
  | e :: es => do
    let v ← run e >>= asVal
    let vs ← vals run es
    pure (v :: vs)

/-- Evaluates the fields of a record literal in the order they are written
(values.left-to-right). -/
def fields (run : VExpr → Eval VState RVal) :
    List (Name × VExpr) → Eval VState (List (Name × Value))
  | [] => pure []
  | (f, e) :: rest => do
    let v ← run e >>= asVal
    let vs ← fields run rest
    pure ((f, v) :: vs)

/-- Assigns the value of an expression to a place: the indexes, then the
value, then the store (values.assignment-order). -/
def assign (run : VExpr → Eval VState RVal) (target value : VExpr) : Eval VState RVal := do
  let p ← place run target
  let w ← run value >>= asVal
  Eval.update fun s => s.write p.1 p.2 w
  pure (.val .unit)

/-- Runs the body of a `for` loop with `x` bound to each element in turn. A
list is iterated as it was when the loop started, as copy-on-write makes it
(modes.change-while-iterating); a view is read at each element, as a window reads its source
(views.for-over-view). -/
def loop (run : VExpr → Eval VState RVal) (x : Name) (r : RVal) (body : VExpr) :
    Eval VState Unit :=
  match r with
  | .val (.list vs) => each (fun v => discard (within x (.val v) (run body))) vs
  | .val _ => Eval.fail .stuck
  | r =>
    match r.len with
    | .ok n =>
      each (fun k => do
        let v ← Eval.inspect fun s => r.elem s.store k
        discard (within x (.val v) (run body))) (indices n)
    | .error f => Eval.fail f

/-- `View.of(source, start, end)`, in the model `M`. Its arguments are
evaluated from left to right, a place as the place it names, and the call then
reads the source (views.making-view). A source that is no place is stored in a
temporary. -/
def make (M : Model) (run : VExpr → Eval VState RVal) (src start stop : VExpr) :
    Eval VState RVal :=
  match src.shape? with
  | some _ => do
    let p ← place run src
    let a ← run start >>= asInt
    let b ← run stop >>= asInt
    Eval.inspect fun s =>
      match s.loc? p.1 with
      | .ok ℓ => M.make s.store ℓ p.2 a b
      | .error f => .error f
  | none => do
    let v ← run src >>= asVal
    let ℓ ← temp v
    let a ← run start >>= asInt
    let b ← run stop >>= asInt
    Eval.inspect fun s => M.make s.store ℓ [] a b

end Run

open Run in
/-- Evaluates an expression, with at most `fuel` nested steps, in the model of
a view `M`. Each case follows the rule its constructor cites in
`Stilt.Views.Syntax`. -/
def veval (D : Decls) (M : Model) : Nat → VExpr → Eval VState RVal
  | 0, _ => Eval.outOfFuel
  | n + 1, e =>
    let run := veval D M n
    match e with
    | .var x => Eval.inspect fun s => s.read x
    | .int k => pure (.val (.int k))
    | .bool b => pure (.val (.bool b))
    | .unit => pure (.val .unit)
    | .record R fs => do
      let w ← fields run fs
      let v ← Eval.declare D R w
      pure (.val v)
    | .list _ es => do
      let vs ← vals run es
      pure (.val (.list vs))
    | .field e f => do
      let v ← run e >>= asVal
      Eval.ofExcept (lift (v.get [.field f]))
    | .index e i => do
      let r ← run e
      let k ← run i >>= asInt
      Eval.inspect fun s => r.index s.store k
    | .letIn x _ init body | .varIn x _ init body => do
      let r ← run init
      within x r (run body)
    | .assign target value => assign run target value
    | .seq a b => do
      let _ ← run a
      run b
    | .if c _ a b => do
      let v ← run c >>= asBool
      if v then run a else run b
    | .for x _ it body => do
      let r ← run it
      loop run x r body
      pure (.val .unit)
    | .viewOf src a b => make M run src a b
    | .sub v a b => do
      let r ← run v
      let s ← run a >>= asInt
      let t ← run b >>= asInt
      Eval.ofExcept (r.sub s t)
    | .len v => do
      let r ← run v
      let k ← Eval.ofExcept r.len
      pure (.val (.int k))
    | .copy v => do
      let r ← run v
      Eval.inspect fun s => r.copy s.store

/-! ## Programs -/

/-- The caller's frame: each parameter in a location of its own, holding its
argument. The caller's storage outlives the call. -/
def frame : List Name → Nat → List (Name × Binding)
  | [], _ => []
  | x :: xs, i => (x, .loc i) :: frame xs (i + 1)

namespace VProgram

/-- The state the body starts in. -/
def start (p : VProgram) : VState :=
  ⟨frame (p.args.map (·.1)) 0, p.args.map fun a => some a.2.2⟩

/-- Runs the body in the model `M`. -/
def run (M : Model) (p : VProgram) (fuel : Nat) : Outcome VState RVal :=
  veval p.decls M fuel p.body p.start

end VProgram

/-- What the caller sees of a result: a value, or the part a view reads, as
`copy` would give it after the call returns. A window whose source is gone is
stuck. -/
def shown (store : Store) : RVal → Observation
  | .val v => .returned v
  | r =>
    match r.part store with
    | .ok part => .returned (.list part)
    | .error _ => .stuck

/-- What a run shows of its outcome. -/
def VProgram.observe (M : Model) (p : VProgram) (fuel : Nat) : Observation :=
  match p.run M fuel with
  | .done r s => shown s.store r
  | .raised e _ => .raised e
  | .jumped j _ => .jumped j
  | .panicked k _ => .panicked k
  | .performed .. => .stuck
  | .outOfFuel => .outOfFuel
  | .stuck => .stuck

end Stilt.Views
