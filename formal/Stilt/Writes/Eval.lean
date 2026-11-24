import Stilt.Views.Eval
import Stilt.Writes.Semantics

/-!
# The evaluator of writable views

The evaluator, generic in the model of a view, written in the monad of
`Stilt.Eval` as `Stilt.Views.veval` is, and the runs of a program.
-/

namespace Stilt.Writes

open Stilt.Views (Model)

namespace Run

variable {α : Type}

/-- The value a run-time value is, if it isn't a view: a view can't be stored
(views.view-types). -/
def asVal : WVal → Eval WState Value
  | .val v => pure v
  | _ => Eval.fail .stuck

/-- The integer a run-time value is: an index or an offset. -/
def asInt : WVal → Eval WState Int
  | .val (.int k) => pure k
  | _ => Eval.fail .stuck

/-- Runs `m` with `x` bound to `r`, writable when `w` holds, and ends the
binding however `m` ends (expressions.scope), which writes a copy that
`view.into` made back. No step of the calculus performs an operation, so a
performance is stuck. -/
def within (w : Bool) (x : Name) (r : WVal) (m : Eval WState α) : Eval WState α := fun s =>
  match m (s.bind w x r) with
  | .done a s' =>
    match s'.unbind with
    | .ok s'' => .done a s''
    | .error f => .fault f s'
  | .raised e s' => .raised e s'
  | .jumped j s' => .jumped j s'
  | .panicked k s' => .panicked k s'
  | .performed .. => .stuck
  | .outOfFuel => .outOfFuel
  | .stuck => .stuck

/-- Evaluates a place, a variable followed by indexes: its root and its path,
with its indexes evaluated from left to right (values.left-to-right). -/
def place (run : WExpr → Eval WState WVal) : WExpr → Eval WState (Name × Path)
  | .var x => pure (x, [])
  | .index e i => do
    let p ← place run e
    let k ← run i >>= asInt
    pure (p.1, p.2 ++ [.index k])
  | _ => Eval.fail .stuck

/-- Evaluates expressions from left to right, each to a value (values.left-to-right). -/
def vals (run : WExpr → Eval WState WVal) : List WExpr → Eval WState (List Value)
  | [] => pure []
  | e :: es => do
    let v ← run e >>= asVal
    let vs ← vals run es
    pure (v :: vs)

/-- Assigns the value of an expression to a place: the indexes, then the
value, then the store or the view (values.assignment-order; projections.places-through-views). -/
def assign (run : WExpr → Eval WState WVal) (target value : WExpr) : Eval WState WVal := do
  let p ← place run target
  let w ← run value >>= asVal
  Eval.update fun s => s.write p.1 p.2 w
  pure (.val .unit)

/-- `View.of(source, a, b)` or `view.into(inout source, a, b)`: the place, then
the offsets, from left to right, then the view (views.making-view; projections.writable-views). -/
def make (M : Model) (writes : Bool) (run : WExpr → Eval WState WVal) (src start stop : WExpr) :
    Eval WState WVal := do
  let p ← place run src
  let a ← run start >>= asInt
  let b ← run stop >>= asInt
  Eval.inspect fun s =>
    match s.loc? p.1 with
    | .ok ℓ => makeView M writes s.store ℓ p.2 a b
    | .error f => .error f

end Run

open Run in
/-- Evaluates an expression, with at most `fuel` nested steps, in the model of
a view `M`. Each case follows the rule its constructor cites in
`Stilt.Writes.Syntax`. -/
def weval (M : Model) : Nat → WExpr → Eval WState WVal
  | 0, _ => Eval.outOfFuel
  | n + 1, e =>
    let run := weval M n
    match e with
    | .var x => Eval.inspect fun s => s.read x
    | .int k => pure (.val (.int k))
    | .list _ es => do
      let vs ← vals run es
      pure (.val (.list vs))
    | .index e i => do
      let r ← run e
      let k ← run i >>= asInt
      Eval.inspect fun s => r.index s.store k
    | .letIn x _ init body => do
      let r ← run init
      within false x r (run body)
    | .varIn x τ init body => do
      let r ← run init
      within (writable τ) x r (run body)
    | .assign target value => assign run target value
    | .seq a b => do
      let _ ← run a
      run b
    | .viewOf src a b => make M false run src a b
    | .into src a b => make M true run src a b
    | .sub v a b => do
      let r ← run v
      let s ← run a >>= asInt
      let t ← run b >>= asInt
      Eval.ofExcept (r.sub s t)
    | .len v => do
      let r ← run v
      let k ← Eval.ofExcept r.len
      pure (.val (.int k))

/-- What a run shows of its value: a value, or the part a view reads. -/
def shown (store : Stilt.Views.Store) : WVal → Observation
  | .val v => .returned v
  | r =>
    match r.part store with
    | .ok part => .returned (.list part)
    | .error _ => .stuck

namespace WProgram

/-- Runs the body in the model `M`, from an empty state. -/
def run (M : Model) (p : WProgram) (fuel : Nat) : Outcome WState WVal :=
  weval M fuel p.body ⟨[], []⟩

/-- What a run shows of its outcome. -/
def observe (M : Model) (p : WProgram) (fuel : Nat) : Observation :=
  match p.run M fuel with
  | .done r s => shown s.store r
  | .raised e _ => .raised e
  | .jumped j _ => .jumped j
  | .panicked k _ => .panicked k
  | .performed .. => .stuck
  | .outOfFuel => .outOfFuel
  | .stuck => .stuck

end WProgram

end Stilt.Writes
