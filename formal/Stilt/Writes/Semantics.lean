import Stilt.Views.Semantics
import Stilt.Writes.Syntax

/-!
# The semantics of writable views

A big-step evaluator with fuel, as `Stilt.Views.Eval` is, in one of two
models of a view (views.what-view-is and projections.writable-views):

* a **window**, the compiler's: every view, read-only or writable, is the
  location of its source's storage, the path to the viewed list within it, and
  two offsets. Reading through it reads that storage as it is now, and a write
  through `v[i]` writes it at once;
* a **copy**: every view is the viewed part, copied when it is made. A
  writable binding writes its copy, and writes it back into the place its view
  was made from when its scope ends, as copy-in, copy-out writes an `inout`
  argument back (values.inout-argument-order).

Only `View.of` and `view.into` read the model. A view that `view.into` made
is, as a copy, the part with the place it writes back to (`pending`); a binding
that doesn't write holds it as the part alone (projections.what-view-writes).
-/

namespace Stilt.Writes

open Stilt.Views (Store bounded slice cell source Model)

/-- Run-time values: a value of the core calculus, or a view. -/
inductive WVal where
  | val (v : Value)
  /-- A view as a window: its source's location, the path to the viewed list
  within it, and the offsets of the part (views.what-view-is). -/
  | window (loc : Nat) (path : Path) (start stop : Int)
  /-- A view as a copy of the viewed part. -/
  | copied (part : List Value)
  /-- A view that `view.into` made, as a copy: the part, and the place it
  writes back to. -/
  | pending (part : List Value) (loc : Nat) (path : Path) (start stop : Int)

/-- What a variable holds: a location, a view that reads, or the view of a
writable binding (projections.writable-bindings). -/
inductive WBinding where
  | loc (loc : Nat)
  | view (view : WVal)
  | writes (view : WVal)

/-- The variables in scope, the newest first, and the store. -/
structure WState where
  env : List (Name × WBinding)
  store : Store

/-- A list with its part from `a` to `b` replaced. -/
def splice (vs : List Value) (a b : Int) (part : List Value) : List Value :=
  vs.take a.toNat ++ (part ++ vs.drop b.toNat)

/-- A value with the part from `a` to `b` of the list along `π` replaced by
`part`: the write-back of a writable binding's copy (values.inout-argument-order; projections.writable-views),
which needs the list there, the offsets within it and the part
of their length. -/
def restore (c : Value) (π : Path) (a b : Int) (part : List Value) : Except Fault Value :=
  match c.get π with
  | .ok (.list vs) =>
    if bounded vs.length a b && part.length == (b - a).toNat then
      c.set π (.list (splice vs a b part))
    else .error .stuck
  | _ => .error .stuck

/-- A value of the core calculus, as a run-time value. -/
def lift : Except Fault Value → Except Fault WVal
  | .ok v => .ok (.val v)
  | .error f => .error f

namespace WVal

/-- The part a view reads now, as `Stilt.Views.RVal.part` gives it. -/
def part (store : Store) : WVal → Except Fault (List Value)
  | .window ℓ π a b =>
    match source store ℓ π with
    | .ok (.list vs) => if bounded vs.length a b then .ok (slice vs a b) else .error .stuck
    | _ => .error .stuck
  | .copied part | .pending part _ _ _ _ => .ok part
  | .val _ => .error .stuck

/-- `v.len()` (views.functions-of-views). -/
def len : WVal → Except Fault Int
  | .window _ _ a b => .ok (b - a)
  | .copied part | .pending part _ _ _ _ => .ok part.length
  | .val _ => .error .stuck

/-- The element at an index of the part a view reads, which panics with
`bounds` out of it (views.functions-of-views). -/
def elem (store : Store) (r : WVal) (k : Int) : Except Fault Value :=
  match r.part store with
  | .ok part =>
    match elemAt? part k with
    | some v => .ok v
    | none => .error (.panic .bounds)
  | .error f => .error f

/-- `e[k]` on a list or a view. -/
def index (store : Store) : WVal → Int → Except Fault WVal
  | .val v, k => lift (v.get [.index k])
  | r, k => lift (r.elem store k)

/-- `v.view(s, e)`, which panics with `bounds` as `View.of` does (views.making-view and views.functions-of-views). A part reads, so a copy's is the part alone (projections.writable-views). -/
def sub : WVal → Int → Int → Except Fault WVal
  | .window ℓ π a b, s, e =>
    if bounded (b - a).toNat s e then .ok (.window ℓ π (a + s) (a + e))
    else .error (.panic .bounds)
  | .copied part, s, e | .pending part _ _ _ _, s, e =>
    if bounded part.length s e then .ok (.copied (slice part s e)) else .error (.panic .bounds)
  | .val _, _, _ => .error .stuck

/-- The view a binding that doesn't write holds: a copy's part alone
(projections.what-view-writes). -/
def readOnly : WVal → WVal
  | .pending part _ _ _ _ => .copied part
  | r => r

/-- `v[k] = w` on a copy: its part with the element replaced, which panics
with `bounds` out of it (projections.places-through-views). -/
def put : WVal → Int → Value → Except Fault WVal
  | .copied part, k, w =>
    match elemAt? part k with
    | some _ => .ok (.copied (part.set k.toNat w))
    | none => .error (.panic .bounds)
  | .pending part ℓ π a b, k, w =>
    match elemAt? part k with
    | some _ => .ok (.pending (part.set k.toNat w) ℓ π a b)
    | none => .error (.panic .bounds)
  | _, _, _ => .error .stuck

end WVal

/-- `View.of` (`writes` off) and `view.into` (`writes` on) on the list along
`π` from the location `ℓ`, in the model `M`: they panic with `bounds` unless
`0 ≤ start ≤ end ≤ len` (views.making-view; projections.writable-views). -/
def makeView (M : Model) (writes : Bool) (store : Store) (ℓ : Nat) (π : Path) (a b : Int) :
    Except Fault WVal :=
  match source store ℓ π with
  | .ok (.list vs) =>
    if bounded vs.length a b then
      .ok (match M, writes with
        | .window, _ => .window ℓ π a b
        | .copy, false => .copied (slice vs a b)
        | .copy, true => .pending (slice vs a b) ℓ π a b)
    else .error (.panic .bounds)
  | .ok _ => .error .stuck
  | .error f => .error f

/-- Writes the value along `π` at the location `ℓ` (values.let-and-var and values.assignment-order). -/
def setCell (store : Store) (ℓ : Nat) (π : Path) (w : Value) : Except Fault Store :=
  match cell store ℓ with
  | .ok v =>
    match v.set π w with
    | .ok v' => .ok (store.set ℓ (some v'))
    | .error f => .error f
  | .error f => .error f

/-- What the end of a binding's scope does to the store: it frees a location
(expressions.scope), and writes a copy that `view.into` made back (projections.what-view-writes). -/
def release : WBinding → Store → Except Fault Store
  | .loc ℓ, store => .ok (store.set ℓ none)
  | .writes (.pending part ℓ π a b), store =>
    match cell store ℓ with
    | .ok c =>
      match restore c π a b part with
      | .ok c' => .ok (store.set ℓ (some c'))
      | .error f => .error f
    | .error f => .error f
  | .writes (.val _), store | .writes (.window _ _ _ _), store | .writes (.copied _), store
  | .view _, store => .ok store

namespace WState

/-- The location a variable that holds a value has. -/
def loc? (s : WState) (x : Name) : Except Fault Nat :=
  match s.env.lookup x with
  | some (.loc ℓ) => .ok ℓ
  | _ => .error .stuck

/-- Reads a variable: its value, or the view it holds, which reads the
variable when it is a writable binding (projections.places-through-views). -/
def read (s : WState) (x : Name) : Except Fault WVal :=
  match s.env.lookup x with
  | some (.loc ℓ) => lift (cell s.store ℓ)
  | some (.view r) => .ok r
  | some (.writes r) => .ok r.readOnly
  | none => .error .stuck

/-- `x[k] = w` through the view `r` of the writable binding `x` (projections.places-through-views): a window writes its source's storage, a copy its part. Indexes out
of the part panic with `bounds`. -/
def through (s : WState) (x : Name) (r : WVal) (k : Int) (w : Value) : Except Fault WState :=
  match r with
  | .window ℓ π a b =>
    if 0 ≤ k ∧ k < b - a then
      match setCell s.store ℓ (π ++ [.index (a + k)]) w with
      | .ok st => .ok { s with store := st }
      | .error f => .error f
    else .error (.panic .bounds)
  | r =>
    match r.put k w with
    | .ok r' => .ok { s with env := assocSet s.env x (.writes r') }
    | .error f => .error f

/-- Writes a place where it is (values.let-and-var and values.assignment-order), or `v[k]` through a
writable binding. A view that reads is no place (projections.places-through-views). -/
def write (s : WState) (x : Name) (π : Path) (w : Value) : Except Fault WState :=
  match s.env.lookup x, π with
  | some (.loc ℓ), π =>
    match setCell s.store ℓ π w with
    | .ok st => .ok { s with store := st }
    | .error f => .error f
  | some (.writes r), [.index k] => s.through x r k w
  | _, _ => .error .stuck

/-- Binds a variable: a value to a new location, a view to itself, as a
writable binding when `w` holds (projections.writable-bindings). -/
def bind (s : WState) (w : Bool) (x : Name) : WVal → WState
  | .val v => ⟨(x, .loc s.store.length) :: s.env, s.store ++ [some v]⟩
  | r => { s with env := (x, if w then .writes r else .view r.readOnly) :: s.env }

/-- Ends the scope of the newest binding (expressions.scope). -/
def unbind (s : WState) : Except Fault WState :=
  match s.env with
  | (_, b) :: env =>
    match release b s.store with
    | .ok st => .ok ⟨env, st⟩
    | .error f => .error f
  | [] => .ok s

end WState

end Stilt.Writes
