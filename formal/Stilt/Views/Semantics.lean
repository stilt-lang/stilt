import Stilt.Semantics
import Stilt.Views.Syntax

/-!
# The semantics of views

A big-step evaluator with fuel, as `Stilt.Semantics` is, in one of two models
of a view (reference/rationale/13-modes.md, Views):

* a **window**, the compiler's: the location of the source's storage, the path
  to the viewed value within it, and two offsets. Reading through it reads the
  source's storage as it is now;
* a **copy**, the reference interpreter's: the viewed part, copied when the view is made.

The two models share everything else. A variable that holds a value has a
location of its own in the store, which its scope's end frees (expressions.scope), and a variable that holds a view holds it. A window that reads a
freed location, or a part that its source no longer has, is `stuck`: it
reads storage that is gone, which a compiler can't detect. The two models
agree on every program that obeys the law of exclusivity with the reads of
views, and whose views don't outlive their sources (`Stilt.Views.Agreement`).
-/

namespace Stilt.Views

/-- Run-time values: a value of the core calculus, or a view, in either
model. -/
inductive RVal where
  | val (v : Value)
  /-- A view as a window: its source's location, the path to the viewed list
  within it, and the offsets of the part (views.what-view-is). -/
  | window (loc : Nat) (path : Path) (start stop : Int)
  /-- A view as a copy of the viewed part. -/
  | copied (part : List Value)

/-- What a variable holds: a location of the store, or a view. -/
inductive Binding where
  | loc (loc : Nat)
  | view (view : RVal)

/-- The store: a value at each location, or none once its scope has ended. -/
abbrev Store := List (Option Value)

/-- The variables in scope, the newest first, and the store. -/
structure VState where
  env : List (Name × Binding)
  store : Store

/-- `0 ≤ start ≤ end ≤ len`, the offsets of a part of a list of `n` elements
(std.lists; views.making-view). -/
def bounded (n : Nat) (start stop : Int) : Bool := decide (0 ≤ start ∧ start ≤ stop ∧ stop ≤ n)

/-- The part of a list between two offsets, as `slice` gives it (std.lists). -/
def slice (vs : List Value) (start stop : Int) : List Value :=
  (vs.drop start.toNat).take (stop - start).toNat

/-- The value at a location, unless its scope has ended. -/
def cell (store : Store) (ℓ : Nat) : Except Fault Value :=
  match store[ℓ]? with
  | some (some v) => .ok v
  | _ => .error .stuck

/-- The value along a path from a location: a view's source. -/
def source (store : Store) (ℓ : Nat) (π : Path) : Except Fault Value :=
  match cell store ℓ with
  | .ok v => v.get π
  | .error f => .error f

/-- A value of the core calculus, as a run-time value. -/
def lift : Except Fault Value → Except Fault RVal
  | .ok v => .ok (.val v)
  | .error f => .error f

namespace RVal

/-- The part a view reads now. A window reads its source; one whose source is
gone, or has fewer elements than its end, is stuck. -/
def part (store : Store) : RVal → Except Fault (List Value)
  | .window ℓ π a b =>
    match source store ℓ π with
    | .ok (.list vs) => if bounded vs.length a b then .ok (slice vs a b) else .error .stuck
    | _ => .error .stuck
  | .copied part => .ok part
  | .val _ => .error .stuck

/-- `v.len()`, the viewed part's length (views.functions-of-views). A window knows it
from its offsets. -/
def len : RVal → Except Fault Int
  | .window _ _ a b => .ok (b - a)
  | .copied part => .ok part.length
  | .val _ => .error .stuck

/-- The element at an index of the part a view reads, which panics with
`bounds` out of it (views.functions-of-views). -/
def elem (store : Store) (r : RVal) (k : Int) : Except Fault Value :=
  match r.part store with
  | .ok part =>
    match elemAt? part k with
    | some v => .ok v
    | none => .error (.panic .bounds)
  | .error f => .error f

/-- `e[k]`: an element of a list (std.lists), or of the part a view reads
(views.functions-of-views). -/
def index (store : Store) : RVal → Int → Except Fault RVal
  | .val v, k => lift (v.get [.index k])
  | r, k => lift (r.elem store k)

/-- `v.view(s, e)`, with offsets counted from the view's start, which panics
with `bounds` as `View.of` does (views.making-view and views.functions-of-views). A window's part
moves its offsets. -/
def sub : RVal → Int → Int → Except Fault RVal
  | .window ℓ π a b, s, e =>
    if bounded (b - a).toNat s e then .ok (.window ℓ π (a + s) (a + e))
    else .error (.panic .bounds)
  | .copied part, s, e =>
    if bounded part.length s e then .ok (.copied (slice part s e)) else .error (.panic .bounds)
  | .val _, _, _ => .error .stuck

/-- `v.copy()`, the part a view reads, as a list (views.functions-of-views). -/
def copy (store : Store) (r : RVal) : Except Fault RVal :=
  lift ((r.part store).map .list)

end RVal

/-- The two models of a view (reference/rationale/13-modes.md, Views). -/
inductive Model where
  /-- The compiler's: a pointer and two offsets into the source's storage. -/
  | window
  /-- The reference interpreter's: a copy of the viewed part. -/
  | copy

/-- `View.of` on the list along `π` from the location `ℓ`: it panics with
`bounds` unless `0 ≤ start ≤ end ≤ len` (views.making-view). -/
def Model.make (M : Model) (store : Store) (ℓ : Nat) (π : Path) (a b : Int) :
    Except Fault RVal :=
  match source store ℓ π with
  | .ok (.list vs) =>
    if bounded vs.length a b then
      .ok (match M with
        | .window => .window ℓ π a b
        | .copy => .copied (slice vs a b))
    else .error (.panic .bounds)
  | .ok _ => .error .stuck
  | .error f => .error f

namespace VState

/-- The location a variable that holds a value has. -/
def loc? (s : VState) (x : Name) : Except Fault Nat :=
  match s.env.lookup x with
  | some (.loc ℓ) => .ok ℓ
  | _ => .error .stuck

/-- Reads a variable: its value, or the view it holds (values.independent-copies). -/
def read (s : VState) (x : Name) : Except Fault RVal :=
  match s.env.lookup x with
  | some (.loc ℓ) => lift (cell s.store ℓ)
  | some (.view r) => .ok r
  | none => .error .stuck

/-- Writes a place where it is (values.let-and-var and values.assignment-order). A view is no place
(views.escaping). -/
def write (s : VState) (x : Name) (π : Path) (w : Value) : Except Fault VState :=
  match s.loc? x with
  | .ok ℓ =>
    match cell s.store ℓ with
    | .ok v =>
      match v.set π w with
      | .ok v' => .ok { s with store := s.store.set ℓ (some v') }
      | .error f => .error f
    | .error f => .error f
  | .error f => .error f

/-- Binds a variable: a value to a new location, a view to itself. -/
def bind (s : VState) (x : Name) : RVal → VState
  | .val v => ⟨(x, .loc s.store.length) :: s.env, s.store ++ [some v]⟩
  | r => { s with env := (x, .view r) :: s.env }

/-- Ends the scope of the newest binding, and frees its location (expressions.scope). -/
def unbind (s : VState) : VState :=
  match s.env with
  | (_, .loc ℓ) :: env => ⟨env, s.store.set ℓ none⟩
  | (_, .view _) :: env => { s with env := env }
  | [] => s

end VState

end Stilt.Views
