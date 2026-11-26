import Stilt.Semantics
import Stilt.Places
import Stilt.Sources

/-!
# Windows

A fourth model of memory, `Windows`, in which a view is a window into its source's storage and
holds no copy of the part it reads (views.what-view-is). It is the in-place model of
`Stilt.Memory`, a store of locations and variables that refer to parts of it, but for two
things:

* the end of a binding's scope frees the binding's location, so a window that outlives its
  source reads freed storage and is stuck (views.escaping, expressions.scope);
* a view is a window, `Value.window`, which reads its source's part each time it is read, so a
  change to the source shows through it (views.change-while-viewed).

A place whose path goes through a window reads, and is written in, what the window reads
(`getW`, `setW`). Reading through a window replaces it with the part it reads (`resolve`): an operation does it
to its operands, as do `copy`, indexing, a `for` and a `match`, and so does a value that leaves
the frames it was made in, for a handler's body or a cell. Reading a variable through the
memory does it too, so a cell holds what its name's window reads. `Stilt.Windows.Eval` makes
the windows.
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

/-- Every variable refers to a part of the store, as in the in-place model. A freed location
holds nothing. -/
structure State where
  env : List (Name × Ref)
  store : List (Option Value)

/-- The value at a location of the store, if it holds one. -/
def cell (st : List (Option Value)) (loc : Nat) : Except Fault Value :=
  match st[loc]? with
  | some (some v) => .ok v
  | _ => .error .stuck

/-- The part a window reads: its source's part at its path, sliced by each of its ranges in
turn as `View.of` and `view` slice, with the panics of `slice` (views.what-view-is and
views.making-view). -/
def part (st : List (Option Value)) (loc : Nat) (path : Path) (ranges : List (Int × Int)) :
    Except Fault Value := do
  let v ← (← cell st loc).get path
  ranges.foldlM (fun v r => Op.view.apply [v, .int r.1, .int r.2]) v

mutual

/-- A value with each window in it replaced by what `f` gives for the window. -/
def mapWindows (f : Nat → Path → List (Int × Int) → Except Fault Value) :
    Value → Except Fault Value
  | .window loc path ranges => f loc path ranges
  | .list vs => .list <$> mapWindowsValues f vs
  | .record R fields => .record R <$> mapWindowsFields f fields
  | .variant T C vs => .variant T C <$> mapWindowsValues f vs
  | v => .ok v

/-- Values, each with its windows replaced. -/
def mapWindowsValues (f : Nat → Path → List (Int × Int) → Except Fault Value) :
    List Value → Except Fault (List Value)
  | [] => .ok []
  | v :: vs => do
    let w ← mapWindows f v
    let ws ← mapWindowsValues f vs
    pure (w :: ws)

/-- Named values, each with its windows replaced. -/
def mapWindowsFields (f : Nat → Path → List (Int × Int) → Except Fault Value) :
    List (Name × Value) → Except Fault (List (Name × Value))
  | [] => .ok []
  | (x, v) :: fields => do
    let w ← mapWindows f v
    let ws ← mapWindowsFields f fields
    pure ((x, w) :: ws)

end

/-- A value with each window in it replaced by the part it reads, read through its own windows
in turn, at most `depth` deep. A source holds no view (views.view-types), so one step reads
every window of a well-typed program. -/
def resolveAt (st : List (Option Value)) : Nat → Value → Except Fault Value
  | 0 => mapWindows fun _ _ _ => .error .stuck
  | n + 1 => mapWindows fun loc path ranges => do resolveAt st n (← part st loc path ranges)

/-- A value read through its windows: a window, through any number of sources, each a
location of the store. -/
def resolve (st : List (Option Value)) (v : Value) : Except Fault Value :=
  resolveAt st (st.length + 1) v

/-- Reads along a path from a value, through each window it meets before the path's end: a
part of a view is a part of what the view reads (views.what-view-is). -/
def getW (st : List (Option Value)) : Value → Path → Except Fault Value
  | v, [] => .ok v
  | .window loc path ranges, p => do (← part st loc path ranges).get p
  | .record _ fields, .field f :: p =>
    match fields.lookup f with
    | some v => getW st v p
    | none => .error .stuck
  | .list vs, .index i :: p =>
    match elemAt? vs i with
    | some v => getW st v p
    | none => .error (.panic .bounds)
  | _, _ :: _ => .error .stuck

/-- A value with its part at a path replaced, as `Value.set` replaces it, a window met
before the path's end replaced first by what it reads. -/
def setW (st : List (Option Value)) : Value → Path → Value → Except Fault Value
  | _, [], w => .ok w
  | .window loc path ranges, p, w => do (← part st loc path ranges).set p w
  | .record R fields, .field f :: p, w =>
    match fields.lookup f with
    | some v => (fun v' => .record R (assocSet fields f v')) <$> setW st v p w
    | none => .error .stuck
  | .list vs, .index i :: p, w =>
    match elemAt? vs i with
    | some v => (fun v' => .list (vs.set i.toNat v')) <$> setW st v p w
    | none => .error (.panic .bounds)
  | _, _ :: _, _ => .error .stuck

/-- Reads along a path from a part of the store, a window at the path's end as it is. -/
def deref (s : State) (r : Ref) (path : Path) : Except Fault Value := do
  getW s.store (← cell s.store r.loc) (r.path ++ path)

/-- Reads a place, windows as they are: the value of a view's variable is its window. -/
def readWindows (s : State) (x : Name) (path : Path) : Except Fault Value :=
  match s.env.lookup x with
  | some r => deref s r path
  | none => .error .stuck

/-- Reads a place through its windows (values.independent-copies: the value read is a copy). -/
def read (s : State) (x : Name) (path : Path) : Except Fault Value := do
  resolve s.store (← readWindows s x path)

/-- Writes a place where it is (values.let-and-var and values.assignment-order). -/
def write (s : State) (x : Name) (path : Path) (w : Value) : Except Fault State :=
  match s.env.lookup x with
  | some r =>
    match s.store[r.loc]? with
    | some (some v) =>
      (fun v' => { s with store := s.store.set r.loc (some v') }) <$>
        setW s.store v (r.path ++ path) w
    | _ => .error .stuck
  | none => .error .stuck

/-- Binds a variable to a new location (values.let-and-var). -/
def bind (s : State) (x : Name) (v : Value) : State :=
  ⟨(x, ⟨s.store.length, []⟩) :: s.env, s.store ++ [some v]⟩

/-- Ends the scope of the newest binding and frees its location (expressions.scope). -/
def unbind (s : State) : State :=
  match s.env with
  | (_, r) :: env => ⟨env, s.store.set r.loc none⟩
  | [] => s

/-- The callee's state, as in the in-place model: the captured variables and the `let`
arguments in new locations, a view's window among them, and each `inout` parameter referring to
its argument's place, whose location's views are read first: a callee changes no view's
source in place, so an `inout` argument holds what its views read. -/
def enter (caller : State) (captured : List (Name × Value))
    (params : List (Name × Passed)) : Except Fault State :=
  let base := captured.foldr (fun (x, v) s => bind s x v) ⟨[], caller.store⟩
  params.foldlM (init := base) fun s (y, a) =>
    match a with
    | .value v | .moved _ v => pure (bind s y v)
    | .place x path =>
      match caller.env.lookup x with
      | some r => do
        let _ ← deref { caller with store := s.store } r path
        let c ← resolve s.store (← cell s.store r.loc)
        pure ⟨(y, ⟨r.loc, r.path ++ path⟩) :: s.env, s.store.set r.loc (some c)⟩
      | none => .error .stuck

/-- The frames of windows: in place, with a location freed at its binding's end. A closure
captures what its variables' windows read (expressions.capture). -/
def frames : Frames State where
  read := read
  write := write
  bind := bind
  bindMoved s y _ v := bind s y v
  unbind := unbind
  capture s keep :=
    (newestOf keep s.env).mapM fun (x, r) => (x, ·) <$> (deref s r [] >>= resolve s.store)
  enter := enter
  leave caller callee _ := pure { caller with store := callee.store }

/-- The model of windows, with the world beside the frames. -/
def memory : Memory (State × World) := frames.withWorld

end Windows

end Stilt
