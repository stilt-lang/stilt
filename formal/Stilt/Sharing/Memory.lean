import Stilt.Semantics
import Stilt.Places

/-!
# Sharing

A further model of memory, `Sharing`, in which a copy of a binding, or of a part of one, into
another binding shares the storage it copies, and a write copies first only where the
inference of modes.shared-writes says the binding is shared. It is the in-place model of
`Stilt.Memory`, a store of locations and variables that refer to parts of it, with these
differences:

* A `let` or `var` whose initializer is a place of a binding (a variable followed by fields,
  and by indexes that are integers or variables), at a copy-on-write type
  (modes.copy-on-write-types), refers to that place instead of a location of its own: the
  copy of modes.copies shares the storage. So does an assignment of such a place to the whole
  of a local. Every other copy, into a literal, a capture or an argument, copies, as in the
  in-place model.
* Each binding has a part of the store of its own all the same, its home: a new location, or,
  for an `inout` parameter, the place its argument names.
* A modification of a binding that the inference calls `unique` writes where the binding
  refers. One it calls `shared` first gives the binding a copy of its own, in a new location,
  when it refers to another's storage, and otherwise gives every other binding of the frame that
  refers into its home a copy of its own (`unshare`): that is the copy a shared write makes
  (facts.copy).
* An assignment of the whole of a binding replaces its value and copies nothing
  (modes.shared-writes): the bindings that refer into its home keep what they read, each in a
  new location.

`Stilt.Sharing.Eval` gives each binding the inference's verdict, by its name.
-/

namespace Stilt

namespace Sharing

open InPlace (Ref)

/-- Whether two parts of the store overlap: one holds the other. -/
def overlaps (a b : Ref) : Bool :=
  a.loc == b.loc && (a.path.isPrefixOf b.path || b.path.isPrefixOf a.path)

/-- A binding of a frame: its home, the part it refers to when that isn't its home, whether
the inference calls its modifications `unique` (modes.shared-writes), whether its type is a
copy-on-write type, whose copies share storage (modes.copy-on-write-types), and whether it is
an `inout` parameter, whose home is its argument's place. -/
structure Entry where
  home : Ref
  alias : Option Ref
  unique : Bool
  cow : Bool
  inout : Bool

/-- The part of the store a binding refers to. -/
def Entry.ref (e : Entry) : Ref := e.alias.getD e.home

/-- Every variable refers to a part of the store, as in the in-place model. The store is an
array, which a run grows and writes in place. -/
structure State where
  env : List (Name × Entry)
  store : Array Value

/-- Reads along a path from a part of the store. -/
def deref (s : State) (r : Ref) (path : Path) : Except Fault Value :=
  match s.store[r.loc]? with
  | some v => v.get (r.path ++ path)
  | none => .error .stuck

/-- Writes along a path into a part of the store. -/
def setAt (s : State) (r : Ref) (path : Path) (w : Value) : Except Fault State :=
  match s.store[r.loc]? with
  | some v => (fun v' => { s with store := s.store.set! r.loc v' }) <$> v.set (r.path ++ path) w
  | none => .error .stuck

/-- Reads a place (values.independent-copies: the value read is a copy). -/
def read (s : State) (x : Name) (path : Path) : Except Fault Value :=
  match s.env.lookup x with
  | some e => deref s e.ref path
  | none => .error .stuck

/-- Reads the bindings `env`, each where it refers: what a closure literal captures
(expressions.capture). -/
def readCaptured (s : State) (env : List (Name × Entry)) : Except Fault (List (Name × Value)) :=
  env.mapM fun (x, e) => (x, ·) <$> deref s e.ref []

/-- Writes a place where its binding refers. -/
def write (s : State) (x : Name) (path : Path) (w : Value) : Except Fault State :=
  match s.env.lookup x with
  | some e => setAt s e.ref path w
  | none => .error .stuck

/-- Binds a variable to a new location holding `v`, its home. -/
def bindWith (s : State) (x : Name) (v : Value) (unique cow : Bool) : State :=
  ⟨(x, ⟨⟨s.store.size, []⟩, none, unique, cow, false⟩) :: s.env, s.store.push v⟩

/-- Binds a variable that no modification reaches through the inference: a `for`'s, an
arm's, a `catch`'s and a `when`'s, each of its own value, never shared into. -/
def bind (s : State) (x : Name) (v : Value) : State := bindWith s x v false false

/-- Binds a variable to the part `r` that its initializer, a place, names: it shares that
part's storage, and has a home all the same (modes.copies). -/
def bindAlias (s : State) (x : Name) (v : Value) (r : Ref) (unique : Bool) : State :=
  ⟨(x, ⟨⟨s.store.size, []⟩, some r, unique, true, false⟩) :: s.env, s.store.push v⟩

/-- A binding that refers to another's storage given a copy of what it refers to, in a new
location, its home from then on. -/
def settle (s : State) (e : Entry) : Except Fault (State × Entry) :=
  match e.alias with
  | none => .ok (s, e)
  | some r => do
    let v ← deref s r []
    pure ({ s with store := s.store.push v },
      { e with home := ⟨s.store.size, []⟩, alias := none })

/-- Gives each binding of `env`, from position `i`, but the one at `skip`, that refers into
`region` a copy of its own. -/
def evacuate (region : Ref) (skip : Nat) :
    Nat → State → List (Name × Entry) → Except Fault (State × List (Name × Entry))
  | _, s, [] => .ok (s, [])
  | i, s, (y, e) :: rest => do
    let (s, e) ← if i != skip && e.alias.any (overlaps region) then settle s e else pure (s, e)
    let (s, rest) ← evacuate region skip (i + 1) s rest
    pure (s, (y, e) :: rest)

/-- The binding `x` stops sharing: it gets a copy of its own when it refers to another's
storage, and otherwise every other binding of the frame that refers into its home gets one
(facts.copy). -/
def unshare (s : State) (x : Name) : Except Fault State :=
  match s.env.findIdx? (·.1 == x), s.env.lookup x with
  | some i, some e =>
    match e.alias with
    | some _ => do
      let (s, e) ← settle s e
      pure { s with env := s.env.set i (x, e) }
    | none => do
      let (s, env) ← evacuate e.home i 0 s s.env
      pure { s with env }
  | _, _ => .error .stuck

/-- A modification of the place `x` and `path` (modes.kinds-of-access): in place where `x`
refers when the inference calls it `unique`, and in a copy of its own otherwise
(modes.shared-writes). -/
def modify (s : State) (x : Name) (path : Path) (w : Value) : Except Fault State :=
  match s.env.lookup x with
  | some e => if e.unique then setAt s e.ref path w else do
    let s ← unshare s x
    write s x path w
  | none => .error .stuck

/-- An assignment of `w` to the whole of `x`, whose value is the place `r` when `alias? = some
r`: a local of a copy-on-write type comes to share that place's storage (modes.copies); any
other value goes in `x`'s home, after the bindings that refer into it get copies of their own,
since the assignment replaces `x`'s value and copies nothing (modes.shared-writes). -/
def assignWhole (s : State) (x : Name) (w : Value) (alias? : Option Ref) :
    Except Fault State :=
  match s.env.findIdx? (·.1 == x), s.env.lookup x with
  | some i, some e =>
    match alias? with
    | some r =>
      if e.cow && !e.inout then .ok { s with env := s.env.set i (x, { e with alias := some r }) }
      else replace i e
    | none => replace i e
  | _, _ => .error .stuck
where
  replace (i : Nat) (e : Entry) : Except Fault State := do
    let (s, env) ← evacuate e.home i 0 s s.env
    setAt { s with env := env.set i (x, { e with alias := none }) } e.home [] w

/-- The callee's state: the captured variables and the `let` arguments in new locations, and
each `inout` parameter with its argument's place as its home, `unique` unless `shared` names it
(modes.shared-writes). The callee shares the caller's store. -/
def enter (shared : Name → Bool) (caller : State) (captured : List (Name × Value))
    (params : List (Name × Passed)) : Except Fault State :=
  let base := captured.foldr (fun (x, v) s => bind s x v) ⟨[], caller.store⟩
  params.foldlM (init := base) fun s (y, a) =>
    match a with
    | .value v | .moved _ v => pure (bind s y v)
    | .place x path =>
      match caller.env.lookup x with
      | some e =>
        (fun _ => { s with env := (y, ⟨⟨e.ref.loc, e.ref.path ++ path⟩, none,
          !shared y, true, true⟩) :: s.env }) <$> deref caller e.ref path
      | none => .error .stuck

/-- The frames of sharing, where the bindings that `shared` names are `shared`. -/
def frames (shared : Name → Bool) : Frames State where
  read := read
  write := write
  bind := bind
  bindMoved s y _ v := bind s y v
  unbind s := { s with env := s.env.tail }
  capture s keep := readCaptured s (newestOf keep s.env)
  enter := enter shared
  leave caller callee _ := pure { caller with store := callee.store }

/-- The model of sharing, with the world beside the frames, where the bindings that `shared`
names are `shared`. -/
def memory (shared : Name → Bool) : Memory (State × World) := (frames shared).withWorld

/-- The integer an index is, when it is one or a variable's, which reading changes nothing. -/
def pureIndex (s : State) : Expr → Option Int
  | .int k => some k
  | .var z => match read s z [] with
    | .ok (.int k) => some k
    | _ => none
  | _ => none

/-- The path of a place's projections, when every index is a `pureIndex`. -/
def pathOf (s : State) : List Projection → Option Path
  | [] => some []
  | .field f :: ps => (.field f :: ·) <$> pathOf s ps
  | .index i :: ps => do
    let k ← pureIndex s i
    (.index k :: ·) <$> pathOf s ps

/-- The part of the store that an expression names, when it is a place whose indexes are
integers or variables. -/
def aliasRef? (s : State) (e : Expr) : Option Ref := do
  let ⟨x, projections⟩ ← e.place?
  let entry ← s.env.lookup x
  let path ← pathOf s projections
  pure ⟨entry.ref.loc, entry.ref.path ++ path⟩

end Sharing

end Stilt
