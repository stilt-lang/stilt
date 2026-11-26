import Stilt.World

/-!
# Models of memory

What the evaluator of `Stilt.Semantics` needs from a model of memory, and the
two models that instantiate it:

* `Copy`, the reference interpreter's model: a body has its own frame of values, and a call
  passes an `inout` argument by copying the place's value in when the call
  starts and writing the callee's final value back when it returns or raises
  (values.inout-arguments and values.inout-argument-order);
* `InPlace`, in which a call passes an `inout` argument as a reference into the
  caller's variable, and the callee changes it where it is.

The two differ only in how calls treat `inout` arguments. `Stilt.Theorems`
states that they agree on exclusive programs. Both copy the value of a
variable's last use, as they copy any other value; `Stilt.Moves.Memory` adds
a third model that hands its storage over.

`Copy.memoryWith` is copy-in, copy-out with the order of write-back as a
parameter. With the Reference's's order it is `Copy.memory`, and
`Stilt.Optimality` uses the others only to show that its bound doesn't rest
on that order.
-/

namespace Stilt

/-- An argument once evaluated. An `inout` argument is the place it names,
with its indexes evaluated in its turn; the place itself is read only when the
call starts (values.index-reads). -/
inductive Passed where
  | value (v : Value)
  | place (root : Name) (path : Path)
  /-- A value argument that is the last use of the variable `root`: its value,
  and the variable whose storage a model may hand over to the parameter
  (values.consumed-parameters). -/
  | moved (root : Name) (v : Value)

/-- The value a value argument passes. -/
def Passed.value? : Passed → Option Value
  | .value v | .moved _ v => some v
  | .place _ _ => none

/-- The newest binding of each name that `keep` holds, the newest first. A lookup
reads the newest binding of a name, so these are the bindings a body that uses
those names reads, and what a closure literal captures (expressions.capture). -/
def newestOf {α : Type} (keep : Name → Bool) : List (Name × α) → List (Name × α)
  | [] => []
  | (x, a) :: scope =>
    if keep x then (x, a) :: newestOf (fun y => keep y && y != x) scope else newestOf keep scope

/-- Keeping the newest bindings commutes with any map that keeps names. -/
theorem newestOf_map {α β : Type} (f : α → β) : ∀ (keep : Name → Bool) (scope : List (Name × α)),
    newestOf keep (scope.map fun p => (p.1, f p.2)) = (newestOf keep scope).map fun p => (p.1, f p.2)
  | _, [] => rfl
  | keep, (x, a) :: scope => by
    by_cases h : keep x = true <;> simp [newestOf, h, newestOf_map f _ scope]

theorem mem_of_mem_newestOf {α : Type} {p : Name × α} :
    ∀ {keep : Name → Bool} {scope : List (Name × α)}, p ∈ newestOf keep scope → p ∈ scope
  | _, [], h => h
  | keep, (x, a) :: scope, h => by
    unfold newestOf at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_of_mem_newestOf h)
    · exact List.mem_cons_of_mem _ (mem_of_mem_newestOf h)

/-- A name that `keep` holds reads the same among the newest bindings. -/
theorem lookup_newestOf {α : Type} {z : Name} :
    ∀ {keep : Name → Bool} (scope : List (Name × α)), keep z = true →
      (newestOf keep scope).lookup z = scope.lookup z
  | _, [], _ => rfl
  | keep, (x, a) :: scope, hz => by
    by_cases hzx : z = x
    · subst hzx
      simp [newestOf, hz]
    · have hne : (z == x) = false := by simpa using hzx
      by_cases hx : keep x = true
      · simp only [newestOf, hx, ↓reduceIte, List.lookup_cons, hne]
        exact lookup_newestOf scope (by simp [hz, hzx])
      · simp only [newestOf, hx, Bool.false_eq_true, ↓reduceIte, List.lookup_cons, hne]
        exact lookup_newestOf scope hz

/-- What the evaluator needs from a model of the frames of memory: the
variables of the running body and how calls pass them. -/
structure Frames (σ : Type) where
  /-- Reads a place whose indexes have been evaluated. -/
  read : σ → Name → Path → Except Fault Value
  /-- Writes a place whose indexes have been evaluated. -/
  write : σ → Name → Path → Value → Except Fault σ
  /-- Binds a new variable, as `let`, `var`, a loop, an arm or a `catch` does. -/
  bind : σ → Name → Value → σ
  /-- Binds a new variable to the value of the last use of another, as `let`
  or `var` does when its initializer is one (values.passing-values). -/
  bindMoved : σ → Name → Name → Value → σ
  /-- Ends the scope of the newest binding. -/
  unbind : σ → σ
  /-- The newest binding of each variable in scope that `keep` holds, with its
  value, which a closure literal captures by copy (expressions.capture). -/
  capture : σ → (Name → Bool) → Except Fault (List (Name × Value))
  /-- Starts a call, once every argument is evaluated: from the caller's state,
  the callee's, with the closure's captured variables and each parameter bound
  to its argument (values.inout-argument-order). -/
  enter : σ → List (Name × Value) → List (Name × Passed) → Except Fault σ
  /-- Ends a call that returned or raised: from the caller's state and the
  callee's final one, the caller's (values.inout-arguments). -/
  leave : σ → σ → List (Name × Passed) → Except Fault σ

/-- What the evaluator needs from a model of memory: its frames, and the world
beside them (`Stilt.World`). -/
structure Memory (σ : Type) extends Frames σ where
  /-- The world of a state. -/
  world : σ → World
  /-- A state with its frames, in another world. -/
  setWorld : σ → World → σ
  /-- Runs `f` on a state's world: the value it gives, and the state with its frames in the
  world it leaves (std.io). -/
  inWorld : σ → (World → Except Fault (Value × World)) → Except Fault (Value × σ)

/-- A model of frames with the world beside them: reading, writing and binding
leave the world as it is, a call starts in its caller's world, and its caller
goes on in the world the call ended in. -/
def Frames.withWorld {σ : Type} (F : Frames σ) : Memory (σ × World) where
  read | (fr, _) => F.read fr
  write | (fr, w), x, path, v => (·, w) <$> F.write fr x path v
  bind | (fr, w), x, v => (F.bind fr x v, w)
  bindMoved | (fr, w), y, x, v => (F.bindMoved fr y x v, w)
  unbind | (fr, w) => (F.unbind fr, w)
  capture | (fr, _), keep => F.capture fr keep
  enter | (fr, w), captured, params => (·, w) <$> F.enter fr captured params
  leave | (fr, _), (fr', w'), params => (·, w') <$> F.leave fr fr' params
  world := Prod.snd
  setWorld | (fr, _), w => (fr, w)
  inWorld
    | (fr, w), f => match f w with
      | .ok (v, x) => .ok (v, (fr, x))
      | .error e => .error e

namespace Frames

variable {σ : Type} (F : Frames σ)

theorem map_ok {α β : Type} (f : α → β) (a : α) :
    (f <$> (Except.ok a : Except Fault α)) = .ok (f a) := rfl

theorem map_error {α β : Type} (f : α → β) (e : Fault) :
    (f <$> (Except.error e : Except Fault α)) = .error e := rfl

theorem withWorld_enter (s : σ × World) (captured : List (Name × Value))
    (params : List (Name × Passed)) :
    F.withWorld.enter s captured params = (·, s.2) <$> F.enter s.1 captured params := rfl

theorem withWorld_leave (s s' : σ × World) (params : List (Name × Passed)) :
    F.withWorld.leave s s' params = (·, s'.2) <$> F.leave s.1 s'.1 params := rfl

theorem withWorld_write (s : σ × World) (x : Name) (path : Path) (v : Value) :
    F.withWorld.write s x path v = (·, s.2) <$> F.write s.1 x path v := rfl

theorem withWorld_leave_ok {s s' t : σ × World} {params : List (Name × Passed)}
    (h : F.withWorld.leave s s' params = .ok t) :
    ∃ fr, F.leave s.1 s'.1 params = .ok fr ∧ t = (fr, s'.2) := by
  rw [withWorld_leave] at h
  cases hl : F.leave s.1 s'.1 params with
  | ok fr => rw [hl] at h; cases h; exact ⟨fr, rfl, rfl⟩
  | error e => rw [hl] at h; cases h

theorem withWorld_enter_ok {s t : σ × World} {captured : List (Name × Value)}
    {params : List (Name × Passed)} (h : F.withWorld.enter s captured params = .ok t) :
    ∃ fr, F.enter s.1 captured params = .ok fr ∧ t = (fr, s.2) := by
  rw [withWorld_enter] at h
  cases hl : F.enter s.1 captured params with
  | ok fr => rw [hl] at h; cases h; exact ⟨fr, rfl, rfl⟩
  | error e => rw [hl] at h; cases h

theorem withWorld_write_ok {s t : σ × World} {x : Name} {path : Path} {v : Value}
    (h : F.withWorld.write s x path v = .ok t) :
    ∃ fr, F.write s.1 x path v = .ok fr ∧ t = (fr, s.2) := by
  rw [withWorld_write] at h
  cases hl : F.write s.1 x path v with
  | ok fr => rw [hl] at h; cases h; exact ⟨fr, rfl, rfl⟩
  | error e => rw [hl] at h; cases h

theorem withWorld_foldl_bind (w : World) :
    ∀ (l : List (Name × Value)) (s : σ),
      l.foldl (fun s xv => F.withWorld.bind s xv.1 xv.2) (s, w) =
        (l.foldl (fun s xv => F.bind s xv.1 xv.2) s, w)
  | [], _ => rfl
  | _ :: l, _ => withWorld_foldl_bind w l _

end Frames

/-! ## Copy-in, copy-out -/

namespace Copy

/-- A body's variables and their values, the newest first. -/
abbrev Frame := List (Name × Value)

/-- Reads a place of the frame (values.independent-copies: the value read is a copy). -/
def read (fr : Frame) (x : Name) (path : Path) : Except Fault Value :=
  match fr.lookup x with
  | some v => v.get path
  | none => .error .stuck

/-- Writes a place of the frame (values.let-and-var and values.assignment-order). -/
def write (fr : Frame) (x : Name) (path : Path) (w : Value) : Except Fault Frame :=
  match fr.lookup x with
  | some v => (assocSet fr x ·) <$> v.set path w
  | none => .error .stuck

/-- The callee's frame: the captured variables, then each parameter bound to
a copy of its argument. An `inout` argument's place is read now, when the call
starts, from left to right (values.inout-argument-order). -/
def enter (caller captured : Frame) (params : List (Name × Passed)) : Except Fault Frame :=
  params.foldlM (init := captured) fun fr (y, a) =>
    match a with
    | .value v | .moved _ v => pure ((y, v) :: fr)
    | .place x path => (fun v => (y, v) :: fr) <$> read caller x path

/-- The caller's frame after the call, with each `inout` argument's place
given the final value of its parameter, from left to right, whether the
callee returned or raised (values.inout-arguments and values.inout-argument-order). -/
def leave (caller callee : Frame) (params : List (Name × Passed)) : Except Fault Frame :=
  params.foldlM (init := caller) fun fr (y, a) =>
    match a with
    | .value _ | .moved _ _ => pure fr
    | .place x path => do
      let v ← read callee y []
      write fr x path v

/-- The reference interpreter's model of frames. -/
def frames : Frames Frame where
  read := read
  write := write
  bind fr x v := (x, v) :: fr
  bindMoved fr y _ v := (y, v) :: fr
  unbind := List.tail
  capture fr keep := pure (newestOf keep fr)
  enter := enter
  leave := leave

/-- A state of the reference interpreter's model: a frame and the world. -/
abbrev State := Frame × World

/-- The reference interpreter's model of memory. -/
def memory : Memory State := frames.withWorld

end Copy

/-! ## The order of write-back -/

/-- An order in which copy-out writes a call's `inout` arguments back: for the
parameters a call binds, a permutation of them, which may depend on their
names and on the places they name. values.inout-argument-order gives left to right. -/
structure WriteBack where
  order : List (Name × Passed) → List (Name × Passed)
  perm : ∀ bound, (order bound).Perm bound

/-- The order of values.inout-argument-order: from left to right. -/
def WriteBack.leftToRight : WriteBack := ⟨id, List.Perm.refl⟩

/-- Copy-in, copy-out writing the `inout` arguments back in the order `w`
when a call ends. It is the reference interpreter's model but for that order. -/
def Copy.memoryWith (w : WriteBack) : Memory Copy.State :=
  Frames.withWorld
    { Copy.frames with
      leave := fun caller callee params => Copy.leave caller callee (w.order params) }

/-- With the order of values.inout-argument-order, it is the reference interpreter's model. -/
theorem Copy.memoryWith_leftToRight : Copy.memoryWith .leftToRight = Copy.memory := rfl

/-! ## In-place mutation -/

namespace InPlace

/-- A part of the store: a location, and a path within the value there. -/
structure Ref where
  loc : Nat
  path : Path

/-- Every variable refers to a part of the store. A variable of the body's
own refers to a location of its own; an `inout` parameter refers to the
caller's place. -/
structure State where
  env : List (Name × Ref)
  store : List Value

/-- Reads along a path from a part of the store. -/
def deref (s : State) (r : Ref) (path : Path) : Except Fault Value :=
  match s.store[r.loc]? with
  | some v => v.get (r.path ++ path)
  | none => .error .stuck

/-- Reads a place (values.independent-copies: the value read is a copy). -/
def read (s : State) (x : Name) (path : Path) : Except Fault Value :=
  match s.env.lookup x with
  | some r => deref s r path
  | none => .error .stuck

/-- Writes a place where it is (values.let-and-var and values.assignment-order). -/
def write (s : State) (x : Name) (path : Path) (w : Value) : Except Fault State :=
  match s.env.lookup x with
  | some r =>
    match s.store[r.loc]? with
    | some v => (fun v' => { s with store := s.store.set r.loc v' }) <$> v.set (r.path ++ path) w
    | none => .error .stuck
  | none => .error .stuck

/-- Binds a variable to a new location (values.let-and-var). -/
def bind (s : State) (x : Name) (v : Value) : State :=
  ⟨(x, ⟨s.store.length, []⟩) :: s.env, s.store ++ [v]⟩

/-- The callee's state: the captured variables and the `let` arguments in new
locations, and each `inout` parameter referring to its argument's place,
which must be readable when the call starts (values.index-reads). The callee
shares the caller's store. -/
def enter (caller : State) (captured : List (Name × Value))
    (params : List (Name × Passed)) : Except Fault State :=
  let base := captured.foldr (fun (x, v) s => bind s x v) ⟨[], caller.store⟩
  params.foldlM (init := base) fun s (y, a) =>
    match a with
    | .value v | .moved _ v => pure (bind s y v)
    | .place x path =>
      match caller.env.lookup x with
      | some r =>
        (fun _ => { s with env := (y, ⟨r.loc, r.path ++ path⟩) :: s.env }) <$>
          deref caller r path
      | none => .error .stuck

/-- In-place mutation: an `inout` argument is a reference to the caller's
place, so nothing is written back when the call ends. -/
def frames : Frames State where
  read := read
  write := write
  bind := bind
  bindMoved s y _ v := bind s y v
  unbind s := { s with env := s.env.tail }
  capture s keep := (newestOf keep s.env).mapM fun (x, r) => (x, ·) <$> deref s r []
  enter := enter
  leave caller callee _ := pure { caller with store := callee.store }

/-- In-place mutation, with the world beside the frames. -/
def memory : Memory (State × World) := frames.withWorld

end InPlace

end Stilt
