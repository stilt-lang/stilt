import Stilt.Modes.Escape

/-!
# Copies and what holds them

The state that `Stilt.Modes.Uniqueness` carries through the scope of a `var`
binding or an `inout` parameter `x` (modes.copies and modes.shared-writes).

A **copy** of `x` is a part of it that a value holds, and that a scope holds
until it ends: a binding, the statement or call whose value holds it, or the
rest of the function, depth `0`, when the holder escapes. Scopes nest, so a
scope is named by its depth.

A copy of a copy is a copy of `x`, held by whatever holds it (modes.copies). So the
analysis keeps, for each binding made in `x`'s scope, the parts of `x` its
value holds (`Alias`): binding, storing or capturing that value copies them
again. A value holds a part of `x` either as that part, so that a projection
of it reaches a part of the part, or inside, stored in a record, a tuple, a
list, a variant or a closure. Inside, the part is at a place of the value when
a field of a record or tuple literal, an element of a list literal or a part
assigned to holds it (modes.shared-writes): a projection to that place reaches
the part itself, one into it a part of the part, and one beside it no part of
`x` at all. A part at no known place may be in any part of the value.

The analysis follows the paths execution takes (modes.shared-writes): what it knows where a
`break`, a `continue`, or a raise or a performance that may leave the expression is taken goes
with the jump (`Pending`), and joins what it knows where the jump lands.
-/

namespace Stilt

/-- A part of `x` that a value holds: the part `sels`, whether the value is a
copy of it already (`copied`), whether the value holds it inside rather
than being it (`inside`), and the place inside the value where it is, if it
is one there (`place`), empty when the value is the part. -/
structure Part where
  sels : List Sel
  copied : Bool
  inside : Bool
  place : Option (List Sel)
  deriving DecidableEq, Repr

/-- `x` itself. -/
def Part.whole : Part := ⟨[], false, false, some []⟩

/-- The part that a value one step further holds, if it holds one: a part of
the part when the value is the part; the part, at the rest of its place, when
the step is toward that place, and no part when it leads beside it; and the
part, at no known place, when its place inside the value is unknown. -/
def Part.step (st : Sel) (p : Part) : Option Part :=
  match p.inside, p.place with
  | true, some (s :: rest) =>
    if s == st then some { p with inside := !rest.isEmpty, place := some rest } else none
  | true, none => some p
  | _, place => some { p with sels := p.sels ++ [st], inside := false, place }

/-- The part as a part of the value at no known place holds it: a variant's
payload, or the rest of a list pattern. -/
def Part.unplaced (p : Part) : Part := { p with inside := true, place := none }

/-- The parts that a value one step further holds, by `step`, or at no known
place when the step has no `Sel`. -/
def Part.into : Option Sel → List Part → List Part
  | some st, parts => parts.filterMap (Part.step st)
  | none, parts => parts.map Part.unplaced

/-- The part as a copy that may be any part of `x`, where the analysis no longer knows which:
held before an assignment of the whole of `x` whose value holds a part of `x`'s own value, or
by a binding at the head of a loop (modes.shared-writes). A part inside a value is no longer at
a known place in it. -/
def Part.widen (p : Part) : Part :=
  { p with sels := [.any], place := if p.inside then none else p.place }

/-- The part as a binding holds it: a copy. -/
def Part.bound (p : Part) : Part := { p with copied := true }

/-- The part as a value stores it: a copy, inside, at the place `step` leads
to, if the value has one there. -/
def Part.stored (step : Option Sel := none) (p : Part) : Part :=
  { p with copied := true, inside := true, place := step.bind fun st => p.place.map (st :: ·) }

mutual

/-- The parts of `x` that the binder `b` of a pattern holds, of a matched
value that holds `parts`: those at the place of the value that `b` matches,
each a copy (modes.copies). A tuple's elements are its fields by position, a
list's are its elements, and a variant's payload and a list's rest are at no
known place. -/
def Pattern.partsAt (b : Name) (parts : List Part) : Pattern → List Part
  | .wild | .int _ | .bool _ | .str _ | .unit => []
  | .bind y => if y == b then parts.map Part.bound else []
  | .tuple ps => patternsPartsAt b parts (fun n => some (.field (tupleField n))) 0 ps
  | .record _ fields => fieldPatternsPartsAt b parts fields
  | .variant _ _ ps => patternsPartsAt b parts (fun _ => none) 0 ps
  | .or p q => p.partsAt b parts ++ q.partsAt b parts
  | .list ps r => patternsPartsAt b parts (fun _ => some .elem) 0 ps ++
      if r.binders.contains b then (Part.into none parts).map Part.bound else []

/-- The parts the binder `b` holds through the patterns `ps`, from the one at
position `n`, each matching the part of the value that `step` leads to. -/
def patternsPartsAt (b : Name) (parts : List Part) (step : Nat → Option Sel) (n : Nat) :
    List Pattern → List Part
  | [] => []
  | p :: ps => p.partsAt b (Part.into (step n) parts) ++ patternsPartsAt b parts step (n + 1) ps

/-- The parts the binder `b` holds through the field patterns of a record
pattern. -/
def fieldPatternsPartsAt (b : Name) (parts : List Part) : List (Name × Pattern) → List Part
  | [] => []
  | (f, p) :: fields =>
    p.partsAt b (Part.into (some (.field f)) parts) ++ fieldPatternsPartsAt b parts fields

end

/-- A copy of a part of `x`, with the shape of that part, held by the scope at
depth `holder`. -/
structure Held where
  holder : Nat
  shape : List Name
  deriving DecidableEq, Repr

/-- A binding made in `x`'s scope, in the scope at depth `depth`, and the parts
of `x` its value holds. A binding that holds none still hides any other of its
name. -/
structure Alias where
  name : Name
  depth : Nat
  parts : List Part
  deriving DecidableEq, Repr

/-- Where a jump goes: out of the innermost loop around it, to that loop's next turn, or out of
the expression, to the innermost `catch` or `with` around it, by a raise or by a performance
whose handler doesn't resume. -/
inductive Leave where
  | brk
  | cont
  | esc
  deriving DecidableEq, Repr

/-- What the analysis knows where a jump is taken: the copies that may still last, and the
parts of `x` that the bindings in scope hold. -/
structure Pending where
  leave : Leave
  live : List Held
  aliases : List Alias

/-- What the analysis knows at a point of `x`'s scope: the copies that may
still last, every copy made, whether a shared write was found, the parts
of `x` that the bindings in scope hold, the other bindings found shared
because their value is a copy of a part of `x` that is read again, and what it knew at the
jumps taken since that haven't landed yet. -/
structure Copies where
  live : List Held
  made : List (List Name)
  shared : Bool
  aliases : List Alias
  mirrored : List Name
  pending : List Pending

namespace Copies

/-- The depth of the binding `y` in scope: `0` for one made outside `x`'s
scope. -/
def depthOf (s : Copies) (y : Name) : Nat :=
  ((s.aliases.find? (·.name == y)).map (·.depth)).getD 0

/-- The parts of `x` that the binding `y` in scope holds, from every branch
that gave it a value. -/
def partsOf (s : Copies) (y : Name) : List Part :=
  (s.aliases.filter fun a => a.name == y && a.depth == s.depthOf y).flatMap (·.parts)

/-- The binding `y`, at depth `k`, now holds these parts too. -/
def give (s : Copies) (y : Name) (k : Nat) (parts : List Part) : Copies :=
  { s with aliases := ⟨y, k, parts⟩ :: s.aliases }

/-- An assignment to the place `path` of the binding `y`, at depth `k`,
replaces the parts its value held there: they are no longer at a place of
it. -/
def replaceAt (s : Copies) (y : Name) (k : Nat) (path : List Sel) : Copies :=
  { s with aliases := s.aliases.map fun a =>
      if a.name == y && a.depth == k then
        { a with parts := a.parts.map fun p =>
            if p.place.any (path.isPrefixOf ·) then { p with place := none } else p }
      else a }

/-- The names of the bindings that may hold parts of `x`. -/
def holders (s : Copies) : List Name := (s.aliases.map (·.name)).eraseDups

/-- The copies, and the bindings, that end with the scope at depth `d`, here and at the jumps
taken inside it, which leave it too. -/
def close (s : Copies) (d : Nat) : Copies :=
  { s with live := s.live.filter (·.holder < d), aliases := s.aliases.filter (·.depth < d),
           pending := s.pending.map fun j =>
             { j with live := j.live.filter (·.holder < d), aliases := j.aliases.filter (·.depth < d) } }

/-- Two states of alternative branches, joined: what may last after either. -/
def join (a b : Copies) : Copies :=
  ⟨a.live ++ b.live, a.made ++ b.made, a.shared || b.shared, a.aliases ++ b.aliases,
    a.mirrored ++ b.mirrored, a.pending ++ b.pending⟩

/-- A jump taken here: what the analysis knows goes with it. -/
def leave (k : Leave) (s : Copies) : Copies :=
  { s with pending := ⟨k, s.live, s.aliases⟩ :: s.pending }

/-- The jumps of kind `k` land here: what the analysis knew where each was taken joins what it
knows. -/
def land (k : Leave) (s : Copies) : Copies :=
  let hit := s.pending.filter (·.leave == k)
  { s with live := s.live ++ hit.flatMap (·.live), aliases := s.aliases ++ hit.flatMap (·.aliases),
           pending := s.pending.filter (·.leave != k) }

/-- The jumps of kind `k` land here, and go on beyond too. -/
def meet (k : Leave) (s : Copies) : Copies :=
  { s.land k with pending := s.pending }

/-- The whole of `x` is assigned: no copy made before shares its new value
(modes.shared-writes), and no binding holds a part of it. -/
def replace (s : Copies) : Copies :=
  { s with live := [], aliases := s.aliases.map fun a => { a with parts := [] } }

/-- The whole of `x` is assigned a value that holds a part of `x`'s own value: the
assignment is no assignment of the whole for the rule, and each copy made before it, or held
by a binding before it, counts as a copy of every part of `x` (modes.shared-writes). -/
def reshape (s : Copies) : Copies :=
  { s with live := s.live.map fun c => { c with shape := [] },
           aliases := s.aliases.map fun a => { a with parts := a.parts.map Part.widen } }

end Copies

/-- What the analysis is about: the binding `x` of type `τ`, the program's
declarations and consumption, the `inout` parameters in scope, the shapes
copied in the bodies of the loops around the current point, the depth of
the scope that holds what is stored in each binding made inside `x`'s
scope, and whether a `catch` or a `with` around the current point may take a raise or a
performance that leaves it. -/
structure Writes where
  decls : Decls
  consumed : Consumed
  inouts : List Name
  x : Name
  τ : Ty
  loop : List (List Name)
  scopes : List (Name × Nat)
  catching : Bool

namespace Writes

/-- The part `p` of `x` is copied, held by the scope at depth `h`, if its type
is copy-on-write (modes.copies). -/
def hold (W : Writes) (h : Nat) (s : Copies) (p : Part) : Copies :=
  if W.decls.cowPart W.τ p.sels then
    { s with live := ⟨h, Sel.shape p.sels⟩ :: s.live, made := Sel.shape p.sels :: s.made }
  else s

/-- Each of these parts is copied, held by the scope at depth `h`. -/
def holdAll (W : Writes) (h : Nat) (s : Copies) (parts : List Part) : Copies :=
  parts.foldl (W.hold h) s

/-- A modification of the part of `x` with these fields: shared when a copy of
an overlapping part lasts, or when a loop around it copies one (modes.shared-writes; modes.overlap). -/
def modify (W : Writes) (s : Copies) (fields : List Name) : Copies :=
  let hit := fun c : List Name => c.isPrefixOf fields || fields.isPrefixOf c
  { s with shared := s.shared || s.live.any (hit ·.shape) || W.loop.any hit }

/-- A modification of the place `path` of a binding `z` other than `x`,
which `replaces` says assigns the place: shared when it reaches inside a
copy of a part of `x` that `z` holds, as its value or at a place inside it,
while `x`, or another binding holding a copy of an overlapping part, is used
after it, as `later` says (modes.shared-writes). An assignment replaces a copy
at its own place rather than writing inside it. -/
def mirror (W : Writes) (later : Name → Bool) (s : Copies) (z : Name) (path : List Sel)
    (replaces : Bool) : Copies :=
  let hit := fun (c f : List Name) => c.isPrefixOf f || f.isPrefixOf c
  let inside := fun (place : List Sel) =>
    place.isPrefixOf path && !(replaces && path.length ≤ place.length)
  let reached := ((s.partsOf z).filter fun p => p.copied && p.place.any inside).map fun p =>
    Sel.shape (p.sels ++ path.drop ((p.place.map List.length).getD 0))
  let other := s.holders.any fun w => w != z && later w &&
    (s.partsOf w).any fun q => reached.any (hit (Sel.shape q.sels))
  if z != W.x && !reached.isEmpty && (later W.x || other) then
    { s with mirrored := z :: s.mirrored }
  else s

/-- An assignment to a place of `x`: of the whole binding, which replaces its
value, or a modification of a part (modes.shared-writes). -/
def assign (W : Writes) (s : Copies) (path : List Projection) : Copies :=
  if path.isEmpty then s.replace else W.modify s (path.filterMap Projection.fieldName?)

/-- The depth of the scope that holds what is stored in the binding `y`: its
own, or the rest of the function if `y` was bound outside `x`'s scope. -/
def holderOf (W : Writes) (y : Name) : Nat := (W.scopes.lookup y).getD 0

/-- The depth of the scope that holds what a binding `y` made at depth `k`
holds, whose scope is `body`: the rest of the function when `y` escapes there
(modes.copies). -/
def scopeOf (W : Writes) (k h : Nat) (y : Name) (τ : Ty) (body : Expr) : Nat :=
  if localityOf W.decls W.consumed W.inouts y τ (if h == 0 then some [] else none) body == .escapes
  then 0 else k

/-- `W` inside the scope of a binding `y` whose copies the scope at depth `hy`
holds. -/
def enter (W : Writes) (y : Name) (hy : Nat) : Writes :=
  { W with scopes := (y, hy) :: W.scopes, inouts := W.inouts.filter (· != y) }

/-- An assignment of a value holding `parts` to the binding `y`, other than
`x`: a copy held by `y`'s scope, of a whole local or stored in a value
(modes.escaping and modes.copies), and `y` holds the parts, inside unless the
assignment is to the whole of it. -/
def assignTo (W : Writes) (s : Copies) (y : Name) (path : List Projection) (parts : List Part) :
    Copies :=
  let s := W.holdAll (W.holderOf y) s parts
  let sels := path.map Projection.sel
  (s.replaceAt y (s.depthOf y) sels).give y (s.depthOf y) (parts.map fun p =>
    if path.isEmpty then p.bound else { p.stored with place := p.place.map (sels ++ ·) })

/-- What a closure literal with parameters `ps` and body `body` captures of
`x`: `x` itself, and the parts that the bindings it captures hold (expressions.capture; modes.copies). -/
def captured (W : Writes) (s : Copies) (ps : List Param) (body : Expr) : List Part :=
  (if !hides ps W.x && body.occurs W.x then [Part.whole] else []) ++
    (s.holders.filter fun y => !hides ps y && body.occurs y).flatMap s.partsOf

end Writes

end Stilt
