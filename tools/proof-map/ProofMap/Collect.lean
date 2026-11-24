import ProofMap.Graph

/-!
# Collecting the written declarations

Every written declaration of the model, with the written declarations its statement and
its proof use, read through the declarations the elaborator made, and the axioms it rests
on. A constructor stands for its type, and a field's projection for its structure, so
the map shows `Expr` where a proof matches on `Expr.call`.
-/

open Lean

namespace ProofMap

/-- What a walk remembers: the written declarations a made one reaches, and the axioms a
declaration rests on, each kept once it is whole; and the declarations each walk is inside,
at their depth. A declaration on a cycle, as a type of a mutual block is through its
constructors, is whole only when the walk leaves the outermost declaration of the cycle that
it entered, so a walk that comes back to one it is inside keeps nothing below it. -/
structure Memo where
  reach : Std.HashMap Name NameSet := {}
  axioms : Std.HashMap Name NameSet := {}
  inReach : Std.HashMap Name Nat := {}
  inAxioms : Std.HashMap Name Nat := {}

abbrev M := ReaderT Environment (StateM Memo)

/-- The declaration that a reference to `n` stands for on the map: the type of a
constructor, the structure of a projection, else `n`. -/
def standFor (env : Environment) (n : Name) : Name :=
  match env.find? n with
  | some (.ctorInfo c) => c.induct
  | _ => match env.getProjectionFnInfo? n with
    | some p => match env.find? p.ctorName with
      | some (.ctorInfo c) => c.induct
      | _ => n
    | none => n

/-- Whether `n` is written: a declaration of the model with a source range of its own that
stands for itself. -/
def written (env : Environment) (ranged : NameSet) (n : Name) : Bool :=
  inModel env n && ranged.contains n && standFor env n == n

/-- What a declaration names: its type, its value, and for a type its constructors' types. -/
def uses (env : Environment) (ci : ConstantInfo) : Array Name :=
  let own := used ci.type ++ ((ci.value? (allowOpaque := true)).map used |>.getD #[])
  match ci with
  | .inductInfo i => i.ctors.foldl (fun acc c =>
      acc ++ ((env.find? c).map (used ·.type) |>.getD #[])) own
  | _ => own

/-- The written declarations that a reference to `n` reaches, walked `depth` declarations
deep, and the depth of the shallowest declaration the walk is inside that it came back to,
past `depth` when none: the result is whole, and kept, when that is not above `n`. -/
partial def reachAt (ranged : NameSet) (n : Name) (depth : Nat) : M (NameSet × Nat) := do
  let env ← read
  let n' := standFor env n
  if written env ranged n' then return (NameSet.empty.insert n', depth + 1)
  if !inModel env n then return ({}, depth + 1)
  if let some s := (← get).reach[n]? then return (s, depth + 1)
  if let some d := (← get).inReach[n]? then return ({}, d)
  let some ci := env.find? n | return ({}, depth + 1)
  modify fun m => { m with inReach := m.inReach.insert n depth }
  let mut acc : NameSet := {}
  let mut low := depth + 1
  for u in uses env ci do
    let (xs, l) ← reachAt ranged u (depth + 1)
    for x in xs do acc := acc.insert x
    low := min low l
  modify fun m => { m with inReach := m.inReach.erase n }
  if low ≥ depth then modify fun m => { m with reach := m.reach.insert n acc }
  return (acc, low)

/-- The written declarations that a reference to `n` reaches. -/
def reach (ranged : NameSet) (n : Name) : M NameSet :=
  Prod.fst <$> reachAt ranged n 0

/-- The written declarations that the references in `names` reach, but `self`. -/
def reachAll (ranged : NameSet) (self : Name) (names : Array Name) : M (Array Name) := do
  let mut acc : NameSet := {}
  for u in names do
    for x in (← reach ranged u) do
      if x != self then acc := acc.insert x
  return acc.toArray.qsort Name.lt

/-- The axioms `n` rests on, through every constant it names, walked `depth` constants deep,
and the depth of the shallowest constant the walk is inside that it came back to, as
`reachAt` gives. -/
partial def axiomsAt (n : Name) (depth : Nat) : M (NameSet × Nat) := do
  if let some s := (← get).axioms[n]? then return (s, depth + 1)
  if let some d := (← get).inAxioms[n]? then return ({}, d)
  let env ← read
  let some ci := env.find? n | return ({}, depth + 1)
  modify fun m => { m with inAxioms := m.inAxioms.insert n depth }
  let mut acc : NameSet := {}
  if ci matches .axiomInfo _ then acc := acc.insert n
  let mut low := depth + 1
  for u in uses env ci do
    let (xs, l) ← axiomsAt u (depth + 1)
    for x in xs do acc := acc.insert x
    low := min low l
  modify fun m => { m with inAxioms := m.inAxioms.erase n }
  if low ≥ depth then modify fun m => { m with axioms := m.axioms.insert n acc }
  return (acc, low)

/-- The axioms `n` rests on, through every constant it names. -/
def axiomsOf (n : Name) : M NameSet :=
  Prod.fst <$> axiomsAt n 0

end ProofMap
