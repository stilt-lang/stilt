import ProofMap.Collect

/-!
# The theorem's shape

`soundness` says that every accepted program keeps its promises: the fields of
`Program.Accepted` are the checks, those of `Program.Promises` the promises, and the proof
gives each promise from a lemma, in the order of the fields. Statements are printed as
Lean prints them, inside the namespace `Stilt`.
-/

open Lean

namespace ProofMap

/-- A field of `Accepted` or `Promises`: its projection, its doc, its statement, and the
written declarations the proof of `soundness` gives it from. -/
structure Field where
  name : Name
  doc : Option String
  statement : String
  from_ : Array Name := #[]

/-- Prints `e` as Lean does inside the namespace `Stilt`, at most `width` columns wide. -/
def pp (env : Environment) (e : Expr) (width := 100) : IO String := do
  let opts := (({} : Options).setBool `pp.proofs false).set `format.width width
  let ctx : Core.Context :=
    { fileName := "<proof-map>", fileMap := default, maxHeartbeats := 0, options := opts,
      currNamespace := `Stilt, openDecls := [.simple `Stilt []] }
  let (fmt, _) ← (Meta.ppExpr e |>.run' {} {}).toIO ctx { env }
  return fmt.pretty width

/-- The statement of a field: its type under the structure's parameters and itself. -/
def fieldStatement (env : Environment) (ty : Expr) (depth : Nat) (width := 100) :
    IO String := do
  let opts := (({} : Options).setBool `pp.proofs false).set `format.width width
  let ctx : Core.Context :=
    { fileName := "<proof-map>", fileMap := default, maxHeartbeats := 0, options := opts,
      currNamespace := `Stilt, openDecls := [.simple `Stilt []] }
  let go : MetaM Format := Meta.forallBoundedTelescope ty depth fun _ body => Meta.ppExpr body
  let (fmt, _) ← (go.run' {} {}).toIO ctx { env }
  return fmt.pretty width

/-- The fields of structure `s`, each with its statement. -/
def fields (env : Environment) (s : Name) : IO (Array Field) := do
  let depth := match env.find? s with
    | some (.inductInfo i) => i.numParams + 1
    | _ => 0
  let mut out := #[]
  for f in getStructureFields env s do
    let proj := s ++ f
    let some ci := env.find? proj | continue
    out := out.push { name := proj, doc := ← findDocString? env proj,
                      statement := ← fieldStatement env ci.type depth }
  return out

/-- The arguments that the proof of `soundness` gives `Promises.mk` for its fields, under
the proof's binders. -/
def promiseProofs (env : Environment) : Array Expr := Id.run do
  let some ci := env.find? `Stilt.soundness | return #[]
  let some v := ci.value? (allowOpaque := true) | return #[]
  let mut e := v
  e := e.consumeMData
  while e.isLambda do e := e.bindingBody!.consumeMData
  let n := (getStructureFields env `Stilt.Program.Promises).size
  if e.getAppFn.constName? == some `Stilt.Program.Promises.mk then
    return e.getAppArgs.extract (e.getAppNumArgs - n) e.getAppNumArgs
  return #[]

/-- The promises, each with the written declarations its proof in `soundness` uses. -/
def promises (env : Environment) (ranged : NameSet) : IO (Array Field) := do
  let fs ← fields env `Stilt.Program.Promises
  let proofs := promiseProofs env
  let walk : M (Array (Array Name)) := proofs.mapM fun e =>
    reachAll ranged `Stilt.soundness (used e)
  let froms := Id.run ((walk.run env).run' {})
  return fs.mapIdx fun i f => { f with
    from_ := (froms[i]?.getD #[]).filter (· != `Stilt.Program.Accepted) }

end ProofMap
