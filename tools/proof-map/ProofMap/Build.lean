import ProofMap.Collect

/-!
# The map's declarations

Reads an environment that imports the model and gives each written declaration, sorted by
module and line.
-/

open Lean

namespace ProofMap

/-- The source line of a declaration, from its range. -/
def lineOf (env : Environment) (n : Name) : Nat :=
  (declRangeExt.find? env n).map (·.range.pos.line) |>.getD 0

/-- The names of the model that have a source range. -/
def rangedNames (env : Environment) : NameSet :=
  env.constants.fold (init := {}) fun acc n _ =>
    if inModel env n && (declRangeExt.find? env n).isSome then acc.insert n else acc

/-- One written declaration, with what it uses and the axioms it rests on. -/
def decl (ranged : NameSet) (ci : ConstantInfo) (doc : Option String)
    (partDocs : Array String) : M Decl := do
  let env ← read
  let n := ci.name
  let statement ← reachAll ranged n (match ci with
    | .inductInfo i => i.ctors.foldl (fun acc c =>
        acc ++ ((env.find? c).map (used ·.type) |>.getD #[])) (used ci.type)
    | _ => used ci.type)
  let body ← match ci with
    | .inductInfo _ => pure #[]
    | _ => reachAll ranged n ((ci.value? (allowOpaque := true)).map used |>.getD #[])
  let axs := (← axiomsOf n).toArray.filter (!standardAxioms.contains ·)
  return { name := n, kind := kindOf env ci, module := (moduleOf env n).getD .anonymous,
           line := lineOf env n, doc, partDocs, statement, body, axioms := axs.qsort Name.lt }

/-- Every written declaration of the model in `env`. -/
def declarations (env : Environment) : IO (Array Decl) := do
  let ranged := rangedNames env
  let names := ranged.toArray.filter (written env ranged)
  let mut docs : Array (Option String) := #[]
  for n in names do docs := docs.push (← findDocString? env n)
  -- The constructors and projections of the model, each of which stands for another
  -- declaration, whose citations its doc adds to.
  let parts := env.constants.fold (init := #[]) fun acc m _ =>
    if inModel env m && standFor env m != m then acc.push m else acc
  let mut partDocs : Std.HashMap Name (Array String) := {}
  for m in parts.qsort Name.lt do
    if let some d ← findDocString? env m then
      let s := standFor env m
      partDocs := partDocs.insert s ((partDocs[s]?.getD #[]).push d)
  let run : M (Array Decl) := do
    let mut out := #[]
    for n in names, d in docs do
      if let some ci := env.find? n then
        out := out.push (← decl ranged ci d (partDocs[n]?.getD #[]))
    return out
  let out := (run.run env).run' {}
  return out.qsort fun a b =>
    a.module.toString < b.module.toString || (a.module == b.module && a.line < b.line)

end ProofMap
