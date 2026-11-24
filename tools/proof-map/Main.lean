import ProofMap.Map

open Lean ProofMap

/-- The citations of every declaration: the paragraphs each cites, the declarations citing
each paragraph, and the words that cite no paragraph. -/
def citeAll (decls : Array Decl) (ids prefixes : Std.HashSet String) :
    Array (Array String) × Std.HashMap String (Array Nat) × Array (Name × String) := Id.run do
  let mut each := #[]
  let mut by_ : Std.HashMap String (Array Nat) := {}
  let mut bad := #[]
  for h : i in [0:decls.size] do
    let d := decls[i]
    let (good, wrong) := citations ids prefixes (d.doc.getD "")
    each := each.push good
    for g in good do by_ := by_.insert g ((by_[g]?.getD #[]).push i)
    for w in wrong do bad := bad.push (d.name, w)
  return (each, by_, bad)

/-- The paragraphs that the docs of the model's modules cite. -/
def moduleCitations (env : Environment) (decls : Array Decl) (ids prefixes : Std.HashSet String) :
    Std.HashSet String :=
  (decls.map (·.module)).toList.eraseDups.foldl (init := {}) fun acc m =>
    ((getModuleDoc? env m).getD #[]).foldl (init := acc) fun acc d =>
      (citations ids prefixes d.doc).1.foldl (·.insert ·) acc

/-- The statements of the theorems that `soundness` reaches, as Lean prints them. -/
def statements (env : Environment) (decls : Array Decl) (inTheorem : Std.HashSet Nat) :
    IO (Std.HashMap Nat String) := do
  let mut out := {}
  for i in inTheorem do
    let d := decls[i]!
    if d.kind == "theorem" then
      if let some ci := env.find? d.name then out := out.insert i (← pp env ci.type 90)
  return out

/-- `proof-map ROOT OUT`: writes the map of the model that `lake` built, against the
Reference in `ROOT/reference`, to `OUT` as JSON, and fails if it finds a problem. -/
unsafe def main (args : List String) : IO UInt32 := do
  let [root, out] := args | IO.eprintln "usage: proof-map ROOT OUT.json"; return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Stilt }] {} (trustLevel := 1024) (loadExts := true)
  let decls ← declarations env
  let index := decls.foldl (init := ({} : Std.HashMap Name Nat)) fun m d => m.insert d.name m.size
  let inTheorem := reached decls index
  let dir : System.FilePath := root / "reference"
  let paras ← paragraphs dir
  let ids := Std.HashSet.ofArray (paras.map (·.id))
  let prefixes := Std.HashSet.ofArray (paras.map (prefixOf ·.id))
  let (each, by_, bad) := citeAll decls ids prefixes
  let shownStatements ← statements env decls inTheorem
  let cite := fun doc => (citations ids prefixes doc).1
  let accepted ← fields env `Stilt.Program.Accepted
  let promised ← promises env (rangedNames env)
  let found := problems decls bad
  let json := Json.mkObj [
    ("decls", Json.arr <| decls.mapIdx fun i d =>
      declJson index each[i]! (inTheorem.contains i) shownStatements[i]? d),
    ("soundness", toJson (index[`Stilt.soundness]?.getD 0)),
    ("accepted", Json.arr (accepted.map (fieldJson index cite))),
    ("promises", Json.arr (promised.map (fieldJson index cite))),
    ("chapters", ← chaptersJson dir paras by_ inTheorem (moduleCitations env decls ids prefixes)),
    ("modules", modulesJson env decls inTheorem),
    ("problems", toJson found)]
  IO.FS.writeFile out json.compress
  IO.println s!"proof map: {decls.size} declarations, {inTheorem.size} reached by soundness, {by_.size} of {paras.size} paragraphs cited"
  for p in found do IO.eprintln s!"ERROR {p}"
  return if found.isEmpty then 0 else 1
