import ProofMap.Output

/-!
# Assembling the map

A paragraph of the Reference is **in the theorem** when a declaration that `soundness`
reaches cites it, **modeled** when only other declarations do, **described** when only a
module's doc does, and **not modeled** otherwise. A problem fails the map: a citation of
no paragraph, or a declaration resting on `sorry` or an axiom of the model's own.
-/

open Lean

namespace ProofMap

/-- The status of a paragraph, from what cites it. -/
def status (byTheorem byModel byModule : Bool) : String :=
  if byTheorem then "theorem" else if byModel then "model"
  else if byModule then "described" else "none"

/-- The title of a chapter: its first line without the `#`. -/
def title (text : String) : String :=
  ((text.splitOn "\n").headD "").dropWhile (fun c => c == '#' || c == ' ') |>.toString

/-- Every chapter with its paragraphs, each with its status and the declarations citing it. -/
def chaptersJson (dir : System.FilePath) (paras : Array Paragraph)
    (by_ : Std.HashMap String (Array Nat)) (inTheorem : Std.HashSet Nat)
    (moduleCited : Std.HashSet String) : IO Json := do
  let files := (paras.map (·.chapter)).toList.eraseDups
  let mut out := #[]
  for f in files do
    let text ← IO.FS.readFile (dir / f)
    let ps := (paras.filter (·.chapter == f)).map fun p =>
      let ds := by_[p.id]?.getD #[]
      Json.mkObj [("id", toJson p.id), ("text", toJson p.text), ("by", toJson ds),
        ("status", toJson (status (ds.any inTheorem.contains) (!ds.isEmpty)
          (moduleCited.contains p.id)))]
    out := out.push (Json.mkObj [("file", toJson f), ("title", toJson (title text)),
      ("paragraphs", Json.arr ps)])
  return Json.arr out

/-- The modules of the model, each with its doc, its declarations and how many of them
`soundness` reaches. -/
def modulesJson (env : Environment) (decls : Array Decl) (inTheorem : Std.HashSet Nat) :
    Json := Id.run do
  let mods := (decls.map (·.module)).toList.eraseDups
  let mut out := #[]
  for m in mods do
    let mine := (List.range decls.size).filter (decls[·]!.module == m)
    let doc := (getModuleDoc? env m).bind (·[0]?) |>.map (·.doc)
    out := out.push <| Json.mkObj <| [("n", toJson (shown m)), ("f", toJson (fileOf m)),
      ("decls", toJson mine.length), ("r", toJson (mine.filter inTheorem.contains).length)]
      ++ (doc.map fun d => [("d", toJson d)]).getD []
  return Json.arr out

/-- The problems of the map. -/
def problems (decls : Array Decl) (bad : Array (Name × String)) : Array String :=
  bad.map (fun (n, w) => s!"{shown n} cites `{w}`, which is no paragraph of the Reference")
  ++ (decls.filter (!·.axioms.isEmpty)).map fun d =>
    s!"{shown d.name} rests on {d.axioms.toList.map toString}"

end ProofMap
