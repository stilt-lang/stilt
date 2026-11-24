import ProofMap.Build
import ProofMap.Theorem
import ProofMap.Reference

/-!
# The map as JSON

What the page reads: every written declaration with what it uses, whether `soundness`
reaches it, and the paragraphs it cites; the checks and the promises; each paragraph of
the Reference with what models it; and the problems that fail the map.
-/

open Lean

namespace ProofMap

/-- A name as the page shows it: without the namespace `Stilt`, and a private name as
its user name. -/
def shown (n : Name) : String :=
  let n := (privateToUserName? n).getD n
  (n.replacePrefix `Stilt .anonymous).toString

/-- The source file of a module of the model, relative to the repository. -/
def fileOf (m : Name) : String :=
  "formal/" ++ (m.toString.replace "." "/") ++ ".lean"

/-- The declarations that `soundness` reaches through what statements and proofs use. -/
def reached (decls : Array Decl) (index : Std.HashMap Name Nat) : Std.HashSet Nat := Id.run do
  let some start := index[`Stilt.soundness]? | return {}
  let mut seen : Std.HashSet Nat := {}
  let mut todo := #[start]
  while h : todo.size > 0 do
    let i := todo.back
    todo := todo.pop
    if seen.contains i then continue
    seen := seen.insert i
    let d := decls[i]!
    for n in d.statement ++ d.body do
      if let some j := index[n]? then todo := todo.push j
  return seen

/-- The indexes of `names` among the declarations. -/
def indexes (index : Std.HashMap Name Nat) (names : Array Name) : Json :=
  toJson (names.filterMap fun n => (index[n]? : Option Nat))

/-- One declaration as the page reads it. -/
def declJson (index : Std.HashMap Name Nat) (cited : Array String) (inTheorem : Bool)
    (statement : Option String) (d : Decl) : Json :=
  Json.mkObj <| [("n", toJson (shown d.name)), ("k", toJson d.kind),
    ("m", toJson (shown d.module)), ("f", toJson (fileOf d.module)), ("l", toJson d.line),
    ("s", indexes index d.statement), ("b", indexes index d.body), ("c", toJson cited),
    ("r", toJson inTheorem)]
    ++ (d.doc.map fun x => [("d", toJson x)]).getD []
    ++ (statement.map fun x => [("t", toJson x)]).getD []
    ++ (if d.axioms.isEmpty then [] else [("a", toJson (d.axioms.map toString))])

/-- A field of `Accepted` or `Promises` as the page reads it. -/
def fieldJson (index : Std.HashMap Name Nat) (cite : String → Array String) (f : Field) :
    Json :=
  Json.mkObj <| [("n", toJson (f.name.componentsRev.headD .anonymous).toString),
    ("t", toJson f.statement), ("c", toJson (cite (f.doc.getD ""))),
    ("from", indexes index f.from_)] ++ (f.doc.map fun x => [("d", toJson x)]).getD []

end ProofMap
