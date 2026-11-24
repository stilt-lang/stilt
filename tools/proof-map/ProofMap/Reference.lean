import Lean

/-!
# The Reference's paragraphs and the citations of them

A paragraph of the Reference is an `<a id="…"></a>` line of a chapter, followed by its
text. A citation is a word of a doc comment written as a paragraph ID is, `modes.law`,
whose part before the first dot is the prefix of some paragraph's ID: a citation of a
paragraph that no chapter has is a mistake the map reports.
-/

namespace ProofMap

/-- One paragraph: its ID, its chapter's file and the start of its text. -/
structure Paragraph where
  id : String
  chapter : String
  text : String

/-- The first sentence of a paragraph's text, or its first 160 characters. -/
def opening (text : String) : String :=
  let first := (text.splitOn ". ").headD text
  if first.length ≤ 160 then first else (first.take 157).toString ++ "…"

/-- The paragraphs of a chapter, in order. -/
def paragraphsOf (chapter text : String) : Array Paragraph := Id.run do
  let lines := (text.splitOn "\n").toArray
  let mut out := #[]
  for i in [0:lines.size] do
    let line := lines[i]!
    if line.startsWith "<a id=\"" then
      let id := ((line.drop 7).toString.splitOn "\"").headD ""
      out := out.push { id, chapter, text := opening (lines[i + 1]?.getD "") }
  return out

/-- Every paragraph of the chapters in `dir`, `reference/`, in the chapters' order. -/
def paragraphs (dir : System.FilePath) : IO (Array Paragraph) := do
  let entries ← dir.readDir
  let chapters := (entries.map (·.fileName)).filter fun f =>
    f.endsWith ".md" && (f.front).isDigit
  let mut out := #[]
  for f in chapters.qsort (· < ·) do
    out := out ++ paragraphsOf f (← IO.FS.readFile (dir / f))
  return out

/-- Whether `c` can be part of a paragraph ID. -/
def idChar (c : Char) : Bool := c.isLower || c.isDigit || c == '-' || c == '.'

/-- The words of `s` written as paragraph IDs, outside code in backquotes: letters, digits,
`-` and `.`, holding a dot, without a final dot. -/
def idWords (s : String) : Array String := Id.run do
  let mut out := #[]
  let mut cur := ""
  let mut code := false
  for c in s.toList ++ [' '] do
    if c == '`' then code := !code
    if idChar c && !code then cur := cur.push c
    else
      let w := (cur.toList.reverse.dropWhile (· == '.')).reverse
      if w.contains '.' && !w.isEmpty && w.head! != '.' then out := out.push (String.ofList w)
      cur := ""
  return out

/-- The prefix of an ID: its part before the first dot. -/
def prefixOf (id : String) : String := (id.splitOn ".").headD id

/-- The citations in a doc comment, given the IDs and prefixes of the Reference: the IDs
it names, and the words that look like IDs of no paragraph. -/
def citations (ids prefixes : Std.HashSet String) (doc : String) :
    Array String × Array String :=
  (idWords doc).foldl (init := (#[], #[])) fun (good, bad) w =>
    if ids.contains w then (if good.contains w then good else good.push w, bad)
    else if prefixes.contains (prefixOf w) && (w.splitOn ".").length == 2 then (good, bad.push w)
    else (good, bad)

end ProofMap
