import Stilt.Maps
import Stilt.FloatText

/-!
# Showing values

The output of the prelude's structural impls of `Show` (std.show-output and
traits.show): a value's text, and its text nested in another value, where a
string is quoted and escaped (std.show-names-and-escapes). Variants and records
are shown by their unqualified names; a tuple, a map and a set by their own
forms. A float is shown in its shortest printed form (numbers.printing-floats).
The export never shows a type with an impl of `Show` of its own, whose output
the program writes.
-/

namespace Stilt

/-- A digit of a number in lowercase hexadecimal. -/
def hexDigit (d : Nat) : Char :=
  if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

/-- A number in lowercase hexadecimal, with no leading zeros. -/
def hex (n : Nat) : String :=
  if n < 16 then (hexDigit n).toString else hex (n / 16) ++ (hexDigit (n % 16)).toString
termination_by n
decreasing_by omega

/-- A character of a nested string, escaped (std.show-names-and-escapes). -/
def escapeChar (c : Char) : String :=
  if c = '"' then "\\\""
  else if c = '\\' then "\\\\"
  else if c = '\n' then "\\n"
  else if c = '\t' then "\\t"
  else if c = '\r' then "\\r"
  else if c.toNat = 0 then "\\0"
  else if c.toNat < 0x20 ∨ c.toNat = 0x7f then "\\u{" ++ hex c.toNat ++ "}"
  else c.toString

/-- A string nested in another value: quoted and escaped. -/
def quoted (s : String) : String := "\"" ++ String.join (s.toList.map escapeChar) ++ "\""

/-- A type's name as a value shows it: unqualified, after its module's, and without the
arguments that name one instance of a generic type (std.show-names-and-escapes). -/
def unqualified (n : Name) : String :=
  let base := (n.splitOn "<").headD n
  (base.splitOn ".").getLastD base

/-- Whether a record's name is an anonymous record type's: the type as written,
`{ f: T, … }`, its fields in the alphabetical order of their names, which no
declaration can be named (records.anonymous-types and records.field-order). -/
def anonymousName (R : Name) : Bool := R.startsWith "{ "

/-- Texts joined by `, `. -/
def commaJoin : List String → String
  | [] => ""
  | [s] => s
  | s :: rest => s ++ ", " ++ commaJoin rest

mutual

/-- A value's text, nested in another value or not. -/
def Value.shown (nested : Bool) : Value → String
  | .int n => toString n
  | .float x => x.text
  | .bool b => toString b
  | .str s => if nested then quoted s else s
  | .unit => "()"
  | .record R fields =>
    if R = tupleName then
      "(" ++ commaJoin (shownFields fields) ++ (if fields.length = 1 then ",)" else ")")
    else if R = mapName then "{" ++ commaJoin (shownEntries fields) ++ "}"
    else if R = setName then "Set([" ++ commaJoin (shownElements fields) ++ "])"
    else if anonymousName R then "{ " ++ commaJoin (shownNamed fields) ++ " }"
    else if fields.isEmpty then unqualified R ++ " {}"
    else unqualified R ++ " { " ++ commaJoin (shownNamed fields) ++ " }"
  | .variant _ C [] => C
  | .variant _ C vs => C ++ "(" ++ commaJoin (shownValues vs) ++ ")"
  | .list vs => "[" ++ commaJoin (shownValues vs) ++ "]"
  | .closure .. | .function .. | .handle .. | .window .. => ""

/-- Values, each nested. -/
def shownValues : List Value → List String
  | [] => []
  | v :: vs => v.shown true :: shownValues vs

/-- A tuple's elements, each nested. -/
def shownFields : List (Name × Value) → List String
  | [] => []
  | (_, v) :: fields => v.shown true :: shownFields fields

/-- A record's fields, `name: value`. -/
def shownNamed : List (Name × Value) → List String
  | [] => []
  | (f, v) :: fields => (f ++ ": " ++ v.shown true) :: shownNamed fields

/-- A map's entries, `key: value`, from its record's entries field. -/
def shownEntries : List (Name × Value) → List String
  | [] => []
  | (_, .list es) :: _ => shownPairs es
  | _ :: fields => shownEntries fields

/-- Entries, each a list of its key and its value. -/
def shownPairs : List Value → List String
  | [] => []
  | .list [k, v] :: es => (k.shown true ++ ": " ++ v.shown true) :: shownPairs es
  | _ :: es => shownPairs es

/-- A set's elements, from its record's elements field. -/
def shownElements : List (Name × Value) → List String
  | [] => []
  | (_, .list ks) :: _ => shownValues ks
  | _ :: fields => shownElements fields

end

end Stilt
