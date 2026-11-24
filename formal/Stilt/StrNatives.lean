import Stilt.Strings

/-!
# The natives of strings

What std.str's natives that split, trim, replace and count compute, on a
string's scalar values (std.bytes-and-scalars): `chars()`, `split(sep)`,
`lines()` and `split_whitespace()` (std.str-splitting), `trim()`,
`trim_start()` and `trim_end()`, which strip ASCII whitespace
(std.str-classes), `replace(from, to)`, `replace_first(from, to)`,
`reversed()`, `ascii_upper()` and `ascii_lower()` (std.str-building),
`count(sub)` (std.str-search) and `char_count()` (std.str).
-/

namespace Stilt

namespace Str

/-- ASCII whitespace: a space, `\t`, `\n`, `\r` or a form feed (std.str-classes). -/
def isSpace (c : Char) : Bool := c = ' ' || c = '\t' || c = '\n' || c = '\r' || c.toNat = 12

/-- The pieces of `cs` between the occurrences of a non-empty `sep`, found from
left to right, `acc` the current piece reversed (std.str-splitting). Each step
reads at least one scalar value, so `cs.length` steps, the fuel `n`, suffice. -/
def piecesOf (sep : List Char) : Nat → List Char → List Char → List (List Char)
  | _, acc, [] => [acc.reverse]
  | 0, acc, cs => [acc.reverse ++ cs]
  | n + 1, acc, c :: cs =>
    if sep ≠ [] ∧ sep.isPrefixOf (c :: cs) then
      acc.reverse :: piecesOf sep n [] (cs.drop (sep.length - 1))
    else piecesOf sep n (c :: acc) cs

/-- The pieces of `cs` between the occurrences of `sep`. -/
def pieces (sep cs : List Char) : List (List Char) := piecesOf sep cs.length [] cs

/-- `s.chars()`: one string for each scalar value (std.str). -/
def chars (s : String) : List String := s.toList.map fun c => String.ofList [c]

/-- `s.split(sep)`: the pieces between the occurrences of `sep`, or the scalar
values for an empty `sep`, as `chars` gives them (std.str-splitting). -/
def split (s sep : String) : List String :=
  if sep.isEmpty then chars s else (pieces sep.toList s.toList).map String.ofList

/-- `s.lines()`: the pieces between the `\n`s, each without one trailing `\r`,
and no empty last piece after a final `\n` (std.str-splitting). -/
def lines (s : String) : List String :=
  let ps := pieces ['\n'] s.toList
  let ps := if ps.getLast? = some [] then ps.dropLast else ps
  ps.map fun p => String.ofList (if p.getLast? = some '\r' then p.dropLast else p)

/-- The pieces of `cs` between its ASCII whitespace, `acc` the current piece
reversed. -/
def words (acc : List Char) : List Char → List (List Char)
  | [] => [acc.reverse]
  | c :: cs => if isSpace c then acc.reverse :: words [] cs else words (c :: acc) cs

/-- `s.split_whitespace()`: the pieces between runs of ASCII whitespace, none
empty (std.str-splitting). -/
def splitWhitespace (s : String) : List String :=
  ((words [] s.toList).filter (· ≠ [])).map String.ofList

/-- `trim_start()`, `trim_end()` and `trim()` strip ASCII whitespace from the
start, the end, or both (std.str-splitting). -/
def trimStart (s : String) : String := String.ofList (s.toList.dropWhile isSpace)
def trimEnd (s : String) : String := String.ofList (s.toList.reverse.dropWhile isSpace).reverse
def trim (s : String) : String := trimEnd (trimStart s)

/-- `cs` with every non-overlapping occurrence of `pat` replaced by `rep`, from
left to right, or `rep` at every boundary between scalar values, both ends
included, for an empty `pat` (std.str-building); the fuel `n` is `cs.length`. -/
def replaceFrom (pat rep : List Char) : Nat → List Char → List Char
  | _, [] => if pat = [] then rep else []
  | 0, cs => cs
  | n + 1, c :: cs =>
    if pat = [] then rep ++ c :: replaceFrom pat rep n cs
    else if pat.isPrefixOf (c :: cs) then rep ++ replaceFrom pat rep n (cs.drop (pat.length - 1))
    else c :: replaceFrom pat rep n cs

def replaceAll (pat rep cs : List Char) : List Char := replaceFrom pat rep cs.length cs

/-- `cs` with its first occurrence of `pat` replaced by `rep`, or `rep` at the
start for an empty `pat` (std.str-building). -/
def replaceFirst (pat rep : List Char) : List Char → List Char
  | [] => if pat = [] then rep else []
  | c :: cs =>
    if pat.isPrefixOf (c :: cs) then rep ++ (c :: cs).drop pat.length
    else c :: replaceFirst pat rep cs

/-- The non-overlapping occurrences of a non-empty `pat` in `cs`, counted from
left to right; the fuel `n` is `cs.length`. -/
def occurrences (pat : List Char) : Nat → List Char → Nat
  | _, [] => 0
  | 0, _ => 0
  | n + 1, c :: cs =>
    if pat ≠ [] ∧ pat.isPrefixOf (c :: cs) then 1 + occurrences pat n (cs.drop (pat.length - 1))
    else occurrences pat n cs

/-- `s.count(sub)`: the non-overlapping occurrences of `sub` from left to
right, and the number of scalar values plus one for an empty `sub`
(std.str-search). -/
def count (s sub : String) : Nat :=
  if sub.isEmpty then s.length + 1 else occurrences sub.toList s.length s.toList

/-- The line at the start of `s`: up to its first `\n`, which it leaves out, and
without a `\r` that ends what is left, even on a last line with no `\n`; none
when `s` is empty, at the end of the input (std.read-line). -/
def nextLine (s : String) : List String :=
  if s.isEmpty then [] else
    let line := s.toList.takeWhile (· ≠ '\n')
    [String.ofList (if line.getLast? = some '\r' then line.dropLast else line)]

/-- The offset of the first place in `bs`, from `i`, where `sub` starts, at its end
for an empty `sub`'s last. -/
def firstAt (sub : List UInt8) : List UInt8 → Nat → Option Nat
  | [], i => if sub.isEmpty then some i else none
  | b :: bs, i => if sub.isPrefixOf (b :: bs) then some i else firstAt sub bs (i + 1)

/-- The offset of the last place in `bs`, from `i`, where `sub` starts. -/
def lastAt (sub : List UInt8) : List UInt8 → Nat → Option Nat
  | [], i => if sub.isEmpty then some i else none
  | b :: bs, i => match lastAt sub bs (i + 1) with
    | some j => some j
    | none => if sub.isPrefixOf (b :: bs) then some i else none

/-- `s.find(sub)`, or `s.rfind(sub)` when `last`: the byte offset of the first or the
last occurrence of `sub` in `s`, which may overlap earlier ones; `find("")` is `0` and
`rfind("")` the length (std.str-search). UTF-8 is self-synchronizing, so a match of
whole strings' bytes starts at a scalar's start. -/
def find (last : Bool) (s sub : String) : Option Nat :=
  (if last then lastAt else firstAt) sub.toUTF8.toList s.toUTF8.toList 0

/-- The bits a UTF-8 sequence's lead byte gives its scalar value, and the ranges its
continuation bytes must be in: the Unicode Standard's table of well-formed sequences
(§3.9), which rules out overlong forms, surrogates and values above `0x10FFFF`;
none for a byte that leads no sequence. -/
def utf8Lead (b : Nat) : Option (Nat × List (Nat × Nat)) :=
  let tail := (0x80, 0xBF)
  if b < 0x80 then some (b, [])
  else if 0xC2 ≤ b ∧ b ≤ 0xDF then some (b % 0x20, [tail])
  else if b = 0xE0 then some (b % 0x10, [(0xA0, 0xBF), tail])
  else if b = 0xED then some (b % 0x10, [(0x80, 0x9F), tail])
  else if 0xE1 ≤ b ∧ b ≤ 0xEF then some (b % 0x10, [tail, tail])
  else if b = 0xF0 then some (b % 8, [(0x90, 0xBF), tail, tail])
  else if 0xF1 ≤ b ∧ b ≤ 0xF3 then some (b % 8, [tail, tail, tail])
  else if b = 0xF4 then some (b % 8, [(0x80, 0x8F), tail, tail])
  else none

/-- The continuation bytes read in their ranges: the value so far, the bytes after
those that fit, and whether every range had its byte. -/
def utf8Tail : List (Nat × Nat) → Nat → List Nat → Nat × List Nat × Bool
  | [], v, bs => (v, bs, true)
  | (lo, hi) :: rs, v, c :: bs =>
    if lo ≤ c ∧ c ≤ hi then utf8Tail rs (v * 64 + c % 64) bs else (v, c :: bs, false)
  | _ :: _, v, [] => (v, [], false)

/-- Bytes decoded, each maximal subpart of an ill-formed sequence one U+FFFD, the
next byte read anew (std.code-points), with whether they were all well formed;
`fuel` at least their number. -/
def utf8Decode : Nat → List Nat → List Char × Bool
  | 0, _ | _, [] => ([], true)
  | fuel + 1, b :: bs =>
    match utf8Lead b with
    | none => ('\uFFFD' :: (utf8Decode fuel bs).1, false)
    | some (v, rs) =>
      let (v, rest, whole) := utf8Tail rs v bs
      let (cs, ok) := utf8Decode fuel rest
      if whole then (Char.ofNat v :: cs, ok) else ('\uFFFD' :: cs, false)

/-- The string that bytes decode to, and whether they are valid UTF-8. -/
def fromUtf8 (ns : List Int) : String × Bool :=
  let (cs, ok) := utf8Decode ns.length (ns.map Int.toNat)
  (String.ofList cs, ok)

/-- The string of one scalar value, if `p` is one: not a surrogate, `0xD800` to
`0xDFFF`, nor above `0x10FFFF` (std.code-points). -/
def fromCodePoint (p : Int) : List String :=
  if 0 ≤ p ∧ p ≤ 0x10FFFF ∧ ¬(0xD800 ≤ p ∧ p ≤ 0xDFFF) then [String.ofList [Char.ofNat p.toNat]]
  else []

/-- What reading a line leaves of `s`: what follows its first `\n`, or nothing. -/
def afterLine (s : String) : String := String.ofList ((s.toList.dropWhile (· ≠ '\n')).drop 1)

/-- `s` with copies of `fill` before it, or after it when not `start`, until it holds
`width` scalar values, the last copy cut short at its end; unchanged when it is that
wide already or `fill` is empty (std.str-building). -/
def pad (start : Bool) (s : String) (width : Int) (fill : String) : String :=
  if fill.isEmpty || width ≤ s.length then s else
    let need := (width - s.length).toNat
    let padding := ((List.replicate need fill.toList).flatten).take need
    String.ofList (if start then padding ++ s.toList else s.toList ++ padding)

end Str

/-- Whether a string is of a class: `ascii` holds for every string whose bytes are
below `0x80`, the empty one included, and each other class for a string that isn't
empty and whose every byte is of it; a scalar beyond ASCII is of none
(std.str-classes). -/
def StrClass.test (c : StrClass) (s : String) : Bool :=
  let all (p : Char → Bool) := !s.isEmpty && s.toList.all p
  match c with
  | .ascii => s.toList.all (·.toNat < 128)
  | .digit => all Char.isDigit
  | .alpha => all Char.isAlpha
  | .alnum => all Char.isAlphanum
  | .whitespace => all Str.isSpace
  | .upper => all Char.isUpper
  | .lower => all Char.isLower

/-- What a native of `str` from a string to a string gives. -/
def StrMap.apply : StrMap → String → String
  | .trim => Str.trim
  | .trimStart => Str.trimStart
  | .trimEnd => Str.trimEnd
  | .asciiUpper => fun s => String.ofList (s.toList.map Char.toUpper)
  | .asciiLower => fun s => String.ofList (s.toList.map Char.toLower)
  | .reversed => fun s => String.ofList s.toList.reverse
  | .afterLine => Str.afterLine

/-- `s.replace(from, to)`, or `s.replace_first(from, to)` when `first` says so
(std.str-building). -/
def Str.replace (first : Bool) (s a b : String) : String :=
  String.ofList ((if first then Str.replaceFirst else Str.replaceAll) a.toList b.toList s.toList)

end Stilt
