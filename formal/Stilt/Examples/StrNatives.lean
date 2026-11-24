import Stilt.StrNatives

/-!
# The natives of strings

The cases std.str, std.str-search, std.str-splitting and std.str-building name.
-/

namespace Stilt.Examples.StrNatives

open Str

example : split "a,,b" "," = ["a", "", "b"] := by decide
example : split "" "," = [""] := by decide
example : split "héllo" "" = ["h", "é", "l", "l", "o"] := by decide
example : split "a--b--" "--" = ["a", "b", ""] := by decide
example : split "aaa" "aa" = ["", "a"] := by decide
example : lines "" = [] := by decide
example : lines "a\r\nb\n" = ["a", "b"] := by decide
example : lines "a\n\nb" = ["a", "", "b"] := by decide
example : lines "a\n\n" = ["a", ""] := by decide
example : splitWhitespace " a  b " = ["a", "b"] := by decide
example : splitWhitespace "\t\n" = [] := by decide
example : trim " \t a b \r\n" = "a b" := by decide
example : trimStart "  a " = "a " := by decide
example : trimEnd "  a " = "  a" := by decide
example : Str.replace false "ab" "" "-" = "-a-b-" := by decide
example : Str.replace false "" "" "-" = "-" := by decide
example : Str.replace false "aaa" "aa" "b" = "ba" := by decide
example : Str.replace true "abab" "b" "c" = "acab" := by decide
example : Str.replace true "ab" "" "-" = "-ab" := by decide
example : count "aaa" "aa" = 1 := by decide
example : count "héllo" "" = 6 := by decide
example : StrMap.reversed.apply "héllo" = "olléh" := by decide
example : StrMap.asciiUpper.apply "héllo" = "HéLLO" := by decide
example : StrMap.asciiLower.apply "ÉCOLE" = "École" := by decide
example : chars "é!" = ["é", "!"] := by decide

/-- A line leaves out its `\n` and a `\r` before it, a last line without a `\n`
its final `\r`, and an empty input has no line (std.read-line). -/
example : nextLine "a\r\nb" = ["a"] ∧ afterLine "a\r\nb" = "b" := by decide +kernel
example : nextLine "b\r" = ["b"] ∧ afterLine "b\r" = "" := by decide +kernel
example : nextLine "\nc" = [""] ∧ afterLine "\nc" = "c" := by decide +kernel
example : nextLine "" = [] := by decide +kernel

/-- `find` and `rfind` give byte offsets, the last occurrence may overlap earlier ones,
and the empty string is at `0` and at the length (std.str-search). -/
example : find false "héllo" "l" = some 3 ∧ find true "héllo" "l" = some 4 := by decide +kernel
example : find true "aaa" "aa" = some 1 ∧ find false "abc" "x" = none := by decide +kernel
example : find false "ab" "" = some 0 ∧ find true "ab" "" = some 2 := by decide +kernel

/-- Valid UTF-8 decodes to its scalars; an overlong form, a surrogate's encoding and a
cut sequence are ill formed, each maximal subpart one U+FFFD (std.code-points). -/
example : fromUtf8 [0x68, 0xC3, 0xA9] = ("hé", true) := by decide +kernel
example : fromUtf8 [0xC0, 0x80] = ("\uFFFD\uFFFD", false) := by decide +kernel
example : fromUtf8 [0xED, 0xA0, 0x80] = ("\uFFFD\uFFFD\uFFFD", false) := by decide +kernel
example : fromUtf8 [0xF0, 0x9F, 0x98, 0x41] = ("\uFFFDA", false) := by decide +kernel
example : fromCodePoint 0xE9 = ["é"] ∧ fromCodePoint 0xD800 = [] ∧ fromCodePoint 0x110000 = [] := by
  decide +kernel

/-- `"7".pad_start(4, "ab")` cuts the last copy short, and a string that wide already
or an empty fill comes back unchanged (std.str-building). -/
example : pad true "7" 4 "ab" = "aba7" ∧ pad false "7" 4 "ab" = "7aba" := by decide +kernel
example : pad true "abc" 2 "-" = "abc" ∧ pad true "a" 3 "" = "a" := by decide +kernel

/-- Every string with no byte from `0x80` is ASCII, the empty one included, and a class
holds only for a string that isn't empty (std.str-classes). -/
example : StrClass.ascii.test "" ∧ ¬ StrClass.digit.test "" ∧ StrClass.digit.test "42" ∧
    ¬ StrClass.ascii.test "é" ∧ ¬ StrClass.alpha.test "é" := by decide +kernel

end Stilt.Examples.StrNatives
