import Stilt.Semantics

/-!
# Strings

Runs of the required tests of std.bytes-and-scalars, std.str, std.str-search,
traits.built-in-impls, lexical.interpolation and numbers.printing-integers on
strings, in both models of memory. Each program raises the value it shows, as
in `Stilt.Examples`.
-/

namespace Stilt.Examples.Strings

/-- A program whose `main` raises a value of type `shown`. -/
private def program (shown : Ty) (main : Expr) : Program :=
  ⟨⟨[], [], [], [], [], [], []⟩, main, ⟨false, some shown, [], [], none⟩, {}⟩

/-- Both models give the same observation. -/
private def agree (p : Program) (o : Observation) : Prop :=
  (p.runCopy 64).observe = o ∧ (p.runInPlace 64).observe = o

/-- A string literal. -/
private def lit (t : String) : Expr := .op (.str t) []

/-- `let s = t; raise e`, with `s` in scope. -/
private def withStr (t : String) (shown : Ty) (e : Expr) : Program :=
  program shown (.letIn "s" .str (lit t) (.raise e))

/-- `s.slice(a, b)`. -/
private def slice (a b : Int) : Expr := .op .slice [.var "s", .int a, .int b]

/-! ## std.bytes-and-scalars and std.str: lengths and slices count bytes -/

example : agree (withStr "héllo" .i64 (.op .len [.var "s"])) (.raised (.int 6)) := ⟨rfl, rfl⟩
example : agree (withStr "" .bool (.op .isEmpty [.var "s"])) (.raised (.bool true)) := ⟨rfl, rfl⟩
example : agree (withStr "héllo" .str (slice 0 1)) (.raised (.str "h")) := ⟨rfl, rfl⟩
example : agree (withStr "héllo" .str (slice 1 3)) (.raised (.str "é")) := ⟨rfl, rfl⟩

/-- `"é".slice(1, 0)` panics with `bounds`, which is checked first. -/
example : agree (withStr "é" .str (slice 1 0)) (.panicked .bounds) := ⟨rfl, rfl⟩
example : agree (withStr "é" .str (slice 0 3)) (.panicked .bounds) := ⟨rfl, rfl⟩

/-- An offset inside a UTF-8 sequence panics with `utf8-boundary`, even for an
empty slice. -/
example : agree (withStr "é" .str (slice 0 1)) (.panicked .utf8Boundary) := ⟨rfl, rfl⟩
example : agree (withStr "é" .str (slice 1 1)) (.panicked .utf8Boundary) := ⟨rfl, rfl⟩

/-! ## std.str-search -/

example : agree (withStr "abc" .bool (.op (.search .contains) [.var "s", lit ""]))
    (.raised (.bool true)) := ⟨rfl, rfl⟩
example : agree (withStr "abc" .bool (.op (.search .contains) [.var "s", lit "bc"]))
    (.raised (.bool true)) := ⟨rfl, rfl⟩
example : agree (withStr "abc" .bool (.op (.search .startsWith) [.var "s", lit "b"]))
    (.raised (.bool false)) := ⟨rfl, rfl⟩
example : agree (withStr "abc" .bool (.op (.search .endsWith) [.var "s", lit "bc"]))
    (.raised (.bool true)) := ⟨rfl, rfl⟩

/-! ## traits.built-in-impls: strings by their bytes, and `false < true` -/

example : agree (withStr "ab" .bool (.op (.scompare .lt) [.var "s", lit "b"]))
    (.raised (.bool true)) := ⟨rfl, rfl⟩
example : agree (withStr "é" .bool (.op (.scompare .gt) [.var "s", lit "z"]))
    (.raised (.bool true)) := ⟨rfl, rfl⟩
example : agree (withStr "ab" .bool (.op (.scompare .eq) [.var "s", lit "ab"]))
    (.raised (.bool true)) := ⟨rfl, rfl⟩
example : agree (program .bool (.raise (.op (.bcompare .lt) [.bool false, .bool true])))
    (.raised (.bool true)) := ⟨rfl, rfl⟩

/-! ## lexical.interpolation: `"{n} of {b}"` joins its pieces, shown -/

example : agree (program .str
    (.letIn "n" .i64 (.int (-3)) (.letIn "b" .bool (.bool true)
      (.raise (.op .concat [.op (.showInt .i64) [.var "n"], lit " of ",
        .op .showBool [.var "b"]])))))
    (.raised (.str "-3 of true")) := ⟨rfl, rfl⟩

/-! ## std.str: `sep.join(parts)` puts `sep` between the parts, and joins none to `""` -/

private def parts (ts : List String) : Expr := .list .str (ts.map lit)

example : agree (program .str (.raise (.op (.list .join) [lit ", ", parts ["a", "b", "c"]])))
    (.raised (.str "a, b, c")) := ⟨rfl, rfl⟩
example : agree (program .str (.raise (.op (.list .join) [lit "-", parts []])))
    (.raised (.str "")) := ⟨rfl, rfl⟩

end Stilt.Examples.Strings
