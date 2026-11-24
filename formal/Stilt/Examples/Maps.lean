import Stilt.Semantics

/-!
# Maps and sets

Runs of the required tests of std.maps, std.map-functions, std.sets and
std.set-impls, in both models of memory. `m.insert(k, v)`, `m[k] = v` and
`m.remove(k)` store the changed map in `m`, as their `inout self` writes it
back, and `m[k] += v` reads `m[k]`, then stores (std.finding-keys). Each
program raises the value it shows, as in `Stilt.Examples`, several of them
as a tuple. Tuples of keys are keys too.
-/

namespace Stilt.Examples.Maps

/-- A program whose `main` raises a value of type `shown`. -/
private def program (shown : Ty) (main : Expr) : Program :=
  ⟨⟨[], [], [], [], [], [], []⟩, main, ⟨false, some shown, [], [], none⟩⟩

/-- Both models give the same observation. -/
private def agree (p : Program) (o : Observation) : Prop :=
  (p.runCopy 64).observe = o ∧ (p.runInPlace 64).observe = o

/-- A string literal. -/
private def lit (t : String) : Expr := .op (.str t) []

/-- `(e₁, …, eₙ)`. -/
private def tuple (es : List Expr) : Expr := .op .tuple es

/-- A function of the map `m`. -/
private def onM (o : MapOp) (args : List Expr) : Expr := .op (.map o) (.var "m" :: args)

/-- `m.insert(k, v)`, and `m[k] = v`. -/
private def insert (k v : Expr) : Expr := .assign ⟨"m", []⟩ (onM .insert [k, v])

/-- `m.remove(k)`, its result unused. -/
private def remove (k : Expr) : Expr := .assign ⟨"m", []⟩ (onM .remove [k])

/-- `Map<str, i64>`. -/
private def strMap : Ty := .map .str .i64

/-! ## std.maps: insertion order -/

/-- The body of `main` in std/map_order up to its fourth line:
`var m = Map.new(); m.insert("c", 1); m["a"] = 2; m.insert("b", 3);
m.insert("a", 20)`, then `rest`. -/
private def ordered (rest : Expr) : Expr :=
  .varIn "m" strMap (.op (.map .new) [])
    (.seq (insert (lit "c") (.int 1)) (.seq (insert (lit "a") (.int 2))
      (.seq (insert (lit "b") (.int 3)) (.seq (insert (lit "a") (.int 20)) rest))))

/-- A key that is inserted again keeps its position. -/
example : agree (program strMap (ordered (.raise (.var "m"))))
    (.raised (.mapOf [(.str "c", .int 1), (.str "a", .int 20), (.str "b", .int 3)] none)) :=
  ⟨rfl, rfl⟩

/-- A key inserted after its removal goes to the end: `m.remove("a");
m["a"] = 4` gives `{"c": 1, "b": 3, "a": 4}`, whose keys, values and entries
follow that order. -/
example : agree (program (.tuple [.list .str, .list .i64, .list (.tuple [.str, .i64])])
    (ordered (.seq (remove (lit "a")) (.seq (insert (lit "a") (.int 4))
      (.raise (tuple [onM .keys [], onM .values [], onM .entries []]))))))
    (.raised (.tuple [.list [.str "c", .str "b", .str "a"], .list [.int 1, .int 3, .int 4],
      .list [.tuple [.str "c", .int 1], .tuple [.str "b", .int 3], .tuple [.str "a", .int 4]]])) :=
  ⟨rfl, rfl⟩

/-- `m.len()`, `m.is_empty()`, `m.contains("b")` and `m.contains("z")`, after
removing a key twice. -/
example : agree (program (.tuple [.i64, .bool, .bool, .bool])
    (ordered (.seq (remove (lit "a")) (.seq (remove (lit "a"))
      (.raise (tuple [onM .len [], onM .isEmpty [], onM .contains [lit "b"],
        onM .contains [lit "z"]]))))))
    (.raised (.tuple [.int 2, .bool false, .bool true, .bool false])) := ⟨rfl, rfl⟩

/-- `m[k]` on a map without a default panics with `missing-key` for a missing
key. -/
example : agree (program .i64 (ordered (.raise (onM .index [lit "z"]))))
    (.panicked .missingKey) := ⟨rfl, rfl⟩

/-! ## std.maps and std.map-functions: defaults -/

/-- The body of `main` in std/map_defaults up to its third line:
`var counts = Map.with_default(0); for word in ["b", "a", "b"] { counts[word]
+= 1 }`, then `rest`. -/
private def counted (rest : Expr) : Expr :=
  .varIn "m" strMap (.op (.map .withDefault) [.int 0])
    (.seq (.for "w" .str (.list .str [lit "b", lit "a", lit "b"])
        (insert (.var "w") (.op (.arith .add .i64) [onM .index [.var "w"], .int 1])))
      rest)

/-- `counts[word] += 1` starts from the default: `{"b": 2, "a": 1}`, which
keeps the default. -/
example : agree (program strMap (counted (.raise (.var "m"))))
    (.raised (.mapOf [(.str "b", .int 2), (.str "a", .int 1)] (some (.int 0)))) := ⟨rfl, rfl⟩

/-- `counts["z"]` is the default without inserting it, and `get_or` gives its
own fallback whether or not the map has a default. -/
example : agree (program (.tuple [.i64, .i64, .bool, .i64])
    (counted (.raise (tuple [onM .index [lit "z"], onM .getOr [lit "z", .int 7],
      onM .contains [lit "z"], onM .len []]))))
    (.raised (.tuple [.int 0, .int 7, .bool false, .int 2])) := ⟨rfl, rfl⟩

/-! ## std.sets and std.set-impls -/

/-- A function of sets. -/
private def setOp (o : SetOp) (args : List Expr) : Expr := .op (.set o) args

/-- `Set.from_list([x, …])` of `i64`s. -/
private def ints (xs : List Int) : Expr := setOp .fromList [.list .i64 (xs.map .int)]

/-- `Set<i64>`. -/
private def intSet : Ty := .set .i64

/-- `Set.from_list` keeps the order of first appearance: `Set.from_list([3, 1,
3])` holds `3`, then `1`. -/
example : agree (program intSet (.raise (ints [3, 1, 3]))) (.raised (.setOf [.int 3, .int 1])) :=
  ⟨rfl, rfl⟩

example : agree (program (.tuple [.i64, .bool, .bool, .bool])
    (.letIn "s" intSet (ints [3, 1, 3]) (.raise (tuple [setOp .len [.var "s"],
      setOp .contains [.var "s", .int 1], setOp .contains [.var "s", .int 2],
      setOp .isEmpty [setOp .new []]]))))
    (.raised (.tuple [.int 2, .bool true, .bool false, .bool true])) := ⟨rfl, rfl⟩

/-- `insert` adds an absent element at the end, and `remove` of an absent one
changes nothing: `t` holds `["b", "a", "c"]` and `u.to_list()` is `[1, 2]`. -/
example : agree (program (.tuple [.set .str, .list .i64])
    (.varIn "t" (.set .str) (setOp .fromList [.list .str [lit "b", lit "a"]])
      (.seq (.assign ⟨"t", []⟩ (setOp .insert [.var "t", lit "a"]))
      (.seq (.assign ⟨"t", []⟩ (setOp .insert [.var "t", lit "c"]))
      (.varIn "u" intSet (ints [1, 2, 3])
        (.seq (.assign ⟨"u", []⟩ (setOp .remove [.var "u", .int 3]))
        (.seq (.assign ⟨"u", []⟩ (setOp .remove [.var "u", .int 9]))
          (.raise (tuple [.var "t", setOp .toList [.var "u"]])))))))))
    (.raised (.tuple [.setOf [.str "b", .str "a", .str "c"], .list [.int 1, .int 2]])) :=
  ⟨rfl, rfl⟩

/-- `union`, `intersection`, `difference` and `symmetric_difference` keep the
receiver's order, then the other's. -/
example : agree (program (.tuple [intSet, intSet, intSet, intSet])
    (.raise (tuple [setOp (.combine .union) [ints [1, 2], ints [3, 2]],
      setOp (.combine .intersection) [ints [1, 2, 3], ints [3, 2]],
      setOp (.combine .difference) [ints [1, 2], ints [3, 2]],
      setOp (.combine .symmetricDifference) [ints [1, 2], ints [3, 2]]])))
    (.raised (.tuple [.setOf [.int 1, .int 2, .int 3], .setOf [.int 2, .int 3], .setOf [.int 1],
      .setOf [.int 1, .int 3]])) := ⟨rfl, rfl⟩

/-- `is_subset`, `is_superset` and `is_disjoint`, and `==`, which finds the
same elements in any order. -/
example : agree (program (.tuple [.bool, .bool, .bool, .bool, .bool, .bool])
    (.raise (tuple [setOp (.relate .subset) [ints [1], ints [1, 2]],
      setOp (.relate .subset) [ints [1, 2], ints [1]],
      setOp (.relate .superset) [ints [1, 2], ints [2]],
      setOp (.relate .disjoint) [ints [1], ints [3, 2]],
      setOp (.relate .disjoint) [ints [1, 2], ints [3, 2]],
      setOp (.relate .equal) [ints [1, 2], ints [2, 1]]])))
    (.raised (.tuple [.bool true, .bool false, .bool true, .bool true, .bool false, .bool true])) :=
  ⟨rfl, rfl⟩

/-- Tuples of keys are keys, found by their elements in order (traits.structural-impls):
`(1, "a")` finds `(1, "a")` and not `(1, "b")` or `(1,)`. -/
example : Value.keyEq (.tuple [.int 1, .str "a"]) (.tuple [.int 1, .str "a"]) = true := rfl
example : Value.keyEq (.tuple [.int 1, .str "a"]) (.tuple [.int 1, .str "b"]) = false := rfl
example : Value.keyEq (.tuple [.int 1, .str "a"]) (.tuple [.int 1]) = false := rfl
example : Ty.Key (.tuple [.i64, .tuple [.str, .unit]]) :=
  .tuple fun κ hκ => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hκ
    rcases hκ with rfl | rfl
    · exact .int _
    · exact .tuple fun κ hκ => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hκ
        rcases hκ with rfl | rfl
        · exact .str
        · exact .unit

/-- `"hé".bytes()` is its UTF-8 bytes, two of them for `é`, and `"hé".code_points()`
its two scalar values (std.bytes-and-scalars). -/
example : ListOp.apply .bytes [.str "hé"] = .ok (Stilt.ints ("hé".toUTF8.toList.map UInt8.toNat)) := rfl
example : "hé".toUTF8.toList.map UInt8.toNat = [104, 195, 169] := by decide +kernel
example : "hé".toList.map Char.toNat = [104, 233] := by decide +kernel


/-- `127i8.checked_add(1)` doesn't fit, `100i8.checked_sub(-27)` does, and `300.to_u8()`
is out of `u8`'s range (std.integers and numbers.conversions). -/
example : ListOp.apply (.checked .add IntTy.i8.min IntTy.i8.max) [.int 127, .int 1] = .ok (.list []) :=
  rfl
example : ListOp.apply (.checked .sub IntTy.i8.min IntTy.i8.max) [.int 100, .int (-27)] =
    .ok (.list [.int 127]) := rfl
example : ListOp.apply (.narrow IntTy.u8.min IntTy.u8.max) [.int 300] = .ok (.list []) := rfl

end Stilt.Examples.Maps
