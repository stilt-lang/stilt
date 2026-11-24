import Stilt.Exclusivity
import Stilt.Semantics

/-!
# Tuples

Runs of the required tests of declarations.tuples-and-unit, types.field-access
and modes.overlap on tuples, in both models of memory. A tuple's field is the
field named by its position, so `.0` and `.1` of one tuple are places that
don't overlap (modes.overlap). Each program raises the value it shows, as in
`Stilt.Examples`.
-/

namespace Stilt.Examples.Tuples

/-- A program from its functions, the type of the value it shows and `main`,
whose row is `raise<shown>`. -/
private def program (fns : List FnDecl) (shown : Ty) (main : Expr) : Program :=
  ⟨⟨[], [], fns, [], [], [], []⟩, main, ⟨false, some shown, [], [], none⟩⟩

/-- Both models give the same observation. -/
private def agree (p : Program) (o : Observation) : Prop :=
  (p.runCopy 64).observe = o ∧ (p.runInPlace 64).observe = o

/-- `(e₁, …, eₙ)`. -/
private def tuple (es : List Expr) : Expr := .op .tuple es

/-- `(i64, i64)`. -/
private def pair : Ty := .tuple [.i64, .i64]

/-- `fn swap(inout x: i64, inout y: i64) { let t = x; x = y; y = t }`. -/
private def swap : FnDecl :=
  ⟨"swap", [], [], [⟨.inout, "x", .i64, none⟩, ⟨.inout, "y", .i64, none⟩], .unit, Row.pure,
    .letIn "t" .i64 (.var "x")
      (.seq (.assign ⟨"x", []⟩ (.var "y")) (.assign ⟨"y", []⟩ (.var "t")))⟩

/-- `.0` reads the first element: `let t = (1, true); raise t.0` raises `1`. -/
example : agree (program [] .i64
    (.letIn "t" (.tuple [.i64, .bool]) (tuple [.int 1, .bool true])
      (.raise (.field (.var "t") "0"))))
    (.raised (.int 1)) := ⟨rfl, rfl⟩

/-- A tuple's field is a place: `var t = (1, 2); t.1 = 5; raise t` raises
`(1, 5)`. -/
example : agree (program [] pair
    (.varIn "t" pair (tuple [.int 1, .int 2])
      (.seq (.assign ⟨"t", [.field "1"]⟩ (.int 5)) (.raise (.var "t")))))
    (.raised (.tuple [.int 1, .int 5])) := ⟨rfl, rfl⟩

/-- The body of `main` in modes/disjoint_inout: `var pairs = [(3, 4)];
swap(inout pairs[0].0, inout pairs[0].1); raise pairs`. -/
private def swapped : Expr :=
  .varIn "pairs" (.list pair) (.list pair [tuple [.int 3, .int 4]])
    (.seq (.call (.fnRef "swap" [] [])
        [.inout ⟨"pairs", [.index (.int 0), .field "0"]⟩,
          .inout ⟨"pairs", [.index (.int 0), .field "1"]⟩] .unit)
      (.raise (.var "pairs")))

/-- `.0` and `.1` of one tuple don't overlap, so the law of exclusivity
accepts the call (modes.overlap and modes.overlapping-inout). -/
example : swapped.exclusive [] = true := by decide

/-- Both models swap the elements in place: it raises `[(4, 3)]`. -/
example : agree (program [swap] (.list pair) swapped)
    (.raised (.list [.tuple [.int 4, .int 3]])) := ⟨rfl, rfl⟩


/-- An anonymous record shows without a name, its fields in the alphabetical order its
type gives them (records.field-order). -/
example : (Value.record "{ age: i64, name: str }" [("age", .int 36), ("name", .str "Ada")]).shown false
    = "{ age: 36, name: \"Ada\" }" := by decide +kernel

end Stilt.Examples.Tuples
