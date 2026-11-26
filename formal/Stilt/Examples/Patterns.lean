import Stilt.Exclusivity
import Stilt.Semantics
import Stilt.WellTyped
import Stilt.Exhaustive.Decide

/-!
# Patterns

Runs of the required tests of patterns.pattern-forms, patterns.match and
expressions.if-let in both models of memory: literals, tuples, records and
nested variants, or-patterns and `_`, with the first matching arm taken, and
an `if let` as the `match` that writes it, list patterns, with their rests, and matches over
types without values. Each program raises the value it
shows, as in `Stilt.Examples`. The section on exhaustiveness derives
`Exhaustive` for arms that cover a type, the usefulness algorithm's steps
(patterns.algorithm).
-/

namespace Stilt.Examples.Patterns

/-- `type Shape = | Circle(i64) | Rect(i64, i64) | Empty`. -/
private def shape : VariantDecl :=
  ⟨"Shape", [("Circle", [.i64]), ("Rect", [.i64, .i64]), ("Empty", [])]⟩

/-- `type Opt = | Some(Shape) | None`. -/
private def opt : VariantDecl := ⟨"Opt", [("Some", [.variant "Shape"]), ("None", [])]⟩

/-- `type P = { x: i64, y: i64 }`. -/
private def point : RecordDecl := ⟨"P", [("x", .i64), ("y", .i64)]⟩

private def decls : Decls := ⟨[point], [shape, opt], [], [], [], [], []⟩

/-- A program whose `main` raises a value of `shown`. -/
private def program (shown : Ty) (main : Expr) : Program :=
  ⟨decls, main, ⟨false, some shown, [], [], none⟩, {}⟩

/-- Both models give the same observation. -/
private def agree (p : Program) (o : Observation) : Prop :=
  (p.runCopy 64).observe = o ∧ (p.runInPlace 64).observe = o

/-- An arm, with the names its pattern binds. -/
private def arm (p : Pattern) (body : Expr) : Arm := ⟨p, p.binders, body⟩

private def circle (p : Pattern) : Pattern := .variant "Shape" "Circle" [p]
private def rect (p q : Pattern) : Pattern := .variant "Shape" "Rect" [p, q]

/-! ## patterns.match: the first arm that matches runs -/

/-- `match Rect(2, 3) { Circle(r) => r, Rect(1, h) => h, Rect(w, _) => w, _ => 0 }`
raises `2`: `Rect(1, h)` doesn't match, and `Rect(w, _)` is the first that does. -/
example : agree (program .i64
    (.raise (.match (.variant "Shape" "Rect" [.int 2, .int 3]) .i64
      [arm (circle (.bind "r")) (.var "r"), arm (rect (.int 1) (.bind "h")) (.var "h"),
        arm (rect (.bind "w") .wild) (.var "w"), arm .wild (.int 0)])))
    (.raised (.int 2)) := ⟨rfl, rfl⟩

/-- Nested variants: `match Some(Circle(5)) { Some(Circle(r)) => r, Some(_) => 1,
None => 0 }` raises `5`. -/
example : agree (program .i64
    (.raise (.match (.variant "Opt" "Some" [.variant "Shape" "Circle" [.int 5]]) .i64
      [arm (.variant "Opt" "Some" [circle (.bind "r")]) (.var "r"),
        arm (.variant "Opt" "Some" [.wild]) (.int 1), arm (.variant "Opt" "None" []) (.int 0)])))
    (.raised (.int 5)) := ⟨rfl, rfl⟩

/-- Tuples and literals: `match (true, "b") { (false, _) => 0, (_, "a") => 1,
(true, s) => s.len() }` raises `1`, the length of `"b"`. -/
example : agree (program .i64
    (.raise (.match (.op .tuple [.bool true, .op (.str "b") []]) .i64
      [arm (.tuple [.bool false, .wild]) (.int 0), arm (.tuple [.wild, .str "a"]) (.int 1),
        arm (.tuple [.bool true, .bind "s"]) (.op .len [.var "s"])])))
    (.raised (.int 1)) := ⟨rfl, rfl⟩

/-- Records: `match P { x: 1, y: 2 } { P { y: 0, .. } => 0, P { x, y } => x + y }`
raises `3`. -/
example : agree (program .i64
    (.raise (.match (.record "P" [("x", .int 1), ("y", .int 2)]) .i64
      [arm (.record "P" [("y", .int 0)]) (.int 0),
        arm (.record "P" [("x", .bind "x"), ("y", .bind "y")])
          (.op (.arith .add .i64) [.var "x", .var "y"])])))
    (.raised (.int 3)) := ⟨rfl, rfl⟩

/-- Or-patterns: `match Rect(4, 9) { Circle(n) | Rect(n, _) => n, Empty => 0 }`
raises `4` (patterns.or-patterns). -/
example : agree (program .i64
    (.raise (.match (.variant "Shape" "Rect" [.int 4, .int 9]) .i64
      [arm (.or (circle (.bind "n")) (rect (.bind "n") .wild)) (.var "n"),
        arm (.variant "Shape" "Empty" []) (.int 0)])))
    (.raised (.int 4)) := ⟨rfl, rfl⟩

/-- A negative literal: `match -3 { -3 => 1, _ => 0 }` raises `1`
(numbers.negative-literals). -/
example : agree (program .i64
    (.raise (.match (.int (-3)) .i64 [arm (.int (-3)) (.int 1), arm .wild (.int 0)])))
    (.raised (.int 1)) := ⟨rfl, rfl⟩

/-! ## expressions.if-let -/

/-- `if let p = e { a } else { b }`, the `match` that writes it. -/
private def ifLet (p : Pattern) (e : Expr) (τ : Ty) (a b : Expr) : Expr :=
  .match e τ [arm p a, arm .wild b]

/-- `if let Circle(r) = Empty { r } else { 7 }` raises `7`, and on `Circle(2)`
raises `2`. -/
example : agree (program .i64
    (.raise (ifLet (circle (.bind "r")) (.variant "Shape" "Empty" []) .i64 (.var "r") (.int 7))))
    (.raised (.int 7)) := ⟨rfl, rfl⟩

example : agree (program .i64
    (.raise (ifLet (circle (.bind "r")) (.variant "Shape" "Circle" [.int 2]) .i64 (.var "r")
      (.int 7))))
    (.raised (.int 2)) := ⟨rfl, rfl⟩

/-! ## patterns.algorithm: exhaustive arms -/

/-- `Circle(_) | Rect(_, _)` and `Empty` cover `Shape`: the constructor step,
then the default steps for the payloads. -/
example : Exhaustive decls
    [[.or (circle .wild) (rect .wild .wild)], [.variant "Shape" "Empty" []]]
    [.variant "Shape"] :=
  .variant rfl fun c hc => by
    simp only [shape, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact .default (.done (by simp [specialize, defaultRow, variantRow, circle, rect]))
    · exact .default (.default (.done (by simp [specialize, defaultRow, variantRow, circle, rect])))
    · exact .done (by simp [specialize, variantRow, circle, rect])

/-- `(true, _)` and `(false, _)` cover `(bool, i64)`. -/
example : Exhaustive decls [[.tuple [.bool true, .wild]], [.tuple [.bool false, .wild]]]
    [.tuple [.bool, .i64]] :=
  .tuple (.bool (.default (.done (by simp [specialize, defaultRow, boolRow, tupleRow]))) (.default (.done (by simp [specialize, defaultRow, boolRow, tupleRow]))))

/-- The algorithm finds both derivations (`exhaustive_sound`), and without
`Empty` it finds that the arms don't cover `Shape`. -/
example : Exhaustive decls
    [[.or (circle .wild) (rect .wild .wild)], [.variant "Shape" "Empty" []]]
    [.variant "Shape"] :=
  exhaustive_sound decls 16 rfl

example : Exhaustive decls [[.tuple [.bool true, .wild]], [.tuple [.bool false, .wild]]]
    [.tuple [.bool, .i64]] :=
  exhaustive_sound decls 16 rfl

example : exhaustive decls 16 [[.or (circle .wild) (rect .wild .wild)]] [.variant "Shape"] = false :=
  rfl

/-- An `if let` is exhaustive whatever its pattern: its `else` is `_`. -/
theorem ifLet_exhaustive (D : Decls) (p : Pattern) (σ : Ty) (a b : Expr) :
    Exhaustive D (armRows [arm p a, arm .wild b]) [σ] :=
  .default (.done (by simp [specialize, armRows, arm, defaultRow]))

/-- `if let Circle(r) = Circle(2) { r } else { 7 }` has the type `i64`: its
pattern fits `Shape`, binding `r: i64`, and its arms are exhaustive. -/
example : HasType decls RowScope.closed [] ⟨Row.pure, false, false, .never, false, false⟩
    (ifLet (circle (.bind "r")) (.variant "Shape" "Circle" [.int 2]) .i64 (.var "r") (.int 7))
    .i64 := by
  have hwf : Ty.i64.WellFormed RowScope.closed :=
    ⟨fun _ h => by simp [Ty.rows] at h, fun _ h => by simp [Ty.params] at h,
      fun _ h => by simp [Ty.rows] at h⟩
  refine .match hwf (.variant rfl rfl (.cons (.int (by decide)) (.refl _) .nil))
    (ifLet_exhaustive _ _ _ _ _) ?_
  refine .cons (.variant rfl rfl (.cons .bind .nil)) rfl (by decide) (.var rfl) (.refl _) ?_
  exact .cons .wild rfl (by decide) (.int (by decide)) (.refl _) .nil

/-! ## List patterns -/

private def ints (ns : List Int) : Value := .list (ns.map .int)
private def lst (ps : List Pattern) (r : ListRest) : Pattern := .list ps r

/-- `[a, b]` matches lists of two elements only; `[a, ..]` every list of at
least one; `[a, ..rest]` binds the rest as a list, `[]` when nothing is left
(patterns.pattern-forms). -/
example : (lst [.bind "a", .bind "b"] .exact).matchOn (ints [1, 2]) = some [.int 1, .int 2] := rfl
example : (lst [.bind "a", .bind "b"] .exact).matchOn (ints [1, 2, 3]) = none := rfl
example : (lst [.bind "a"] .any).matchOn (ints [1, 2, 3]) = some [.int 1] := rfl
example : (lst [.bind "a"] .any).matchOn (ints []) = none := rfl
example : (lst [.int 1, .bind "a"] (.bind "rest")).matchOn (ints [1, 2, 3]) =
    some [.int 2, ints [3]] := rfl
example : (lst [.bind "a"] (.bind "rest")).matchOn (ints [7]) = some [.int 7, ints []] := rfl
example : (lst [] (.bind "rest")).matchOn (ints [4, 5]) = some [ints [4, 5]] := rfl

/-- `match [3, 4, 5] { [] => 0, [x] => x, [x, ..rest] => rest.len() }` raises
`2`: the first arm that matches is the last. -/
example : agree (program .i64
    (.raise (.match (.list .i64 [.int 3, .int 4, .int 5]) .i64
      [arm (lst [] .exact) (.int 0), arm (lst [.bind "x"] .exact) (.var "x"),
        arm (lst [.bind "x"] (.bind "rest")) (.op (.list .len) [.var "rest"])])))
    (.raised (.int 2)) := ⟨rfl, rfl⟩

/-- `[]` and `[x, ..rest]` cover `List<i64>`: the empty list, and every list of
at least one element (patterns.algorithm). -/
example : Exhaustive decls (armRows [arm (lst [] .exact) (.int 0),
    arm (lst [.bind "x"] (.bind "rest")) (.var "x")]) [.list .i64] :=
  exhaustive_sound decls 16 rfl

/-- `[]`, `[_]` and `[_, _, ..]` cover lists; without `[_]` the lists of one
element are left over, and `[_, ..]` alone leaves `[]`. -/
example : Exhaustive decls [[lst [] .exact], [lst [.wild] .exact], [lst [.wild, .wild] .any]]
    [.list .i64] :=
  exhaustive_sound decls 16 rfl

example : exhaustive decls 16 [[lst [] .exact], [lst [.wild, .wild] .any]] [.list .i64] = false :=
  rfl

example : exhaustive decls 16 [[lst [.wild] .any]] [.list .i64] = false := rfl

/-- Exact patterns alone never cover lists, however many lengths they list. -/
example : exhaustive decls 16 [[lst [] .exact], [lst [.wild] .exact], [lst [.wild, .wild] .exact]]
    [.list .i64] = false := rfl

/-- Lists of Booleans: `[]`, `[true, ..]` and `[false, ..]` cover them. -/
example : Exhaustive decls [[lst [] .exact], [lst [.bool true] .any], [lst [.bool false] .any]]
    [.list .bool] :=
  exhaustive_sound decls 16 rfl

/-! ## patterns.types-without-values -/

/-- `type OptNever = | Some(Never) | None`, `type Loop = | Loop(Loop)`, and
`type Holds = { n: i64, loop: Loop }`. -/
private def optNever : VariantDecl := ⟨"OptNever", [("Some", [.never]), ("None", [])]⟩
private def loopTy : VariantDecl := ⟨"Loop", [("Loop", [.variant "Loop"])]⟩
private def holds : RecordDecl := ⟨"Holds", [("n", .i64), ("loop", .variant "Loop")]⟩
private def empties : Decls := ⟨[holds], [optNever, loopTy], [], [], [], [], []⟩

/-- A match on an `Option<Never>` is exhaustive with `None` alone: `Some`'s payload
has no values. -/
example : Exhaustive empties [[.variant "OptNever" "None" []]] [.variant "OptNever"] :=
  exhaustive_sound empties 16 rfl

/-- `Loop` has no values, as `Never` has none, so no arm is needed, and neither
for a record that holds one, nor a tuple. -/
example : Exhaustive empties [] [.variant "Loop"] := exhaustive_sound empties 16 rfl
example : Exhaustive empties [] [.record "Holds"] := exhaustive_sound empties 16 rfl
example : Exhaustive empties [] [.tuple [.i64, .never]] := exhaustive_sound empties 16 rfl

/-- A list of `Never` has a value, the empty list, so it needs an arm. -/
example : exhaustive empties 16 [] [.list .never] = false := rfl
example : exhaustive empties 16 [] [.variant "OptNever"] = false := rfl

end Stilt.Examples.Patterns
