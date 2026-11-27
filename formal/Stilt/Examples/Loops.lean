import Stilt.WellTyped
import Stilt.Semantics
import Stilt.Counterexamples.Checks

/-!
# Loops and jumps

Runs of the tests of expressions.loops, expressions.break-and-continue and
expressions.loop-types, in both models of memory: a `while` that counts, a
`continue` that skips a turn, a `break` that leaves a `loop`, a `return` from
inside two loops that ends the function, a call of each, and a `return` that
ends `main`. The function that
returns from two loops is typed: its outer `loop` holds no `break` that exits
it, so it has type `Never`, which fits its result type. Each program raises
the value it shows, as in `Stilt.Examples`.
-/

namespace Stilt.Examples.Loops

/-- `a < b` on `i64`s. -/
private def lt (a b : Expr) : Expr := .op (.compare .lt .i64) [a, b]

/-- `a + b` on `i64`s. -/
private def add (a b : Expr) : Expr := .op (.arith .add .i64) [a, b]

/-- `x = e`. -/
private def set (x : Name) (e : Expr) : Expr := .assign ⟨x, []⟩ e

/-- `if c { a }`. -/
private def when (c a : Expr) : Expr := .if c .unit a .unit

/-- `fn sum(n: i64) -> i64 { var s = 0; var i = 0;
while i < n { i = i + 1; if i < 3 { continue }; s = s + i }; s }`: the integers
from 3 to `n`. -/
private def sumFrom3 : FnDecl :=
  ⟨"sum", [], [], [⟨.let, "n", .i64, none⟩], .i64, Row.pure,
    .varIn "s" .i64 (.int 0) <| .varIn "i" .i64 (.int 0) <|
      .seq (.while (lt (.var "i") (.var "n")) <|
          .seq (set "i" (add (.var "i") (.int 1))) <|
          .seq (when (lt (.var "i") (.int 3)) .continue) <|
          set "s" (add (.var "s") (.var "i")))
        (.var "s"), {}⟩

/-- The body of `first`'s inner `loop`: `if n < i { return i }; i = i + 1; break`. -/
private def turn : Expr :=
  .seq (when (lt (.var "n") (.var "i")) (.return (.var "i"))) <|
    .seq (set "i" (add (.var "i") (.int 1))) .break

/-- `fn first(n: i64) -> i64 { var i = 0; loop { loop { if n < i { return i };
i = i + 1; break } } }`: the least integer above `n`, returned from the inner
loop out of both. -/
private def firstAbove : FnDecl :=
  ⟨"first", [], [], [⟨.let, "n", .i64, none⟩], .i64, Row.pure,
    .varIn "i" .i64 (.int 0) (.loop (.loop turn)), {}⟩

private def decls : Decls := ⟨[], [], [sumFrom3, firstAbove], [], [], [], [], []⟩

/-- A call of one of the functions. -/
private def call (f : Name) (e : Expr) (result : Ty :=
  .i64) : Expr := .call (.fnRef f [] []) [.value e] result

/-- A program whose `main` raises an `i64`. -/
private def program (main : Expr) : Program := ⟨decls, .raise main, ⟨false, some .i64, [], [], none⟩, {}⟩

/-- Whether a run shows the raise of the integer `k`. -/
private def raisedInt (k : Int) : Observation → Bool
  | .raised (.int k') => k' == k
  | _ => false

/-- Both models show the raise of `k`, which the kernel checks. -/
private def raises (p : Program) (k : Int) : Bool :=
  raisedInt k (p.runCopy 64).observe && raisedInt k (p.runInPlace 64).observe

/-! ## Runs -/

/-- `sum(5)` is 3 + 4 + 5: the `continue` skips the turns where `i` is 1 or 2. -/
example : raises (program (call "sum" (.int 5))) 12 := by decide +kernel

/-- `first(12)` returns 13 from inside both loops. -/
example : raises (program (call "first" (.int 12))) 13 := by decide +kernel

/-- `first(sum(5))`: a `return` gives the value of its function's call. -/
example : raises (program (call "first" (call "sum" (.int 5)))) 13 := by decide +kernel

/-- A `return` in `main` ends it with `()` (program.main): `return; raise 1`
raises nothing. -/
example : (Program.mk decls (.seq (.return .unit) (.raise (.int 1))) ⟨false, some .i64, [], [], none⟩ {}
    |>.runCopy 8).observe = .returned .unit := rfl

/-! ## Typing -/

/-- `first` is well typed: its `return` fits `i64`, the inner `loop` has type
`()` since its `break` exits it, and the outer one has type `Never`, which fits
`i64` (expressions.loop-types and declarations.never). -/
example : firstAbove.WellTyped decls firstAbove.scope := by
  have hlt : ∀ {Γ fx} {a b : Expr}, HasType decls firstAbove.scope Γ fx a .i64 →
      HasType decls firstAbove.scope Γ fx b .i64 → HasType decls firstAbove.scope Γ fx (lt a b) .bool :=
    fun ha hb => .op .compare (.cons ha (.refl _) (.cons hb (.refl _) .nil)) (Op.keysIn_of_nil rfl) (Op.boundsIn_of_nil rfl)
  have hturn : HasType decls firstAbove.scope ((Ctx.params [] firstAbove.params).bind "i" ⟨.i64, true⟩)
      (Effects.inLoop { Effects.body Row.pure .i64 with continues := true, breaks := false })
      turn .never :=
    .seq (.if (Counterexamples.wellFormed_of_check (by decide)) (hlt (.var rfl) (.var rfl)) (.refl _)
        (.return (.var rfl) (.refl _)) (.never _) .unit (.refl _)) (.refl _)
      (.seq (.assign (.mk rfl .nil) (.op .arith (.cons (.var rfl) (.refl _)
          (.cons (.int (by decide)) (.refl _) .nil)) (Op.keysIn_of_nil rfl) (Op.boundsIn_of_nil rfl)) (.refl _)) (.refl _) (.break rfl))
  exact ⟨.never, .varIn (Counterexamples.wellFormed_of_check (by decide)) (.int (by decide)) (.refl _)
    (.loopForever (.loopBreaks hturn (.never _)) (.refl _)), .never _⟩

end Stilt.Examples.Loops
