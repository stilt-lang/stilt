import Stilt.Exclusivity
import Stilt.Semantics

/-!
# Projections

Runs, in both models of memory, of projections as the export writes them
(projections.call-is-place and projections.when-projection-runs). The caller's access
to a projection's call is a closure literal that takes the yielded place `inout`, and the
projection is a function of its own for that access: its `yield p` calls the access with
`p`, keeping its value in a one-element list that the body ends with. So the access
happens on the projection's place, and in place on the caller's storage; the body resumes
after it, and the `inout` arguments are written back when it ends, or when the access
raises, which leaves the projection without resuming (projections.raising-during-access).
Two projections' calls that hold one source, as in `swap(inout at(inout xs, 0), inout
at(inout xs, 1))`, become a call whose `inout` arguments overlap, which the law of
exclusivity rejects as modes.overlapping-inout does.

A view that writes is the copy of its part that its binding holds, written back into its
source element by element when the binding's scope ends, or when a raise leaves it
(projections.writable-views and projections.what-view-writes); `view.split` copies two
parts, which its function takes `inout`.
-/

namespace Stilt.Examples.Projections

private def ints : Ty := .list .i64
private def raising : Row := ⟨false, some .i64, [], [], none⟩

private def add (a b : Expr) : Expr := .op (.arith .add .i64) [a, b]
private def at0 (xs : Name) (i : Int) : Expr := .index (.var xs) (.int i)

/-- `fn at(inout xs: List<i64>, i: i64) -> inout i64 { yield xs[i]; xs[0] = xs[i] }`,
written for an access of type `fn(inout i64) -> ()` with the row `row`. -/
private def atFor (name : Name) (row : Row) : FnDecl :=
  ⟨name, [], [], [⟨.inout, "xs", ints, none⟩, ⟨.let, "i", .i64, none⟩,
      ⟨.let, "k", .fn [(.inout, .i64)] .unit row, none⟩], .unit, row,
    .varIn "r" (.list .unit) (.list .unit [])
      (.seq (.assign ⟨"r", []⟩ (.list .unit [.call (.var "k") [.inout ⟨"xs", [.index (.var "i")]⟩] .unit]))
        (.seq (.assign ⟨"xs", [.index (.int 0)]⟩ (.index (.var "xs") (.var "i")))
          (.index (.var "r") (.int 0)))), {}⟩

/-- The same projection written for an access that threads a place of the caller's, of
type `fn(inout i64, inout i64) -> ()`. -/
private def atThreading : FnDecl :=
  ⟨"atThreading", [], [], [⟨.inout, "xs", ints, none⟩, ⟨.let, "i", .i64, none⟩,
      ⟨.inout, "t", .i64, none⟩, ⟨.let, "k", .fn [(.inout, .i64), (.inout, .i64)] .unit Row.pure, none⟩],
    .unit, Row.pure,
    .varIn "r" (.list .unit) (.list .unit [])
      (.seq (.assign ⟨"r", []⟩ (.list .unit [.call (.var "k")
          [.inout ⟨"xs", [.index (.var "i")]⟩, .inout ⟨"t", []⟩] .unit]))
        (.index (.var "r") (.int 0))), {}⟩

/-- `fn swap(inout a: i64, inout b: i64)`. -/
private def swap : FnDecl :=
  ⟨"swap", [], [], [⟨.inout, "a", .i64, none⟩, ⟨.inout, "b", .i64, none⟩], .unit, Row.pure,
    .letIn "x" .i64 (.var "a") (.seq (.assign ⟨"a", []⟩ (.var "b")) (.assign ⟨"b", []⟩ (.var "x"))), {}⟩

private def decls : Decls := ⟨[], [], [atFor "at" Row.pure, atFor "atRaising" raising, atThreading, swap],
  [], [], [], []⟩

private def program (main : Expr) : Program := ⟨decls, main, raising, {}⟩

/-- `var xs = [1, 2, 3]` around `body`. -/
private def withList (body : Expr) : Expr :=
  .varIn "xs" ints (.list .i64 [.int 1, .int 2, .int 3]) body

private def sum : Expr := add (add (at0 "xs" 0) (at0 "xs" 1)) (at0 "xs" 2)

private def raisesBoth (p : Program) (k : Int) : Bool :=
  (match (p.runCopy 64).observe with | .raised (.int k') => k == k' | _ => false) &&
  (match (p.runInPlace 64).observe with | .raised (.int k') => k == k' | _ => false)

/-! ## Runs -/

/-- `at(inout xs, 1) = 9` gives `[9, 9, 3]`: the access writes the yielded place, then the
body resumes and copies it into `xs[0]`. -/
example : raisesBoth (program (withList
    (.seq (.call (.fnRef "at" [] []) [.inout ⟨"xs", []⟩, .value (.int 1),
        .value (.closure [⟨.inout, "x", .i64, none⟩] .unit Row.pure (.assign ⟨"x", []⟩ (.int 9)))] .unit)
      (.raise sum)))) 21 := by
  decide +kernel

/-- An access that writes `5` and raises `7` leaves the projection without resuming:
`xs` is `[1, 5, 3]`, its first element never set (projections.raising-during-access). -/
example : raisesBoth (program (withList
    (.tryCatch
      (.call (.fnRef "atRaising" [] []) [.inout ⟨"xs", []⟩, .value (.int 1),
        .value (.closure [⟨.inout, "x", .i64, none⟩] .unit raising
          (.seq (.assign ⟨"x", []⟩ (.int 5)) (.raise (.int 7))))] .unit)
      .i64 "e" (.raise (add sum (.var "e"))) .unit))) 16 := by
  decide +kernel

/-- `swap(inout at(inout xs, 0), inout t)`, the caller's `t` threaded through the
projection, gives `xs = [5, 2, 3]` and `t = 1`. -/
example : raisesBoth (program (withList (.varIn "t" .i64 (.int 5)
    (.seq (.call (.fnRef "atThreading" [] []) [.inout ⟨"xs", []⟩, .value (.int 0),
        .inout ⟨"t", []⟩,
        .value (.closure [⟨.inout, "x", .i64, none⟩, ⟨.inout, "u", .i64, none⟩] .unit Row.pure
          (.call (.fnRef "swap" [] []) [.inout ⟨"x", []⟩, .inout ⟨"u", []⟩] .unit))] .unit)
      (.raise (add (.op (.arith .mul .i64) [sum, .int 10]) (.var "t"))))))) 101 := by
  decide +kernel

/-! ## Views that write -/

private def slice (xs : Expr) (a b : Expr) : Expr := .op (.list .slice) [xs, a, b]

/-- The part `v` written back into `xs` from the offset `off`, element by element. -/
private def writeBack (v : Name) (off : Int) (rest : Expr) : Expr :=
  .varIn "w" ints (.var "xs")
    (.seq (.for "j" .i64 (.op (.list (.range false)) [.int 0, .op (.list .len) [.var v]])
        (.assign ⟨"w", [.index (add (.int off) (.var "j"))]⟩ (.index (.var v) (.var "j"))))
      (.seq (.assign ⟨"xs", []⟩ (.var "w")) rest))

/-- `{ var v = view.into(inout xs, 1, 3); v[0] = 10; v[1] += 5 }` gives `[1, 10, 8, 4]`. -/
example : raisesBoth (program (.varIn "xs" ints (.list .i64 [.int 1, .int 2, .int 3, .int 4])
    (.varIn "v" ints (slice (.var "xs") (.int 1) (.int 3))
      (.seq (.assign ⟨"v", [.index (.int 0)]⟩ (.int 10))
        (.seq (.assign ⟨"v", [.index (.int 1)]⟩ (add (at0 "v" 1) (.int 5)))
          (writeBack "v" 1 (.raise (add sum (at0 "xs" 3))))))))) 23 := by
  decide +kernel

/-- `view.split(inout xs, 1, |inout a, inout b| { a[0] = 0; b[1] = 9; raise 7 })`, caught:
the parts are written back before the raise leaves, so `xs` is `[0, 2, 9]`. -/
example : raisesBoth (program (withList
    (.tryCatch
      (.varIn "a" ints (slice (.var "xs") (.int 0) (.int 1))
        (.varIn "b" ints (slice (.var "xs") (.int 1) (.op (.list .len) [.var "xs"]))
          (.tryCatch
            (.seq (.assign ⟨"a", [.index (.int 0)]⟩ (.int 0))
              (.seq (.assign ⟨"b", [.index (.int 1)]⟩ (.int 9)) (.raise (.int 7))))
            .i64 "e" (writeBack "a" 0 (writeBack "b" 1 (.raise (.var "e")))) .unit)))
      .i64 "e" (.raise (add sum (.var "e"))) .unit))) 18 := by
  decide +kernel

/-! ## Exclusivity -/

/-- `swap(inout at(inout xs, 0), inout at(inout ys, 0))`, written: the first projection
threads `ys`, which the second takes. -/
private def twoSources (ys : Name) : Expr :=
  .call (.fnRef "atThreading" [] []) [.inout ⟨"xs", []⟩, .value (.int 0), .inout ⟨ys, []⟩,
    .value (.closure [⟨.inout, "a", .i64, none⟩, ⟨.inout, "zs", ints, none⟩] .unit Row.pure
      (.call (.fnRef "atThreading" [] []) [.inout ⟨"zs", []⟩, .value (.int 0), .inout ⟨"a", []⟩,
        .value (.closure [⟨.inout, "b", .i64, none⟩, ⟨.inout, "c", .i64, none⟩] .unit Row.pure
          (.call (.fnRef "swap" [] []) [.inout ⟨"c", []⟩, .inout ⟨"b", []⟩] .unit))] .unit))] .unit

/-- Of two sources, the law accepts it. -/
example : (twoSources "ys").exclusive [] = true := by decide

/-- Of one source, `swap(inout at(inout xs, 0), inout at(inout xs, 1))`, the first
projection takes `xs` and threads it too, so the call's `inout` arguments overlap (E0402,
projections.when-projection-runs). -/
example : (twoSources "xs").exclusive [] = false := by decide

end Stilt.Examples.Projections
