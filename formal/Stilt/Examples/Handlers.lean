import Stilt.Ends.Theorem

/-!
# Effects and handlers

Runs of the programs of `conformance/handlers/resuming.lt` and
`conformance/handlers/basic.lt`, in both models of memory: a handler that takes
control and whose body resumes, then goes on once the rest of the block has
ended (handlers.resuming); one whose body never resumes, which ends the `with`
with its value, so the rest of the block never runs; a handler hidden by an
inner one of its effect, whose body performs on the outer one (handlers.with);
a performance across calls (handlers.performing-operation); and a body that
writes, then raises, whose line stays written. A handler is a
record of closures, one for each operation. Each program raises the list of
the values it shows, as in `Stilt.Examples`.

The facts of handlers (handlers.implicit-effects-and-capabilities): a
performance adds no `panic`, and these programs are panic-free, while a clause
whose body divides by zero isn't; a performance is a site of `div` and a `with`
adds none of its own, so a `with` whose block performs nothing is free of
`div`, and its program is total.
-/

namespace Stilt.Examples.Handlers

private def ask : Operation := ⟨"Ask", "ask"⟩
private def fail : Operation := ⟨"Fail", "fail"⟩

/-- `a + b` and `a < b` on `i64`s. -/
private def add (a b : Expr) : Expr := .op (.arith .add .i64) [a, b]
private def lt (a b : Expr) : Expr := .op (.compare .lt .i64) [a, b]

/-- A row of the effect `E`. -/
private def row (E : Name) : Row := ⟨false, none, [], [E], none⟩

/-- The row of a body that takes control in a handler of the type `R`, whose
operation gives `B`. -/
private def controlRow (B R : Ty) : Row := ⟨false, none, [], [], some (B, R)⟩

/-- A handler of `Ask` or `Fail`: the record of its one closure. -/
private def handler (R op : Name) (A : Ty) (x : Name) (r : Row) (body : Expr) : Expr :=
  .record R [] [(op, .closure [⟨.let, x, A, none⟩] .i64 r body)]

/-- `handler Ask -> i64 { fn ask() -> i64 { let r = resume(10); r } }`. -/
private def around : Expr :=
  handler "AroundAsk" "ask" .unit "_" (controlRow .i64 .i64)
    (.letIn "r" .i64 (.perform Operation.resume (.int 10)) (.var "r"))

/-- `handler Fail -> i64 { fn fail(n: i64) -> i64 { -1 } }`, which never resumes. -/
private def toDefault : Expr := handler "ToDefault" "fail" .i64 "n" (controlRow .i64 .i64) (.int (-1))

/-- `handler Ask { fn ask() -> i64 { k } }`. -/
private def answer (k : Int) : Expr := handler "Answer" "ask" .unit "_" Row.pure (.int k)

/-- `handler Ask { fn ask() -> i64 { 10 + Ask.ask() } }`, which performs on the
handler outside it. -/
private def inner : Expr := handler "Answer" "ask" .unit "_" (row "Ask") (add (.int 10) (.perform ask .unit))

/-- `fn twice_asked() -> i64 / Ask { Ask.ask() + Ask.ask() }`,
`fn checked(n: i64) -> i64 / Fail { if n < 0 { Fail.fail(n) } else { n + n } }`,
`fn once() -> i64 / Ask { Ask.ask() + 1 }` and
`fn deep() -> i64 / Ask { once() + 100 }`. -/
private def fns : List FnDecl := [
  ⟨"twice_asked", [], [], [], .i64, row "Ask", add (.perform ask .unit) (.perform ask .unit), {}⟩,
  ⟨"checked", [], [], [⟨.let, "n", .i64, none⟩], .i64, row "Fail",
    .if (lt (.var "n") (.int 0)) .i64 (.perform fail (.var "n")) (add (.var "n") (.var "n")), {}⟩,
  ⟨"once", [], [], [], .i64, row "Ask", add (.perform ask .unit) (.int 1), {}⟩,
  ⟨"deep", [], [], [], .i64, row "Ask", add (.call (.fnRef "once" [] []) [] .i64) (.int 100), {}⟩]

private def decls : Decls :=
  ⟨[⟨"AroundAsk", [("ask", .fn [(.let, .unit)] .i64 (controlRow .i64 .i64))], []⟩,
      ⟨"ToDefault", [("fail", .fn [(.let, .i64)] .i64 (controlRow .i64 .i64))], []⟩,
      ⟨"Answer", [("ask", .fn [(.let, .unit)] .i64 (row "Ask"))], []⟩],
    [], fns, [], [], [], [⟨"Ask", [("ask", .unit, .i64)]⟩, ⟨"Fail", [("fail", .i64, .i64)]⟩], []⟩

/-- A call of one of the functions. -/
private def call (f : Name) (args : List Expr) (result : Ty :=
  .i64) : Expr := .call (.fnRef f [] []) (args.map .value) result

/-- A program whose `main` raises the list of `es`' values. -/
private def program (es : List Expr) : Program :=
  ⟨decls, .raise (.list .i64 es), ⟨false, some (.list .i64), [], [], none⟩, {}, {}⟩

/-- Whether values are the integers `ks`. -/
private def areInts : List Value → List Int → Bool
  | [], [] => true
  | .int k :: vs, k' :: ks => k == k' && areInts vs ks
  | _, _ => false

/-- Whether a run shows the raise of the list of `ks`. -/
private def raisedInts (ks : List Int) : Observation → Bool
  | .raised (.list vs) => areInts vs ks
  | _ => false

/-- Both models show the raise of the list of `ks`, which the kernel checks. -/
private def raises (p : Program) (ks : List Int) : Bool :=
  raisedInts ks (p.runCopy 64).observe && raisedInts ks (p.runInPlace 64).observe

/-! ## Runs -/

/-- Each body resumes with 10 and gives what the rest of the block ends with,
so `twice_asked()` is 20; a body that never resumes ends the `with` with -1,
and `+ 100` never runs; `checked(4)` performs nothing and is 8. -/
example : raises (program [.withH "Ask" true around (call "twice_asked" []),
    .withH "Fail" true toDefault (add (call "checked" [.int (-3)]) (.int 100)),
    .withH "Fail" true toDefault (call "checked" [.int 4])]) [20, -1, 8] := by decide +kernel

/-- `Ask.ask()` gives 1 under a handler of 1, and 11 under an inner handler
that hides it and asks the outer one. -/
example : raises (program [.withH "Ask" false (answer 1) (.perform ask .unit),
    .withH "Ask" false (answer 1) (.withH "Ask" false inner (.perform ask .unit))]) [1, 11] := by
  decide +kernel

/-- A performance crosses calls: the handler around `deep()` answers the one
that its callee `once()` performs, and the code after each call runs on its
value. -/
example : raises (program [.withH "Ask" false (answer 5) (call "deep" [])]) [106] := by
  decide +kernel

/-- `handler Ask { fn ask() -> i64 / raise<List<i64>> { print("asked"); raise [1] } }`,
whose body writes, then raises out of the `with`. -/
private def loud : Expr :=
  handler "Answer" "ask" .unit "_" ⟨false, some (.list .i64), [], [], none⟩
    (.seq (.op (.world (.write false true)) [.op (.str "asked") []]) (.raise (.list .i64 [.int 1])))

/-- Whether both models end with `out` written to the output and nothing to standard error. -/
private def writes (p : Program) (out : String) : Bool :=
  (p.runCopy 64).output == some ⟨out, ""⟩ && (p.runInPlace 64).output == some ⟨out, ""⟩

/-- What a handler's body writes stays written however the body ends: the body raises
out of the `with`, and the run shows the raise with the line the body wrote before it
(program.output-flushing and handlers.resuming-keeps-exclusivity). -/
example : raises (program [.withH "Ask" false loud (.perform ask .unit)]) [1] ∧
    writes (program [.withH "Ask" false loud (.perform ask .unit)]) "asked\n" := by decide +kernel

/-! ## Facts -/

/-- `handler Ask { fn ask() -> i64 { 1 / 0 } }`. -/
private def byZero : Expr :=
  handler "Answer" "ask" .unit "_" Row.pure (.op (.arith .div .i64) [.int 1, .int 0])

/-- The programs above are panic-free: their performances, their `with`s and
their handlers' bodies add no `panic`. -/
example : (program [.withH "Ask" true around (call "twice_asked" []),
    .withH "Fail" true toDefault (add (call "checked" [.int (-3)]) (.int 100)),
    .withH "Ask" false (answer 1) (.withH "Ask" false inner (.perform ask .unit)),
    .withH "Ask" false (answer 5) (call "deep" [])]).PanicFree := ⟨by decide, rfl⟩

/-- A handler's body is code of the function that writes it: dividing by zero
there adds `panic`. -/
example : ¬ (program [.withH "Ask" false byZero (.perform ask .unit)]).PanicFree := fun h => nomatch h.2

/-- A program without functions, whose `main` raises the list of `es`' values. -/
private def bare (es : List Expr) : Program :=
  ⟨{ decls with functions := [] }, .raise (.list .i64 es), ⟨false, some (.list .i64), [], [], none⟩, {}, {}⟩

/-- A `with` whose block performs nothing adds no `div`, and its program, free of
`panic` too, is total; a performance is a site of `div`. -/
example : (bare [.withH "Ask" false (answer 1) (.int 7)]).divFree = true := rfl
example : raises (bare [.withH "Ask" false (answer 1) (.int 7)]) [7] := by decide +kernel
example : (bare [.withH "Ask" false (answer 1) (.int 7)]).DivFree := Program.divFree_spec rfl
example : (bare [.withH "Ask" false (answer 1) (.int 7)]).PanicFree := ⟨by decide, rfl⟩
example : (bare [.withH "Ask" false (answer 1) (.perform ask .unit)]).divFree = false := rfl

end Stilt.Examples.Handlers
