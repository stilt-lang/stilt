import Stilt.Semantics

/-!
# Shared values

Runs, in both models of memory, of programs with shared values as the export writes them
(shared.std-sync and shared.when): `Shared.new(v)` makes a cell of the world holding `v`
and gives its handle, and a `when` holds the cells its handles name, panicking with
`deadlock` if one is held, binds each name to its cell's value, runs its block and puts
each value back. Two names whose handles are equal are one variable: the export tests the
handles and runs the block holding one cell for both, so a write through one is read
through the other (shared.names-that-may-be-one-place), as in
`conformance/shared/transfers.lt`; and a `when` on a value held by a `when` around it,
through a call, panics with `deadlock`, as in `conformance/held/deadlock.lt`
(shared.when-on-value-already-held).
-/

namespace Stilt.Examples.Shared

private def account : Ty := .record "Account" []

private def add (a b : Expr) : Expr := .op (.arith .add .i64) [a, b]

/-- `Shared.new(Account { balance: n })` bound to `h` in `body`. -/
private def shared (h : Name) (n : Int) (body : Expr) : Expr :=
  .letIn h (.shared account)
    (.op (.world (.sharedNew account)) [.record "Account" [] [("balance", .int n)]]) body

/-- `when h { block }`, its name `x`. -/
private def when1 (h x : Name) (block : Expr) : Expr := .held [(x, account)] [.var h] block

/-- `when c, d { block }`: when the handles are equal, the block with both names one
variable, `pc`; otherwise each value held under its own. -/
private def when2 (τ : Ty) (one two : Expr) : Expr :=
  .if (.op .sameCell [.var "c", .var "d"]) τ (when1 "c" "pc" one)
    (.held [("pc", account), ("pd", account)] [.var "c", .var "d"] two)

/-- `fn bump(c: Shared<Account>) { when c { c.balance += 1 } }`. -/
private def bump : FnDecl :=
  ⟨"bump", [], [], [⟨.let, "c", .shared account, .none⟩], .unit, Row.pure,
    when1 "c" "pc"
      (.assign ⟨"pc", [.field "balance"]⟩ (add (.field (.var "pc") "balance") (.int 1))), {}⟩

private def decls : Decls := ⟨[⟨"Account", [("balance", .i64)], []⟩], [], [bump], [], [], [], [], []⟩

private def program (body : Expr) : Program :=
  ⟨decls, body, ⟨false, Option.some .i64, [], [], .none⟩, {}⟩

private def raisesBoth (p : Program) (k : Int) : Bool :=
  (match (p.runCopy 64).observe with | .raised (.int k') => k == k' | _ => false) &&
  (match (p.runInPlace 64).observe with | .raised (.int k') => k == k' | _ => false)

private def panicsBoth (p : Program) (k : PanicKind) : Bool :=
  (match (p.runCopy 64).observe with | .panicked k' => k == k' | _ => false) &&
  (match (p.runInPlace 64).observe with | .panicked k' => k == k' | _ => false)

private def bumpCall : Expr := .call (.fnRef "bump" [] []) [.value (.var "c")] .unit

/-! ## Runs -/

/-- `let c = Shared.new(Account { balance: 5 }); let d = c;
when c, d { c.balance += 2; d.balance }` gives 7: the two names are one place. -/
example : raisesBoth (program (shared "c" 5 (.letIn "d" (.shared account) (.var "c")
    (.raise (when2 .i64
      (.seq (.assign ⟨"pc", [.field "balance"]⟩ (add (.field (.var "pc") "balance") (.int 2)))
        (.field (.var "pc") "balance"))
      (.seq (.assign ⟨"pc", [.field "balance"]⟩ (add (.field (.var "pc") "balance") (.int 2)))
        (.field (.var "pd") "balance"))))))) 7 := by
  decide +kernel

/-- `bump(c)` twice, then `when c { c.balance }`, gives 2: a call reaches the value through
its handle, and each `when` puts the value back in its cell. -/
example : raisesBoth (program (shared "c" 0 (.seq bumpCall (.seq bumpCall
    (.raise (when1 "c" "pc" (.field (.var "pc") "balance"))))))) 2 := by
  decide +kernel

/-- `when c { bump(c) }` panics with `deadlock`: the outer `when` holds the cell, so the
inner one finds it held. -/
example : panicsBoth (program (shared "c" 0 (when1 "c" "pc" bumpCall))) .deadlock := by
  decide +kernel

/-- `when c { c.balance = 3; raise 0 }`, caught, then `when c { c.balance }`, gives 3: a
`when` left by a raise puts its value back and lets the cell go. -/
example : raisesBoth (program (shared "c" 0 (.seq
    (.tryCatch (when1 "c" "pc" (.seq (.assign ⟨"pc", [.field "balance"]⟩ (.int 3))
      (.raise (.int 0)))) .i64 "e" .unit .unit)
    (.raise (when1 "c" "pc" (.field (.var "pc") "balance")))))) 3 := by
  decide +kernel

end Stilt.Examples.Shared
