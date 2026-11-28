import Stilt.Handling.WithPaired
import Stilt.Typing.Tasks

/-!
# Handlers around a caller's effects

The check of handlers.with-pairing on a function that calls its non-escaping parameter `g`
inside a `with` of `Log`: E0516 when the signature doesn't pair `g`'s row variable with `Log`,
accepted when it does, and accepted when the call is inside a closure literal in the block. Then
trait constants: a read of one is the value of the constant the program declares for it.
-/

namespace Stilt.Examples.WithPaired

/-- `fn run(g: fn() / ρ) / ρ` whose body is `body`, `ρ` holding `g`'s implicit variable `r` and
the effects `es`. -/
private def run (es : List Name) (body : Expr) : FnDecl :=
  let ρ : Row := ⟨false, none, ["r"], es, none⟩
  ⟨"run", [], ["r"], [⟨.let, "g", .fn [] .unit ρ, some "r"⟩], .unit, ρ, body, {}⟩

private def callG : Expr := .call (.var "g") [] .unit

private def decls : Decls := ⟨[], [], [], [], [], [], [⟨"Log", []⟩], []⟩

private def check (d : FnDecl) : Bool :=
  d.body.withPaired decls d (d.params.map fun q => (q.name, q.type)) none

/-- `with h { g() }` where `g`'s row doesn't hold `Log`: E0516. -/
example : check (run [] (.withH "Log" false .unit callG)) = false := by decide

/-- The signature pairs `r` with `Log`: accepted. -/
example : check (run ["Log"] (.withH "Log" false .unit callG)) = true := by decide

/-- The call is inside a closure literal in the block: the rule skips it. -/
example : check (run [] (.withH "Log" false .unit (.closure [] .unit Row.pure callG))) = true := by
  decide

/-- traits.trait-constants: the constant `Zero for i64.ZERO`, and its read. -/
example : TaskForm ⟨[], [], [], [], [], [], [], [⟨"Zero for i64.ZERO", .i64, .int 0⟩]⟩
    (.traitConst "Zero for i64.ZERO") (.int 0) .i64 :=
  .traitConst rfl .value

end Stilt.Examples.WithPaired
