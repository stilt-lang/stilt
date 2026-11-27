import Stilt.Semantics
import Stilt.Typing.Else

/-!
# Let-else and the fallback, run

A let-else and an `Option` fallback run as the `match` each means, one step of fuel later, in
every model of memory: `eval_form`. So `let P = e else x` runs `x` when the value of `e` doesn't
match `P` and the rest of its block with the bindings of `P` when it does (patterns.let-else),
and `e₁ else e₂` gives the value inside a `Some` of `e₁`, running `e₂` only on a `None`
(expressions.option-fallback).
-/

namespace Stilt

variable {σ : Type} (D : Decls) (M : Memory σ) (n : Nat)

/-- A form runs as its meaning. -/
theorem eval_form (k : Form) (m : Expr) : eval D M (n + 1) (.form k m) = eval D M n m := rfl

/-- A let-else runs as `match e { P => rest, _ => x }`. -/
theorem eval_letElse (p : Pattern) (bs : List Name) (e : Expr) (τ : Ty) (rest x : Expr) :
    eval D M (n + 1) (Expr.letElse p bs e τ rest x) =
      eval D M n (.match e τ [⟨p, bs, none, rest⟩, ⟨.wild, [], none, x⟩]) := rfl

/-- An `Option` fallback runs as `match e₁ { Some(v) => v, _ => e₂ }`. -/
theorem eval_orElse (T : Name) (τ : Ty) (v : Name) (e₁ e₂ : Expr) :
    eval D M (n + 1) (Expr.orElse T τ v e₁ e₂) =
      eval D M n (.match e₁ τ [⟨.variant T "Some" [.bind v], [v], none, .var v⟩, ⟨.wild, [], none, e₂⟩]) :=
  rfl

end Stilt
