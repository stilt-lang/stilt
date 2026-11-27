import Stilt.Eval
import Stilt.Memory

/-!
# Scopes

Running code with variables bound, and ending the bindings however the code ends
(expressions.scope): a `let`'s or a `var`'s, which may take over the storage of a variable
at its last use (values.passing-values), and the names a pattern binds.
-/

namespace Stilt

namespace Eval

variable {σ α : Type}

/-- An outcome of a scope's body, the scope ended: the newest binding gone
from its state, and from a performance's rest when it ends (expressions.scope). -/
def _root_.Stilt.Outcome.unbind (M : Memory σ) : Outcome σ α → Outcome σ α
  | .done a s' => .done a (M.unbind s')
  | .raised e s' => .raised e (M.unbind s')
  | .jumped j s' => .jumped j (M.unbind s')
  | .panicked k s' => .panicked k (M.unbind s')
  | .performed op v s' k => .performed op v (M.unbind s') fun w x => (k w x).unbind M
  | .outOfFuel => .outOfFuel
  | .stuck => .stuck

/-- Runs `m` with `x` bound to `v`, and ends the binding however `m` ends
(expressions.scope). -/
def withVar (M : Memory σ) (x : Name) (v : Value) (m : Eval σ α) : Eval σ α := fun s =>
  (m (M.bind s x v)).unbind M

/-- Binds `x` to the value `v` of its initializer `init`. When `init` is the
last use of a variable, the model may hand that variable's storage over
(values.let-and-var and values.passing-values). -/
def _root_.Stilt.Memory.bindInit (M : Memory σ) (s : σ) (x : Name) (init : Expr) (v : Value) :
    σ :=
  match init with
  | .move y => M.bindMoved s x y v
  | _ => M.bind s x v

/-- Runs `m` with `x` bound to the value `v` of its initializer `init`, as
`let` and `var` do, and ends the binding however `m` ends (expressions.scope). -/
def withInit (M : Memory σ) (x : Name) (init : Expr) (v : Value) (m : Eval σ α) :
    Eval σ α := fun s =>
  (m (M.bindInit s x init v)).unbind M

/-- An initializer that isn't the last use of a variable binds a new one. -/
theorem withInit_eq_withVar (M : Memory σ) (x : Name) {init : Expr} (h : ∀ y, init ≠ .move y)
    (v : Value) (m : Eval σ α) : withInit M x init v m = withVar M x v m := by
  cases init <;> first | exact absurd rfl (h _) | rfl

/-- Runs `m` with each name bound to its value, the first one outermost. -/
def withVars (M : Memory σ) : List (Name × Value) → Eval σ α → Eval σ α
  | [], m => m
  | (x, v) :: bindings, m => withVar M x v (withVars M bindings m)

end Eval

end Stilt
