import Stilt.Generics

/-!
# Typing contexts and effects

What the typing judgment of `Stilt.Typing` knows where an expression sits: the variables in
scope, each with its type and mutability, and the row and loops around it; what a call there
must meet, and what a handler's fields must implement.
-/

namespace Stilt

/-- What a typing context knows about a variable: its type, and whether the
body may modify it. Only `var` bindings and `inout` parameters can be modified
(modes.what-can-be-modified). -/
structure Binding where
  type : Ty
  mutable : Bool

/-- A typing context. The newest binding comes first and hides older ones
with the same name (expressions.shadowing). -/
abbrev Ctx := List (Name × Binding)

namespace Ctx

/-- The binding a name refers to. -/
def lookup (Γ : Ctx) (x : Name) : Option Binding := List.lookup x Γ

/-- Adds a binding. -/
def bind (Γ : Ctx) (x : Name) (b : Binding) : Ctx := (x, b) :: Γ

/-- The context of a closure body, before its parameters: every variable is
captured by copy and can't be modified (expressions.capture). -/
def freeze (Γ : Ctx) : Ctx := Γ.map fun (x, b) => (x, { b with mutable := false })

/-- Adds a function's or closure's parameters. Only `inout` parameters can be
modified (modes.what-can-be-modified). -/
def params (Γ : Ctx) (ps : List Param) : Ctx :=
  ps.foldl (fun Γ p => Γ.bind p.name ⟨p.type, p.mode = .inout⟩) Γ

/-- Adds the names of a `when`, each a `var` of its value (shared.when). -/
def holding (Γ : Ctx) (names : List (Name × Ty)) : Ctx :=
  names.foldl (fun Γ p => Γ.bind p.1 ⟨p.2, true⟩) Γ

/-- Adds the immutable bindings of a pattern (modes.what-can-be-modified). -/
def bindAll (Γ : Ctx) (xs : List Name) (τs : List Ty) : Ctx :=
  (xs.zip τs).foldl (fun Γ (x, τ) => Γ.bind x ⟨τ, false⟩) Γ

end Ctx

/-- Where an expression sits, as far as its effects are concerned (effects.rows). -/
structure Effects where
  /-- The row its effects must fit in (effects.missing-effects). -/
  row : Row
  /-- Whether it is inside the operand of a `try`, which marks its raising
  calls, closures included (effects.marking). -/
  marked : Bool
  /-- Whether it is inside the operand of a `try … catch` and outside every
  closure literal in that operand (effects.catch-around-row-variables). The `catch` it
  belongs to is the nearest one, whose error type is `row.raise`. -/
  catching : Bool
  /-- The result type of the function or closure whose body holds it, which a
  `return` fits (expressions.closure-boundaries). The program's `main`
  expression is no body, and its result type is `Never`, which no `return`'s
  value has. -/
  result : Ty
  /-- Whether it is inside the body of a loop that a `break` may exit
  (expressions.break-and-continue and expressions.loop-types). -/
  breaks : Bool
  /-- Whether it is inside the body of a loop (expressions.break-and-continue). -/
  continues : Bool

/-- Where the body of a function or a closure whose row is `row` and whose
result type is `result` sits: outside every `try` and every loop. -/
def Effects.body (row : Row) (result : Ty) : Effects := ⟨row, false, false, result, false, false⟩

/-- The body of a loop that a `break` may exit. -/
def Effects.inLoop (fx : Effects) : Effects := { fx with breaks := true, continues := true }

/-- A call whose callee has the row `σ`, as instantiated at the call, may be
made where `fx` holds, in a body whose row variables `scope` describes. -/
structure CallAllowed (scope : RowScope) (fx : Effects) (σ : Row) : Prop where
  /-- A call contributes its callee's row, which must fit (effects.missing-effects). -/
  within : σ.Within fx.row
  /-- A call that can raise is marked by a `try` (effects.marking). -/
  marked : σ.raise.isSome = true → fx.marked = true
  /-- Inside the operand of a `catch`, a call whose row holds a row variable,
  written or implicit, could raise any error type through it (effects.catch).
  It is allowed only if the row also holds `raise<E>` and the signature pairs
  each such variable with `E` (effects.catch-around-row-variables). The row may have been written
  in the body or formed by an instantiation: the check is on the row as the
  call sees it. -/
  paired : fx.catching = true → ∀ v ∈ σ.vars, ∃ E, σ.raise = some E ∧ scope.pairs v E
  /-- No call is of the body of an operation of a handler that takes control,
  whose row holds `resume`: only a `with` calls it, as no code but such a body
  names `resume` and no closure holds one (handlers.resume-outside-operation and
  handlers.resume-at-most-once). -/
  resume : σ.resume = none

/-- The row of a `with`'s block: the row around it, with the handler's effect
(handlers.with). -/
def Row.withEffect (ρ : Row) (E : Name) : Row := { ρ with effects := E :: ρ.effects }

/-- A handler's fields, `fields` of its record type, implement each operation
of the effect `eff`: under the operation's name, a function of its argument
type that ends with its result type, or with the `with`'s type `R` for a
handler that takes control, whose row's `resume` then takes the operation's
result type and gives `R`. The row, but for its `resume`, holds what a call
where `fx` holds may perform (handlers.handler-literals, handlers.handler-types
and handlers.resuming). -/
def HandlerFits (scope : RowScope) (fx : Effects) (eff : EffectDecl)
    (fields : List (Name × Ty)) (control : Option Ty) : Prop :=
  ∀ o A B, eff.ops.lookup o = some (A, B) → ∃ ρ,
    fields.lookup o = some (.fn [(.let, A)] (control.getD B) ρ) ∧
      ρ.resume = control.map (B, ·) ∧ CallAllowed scope fx { ρ with resume := none }

end Stilt
