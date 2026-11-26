import Stilt.Declarations

/-!
# Rows and types

Effect rows and the relations on them that effects.rows and effects.function-values defines: one row fitting
within another (effects.missing-effects), the union of the rows of branches (effects.function-value-unions), a function
value fitting a function type with a larger row (effects.function-values), the rows a type holds, and the
instantiation of row variables, written and implicit, in a type at a use (effects.row-variables and
effects.inference).
-/

namespace Stilt

namespace Row

/-- The row of code with no explicit effects (effects.rows). -/
def pure : Row := ⟨false, none, [], [], none⟩

/-- `a` fits within `b`: every element of `a` is an element of `b` (effects.missing-effects). A `raise<E>` label fits only a label with the same `E`, since a row
holds one at most (effects.one-error-type). -/
structure Within (a b : Row) : Prop where
  io : a.io = true → b.io = true
  raise : ∀ E, a.raise = some E → b.raise = some E
  vars : ∀ v ∈ a.vars, v ∈ b.vars
  effects : ∀ E ∈ a.effects, E ∈ b.effects
  resume : ∀ p, a.resume = some p → b.resume = some p

/-- Two rows with the same elements. Elements are unordered (effects.rows),
so a row is the set of its elements, whatever the order of its variables. -/
structure Same (a b : Row) : Prop where
  io : a.io = b.io
  raise : a.raise = b.raise
  vars : ∀ v, v ∈ a.vars ↔ v ∈ b.vars
  effects : ∀ E, E ∈ a.effects ↔ E ∈ b.effects
  resume : a.resume = b.resume

/-- The row in which the operand of a `try … catch` runs: the row around it,
with the `raise` label replaced by one for the error type that the `catch`
handles (effects.catch). -/
def withRaise (ρ : Row) (E : Ty) : Row := { ρ with raise := some E }

/-- Two rows can be joined into one row: they agree on the error type where
both have one (effects.one-error-type). A row that a body forms may hold several row
variables (effects.row-variables), so any two sets of variables join. -/
structure Compatible (a b : Row) : Prop where
  raise : ∀ E E', a.raise = some E → b.raise = some E' → E = E'
  resume : ∀ p p', a.resume = some p → b.resume = some p' → p = p'

/-- The union of two rows, which the common type of two branches has when the
branches are function values (effects.function-value-unions). It is the least upper bound
when the rows are compatible. -/
def union (a b : Row) : Row :=
  ⟨a.io || b.io, a.raise <|> b.raise, a.vars ++ b.vars, a.effects ++ b.effects, a.resume <|> b.resume⟩

end Row

/-- A value of type `σ` can be used where a value of type `τ` is expected.
The types are equal, or `σ` is `Never`, which converts to any type (declarations.never), or both are function types that differ only in their rows, and the
row grows (effects.function-values). Function types inside other types must match
exactly, so the relation never looks below the outermost function type. -/
inductive Fits : Ty → Ty → Prop
  | refl (τ : Ty) : Fits τ τ
  | never (τ : Ty) : Fits .never τ
  | fn {params : List (Mode × Ty)} {result : Ty} {a b : Row} :
      a.Within b → Fits (.fn params result a) (.fn params result b)

/-! ## Row variables -/

mutual

/-- Every row in a type, at every depth, including the rows inside error
types. -/
def Ty.rows : Ty → List Row
  | .list τ => τ.rows
  | .tuple τs => tysRows τs
  | .record _ τs | .variant _ τs => tysRows τs
  | .map κ τ => κ.rows ++ τ.rows
  | .set τ => τ.rows
  | .view τ => τ.rows
  | .shared τ => τ.rows
  | .fn ps r ρ => paramRows ps ++ r.rows ++ ρ.rows
  | _ => []

/-- Every row in a list of types. -/
def tysRows : List Ty → List Row
  | [] => []
  | τ :: τs => τ.rows ++ tysRows τs

/-- Every row in a list of parameter types. -/
def paramRows : List (Mode × Ty) → List Row
  | [] => []
  | (_, τ) :: ps => τ.rows ++ paramRows ps

/-- A row, followed by the rows inside its error type. -/
def Row.rows : Row → List Row
  | ⟨io, some E, vs, es, r⟩ => ⟨io, some E, vs, es, r⟩ :: E.rows
  | ⟨io, none, vs, es, r⟩ => [⟨io, none, vs, es, r⟩]

end

/-- A type with no row variable in it. The types of record fields and of
variant payloads are closed, because only functions declare row variables
(effects.row-variables). -/
def Ty.Closed (τ : Ty) : Prop := ∀ ρ ∈ τ.rows, ρ.vars = []

/-- What a function's body knows about its row variables.

`vars` are the row variables in scope: those the function declares and the
implicit ones of its non-escaping parameters (effects.row-variables and effects.non-escaping-parameters).
`pairs v E` says that the function's signature pairs `v` with `E` (effects.paired-row-variables), so that `v` adds no error type other than `E`. Inside a `catch` that
handles `E`, a call through `v` is allowed only then (effects.catch-around-row-variables). A use of
a function that pairs one of its own variables with `E`, and instantiates it
with a row that holds `v`, is allowed only if `passOn v E` (effects.passing-to-paired-variables).

The model states the rules as they stand with `pairs` and `passOn` the
signature's pairs. Making `pairs` or `passOn` true everywhere drops the rule
that reads it. That is how `Stilt.WellTyped` states the earlier rules, whose
unsoundness `Stilt.Counterexamples` proves.

`types` are the function's type parameters, with their bounds, which are all
that the body knows of them (traits.unsatisfied-bounds). -/
structure RowScope where
  vars : List Name
  pairs : Name → Ty → Prop
  passOn : Name → Ty → Prop
  types : List TypeParam

/-- A scope that allows at least what `s` allows. -/
structure RowScope.Le (s s' : RowScope) : Prop where
  vars : ∀ v, v ∈ s.vars → v ∈ s'.vars
  pairs : ∀ v E, s.pairs v E → s'.pairs v E
  passOn : ∀ v E, s.passOn v E → s'.passOn v E
  types : ∀ p, p ∈ s.types → p ∈ s'.types

mutual

/-- The type parameters a type names outside its rows. -/
def Ty.params : Ty → List Name
  | .param T => [T]
  | .list τ => τ.params
  | .tuple τs => tysParams τs
  | .record _ τs | .variant _ τs => tysParams τs
  | .map κ τ => κ.params ++ τ.params
  | .set τ => τ.params
  | .view τ => τ.params
  | .shared τ => τ.params
  | .fn ps r _ => paramTysParams ps ++ r.params
  | _ => []

/-- The type parameters a list of types names. -/
def tysParams : List Ty → List Name
  | [] => []
  | τ :: τs => τ.params ++ tysParams τs

/-- The type parameters a list of parameter types names. -/
def paramTysParams : List (Mode × Ty) → List Name
  | [] => []
  | (_, τ) :: ps => τ.params ++ paramTysParams ps

end

/-- A row whose error type names no type parameter. -/
def Row.ParamFree (ρ : Row) : Prop := ∀ E, ρ.raise = some E → E.params = []

mutual

/-- The type that each `View<T>` in a type views, at every depth, the error types of
its rows included. -/
def Ty.views : Ty → List Ty
  | .list τ => τ.views
  | .tuple τs => tysViews τs
  | .map κ τ => κ.views ++ τ.views
  | .set τ => τ.views
  | .view τ => τ :: τ.views
  | .shared τ => τ.views
  | .fn ps r ρ => paramTysViews ps ++ r.views ++ ρ.views
  | _ => []

/-- The types that the views in a list of types view. -/
def tysViews : List Ty → List Ty
  | [] => []
  | τ :: τs => τ.views ++ tysViews τs

/-- The types that the views in a list of parameter types view. -/
def paramTysViews : List (Mode × Ty) → List Ty
  | [] => []
  | (_, τ) :: ps => τ.views ++ paramTysViews ps

/-- The types that the views in a row's error type view. -/
def Row.views : Row → List Ty
  | ⟨_, some E, _, _, _⟩ => E.views
  | ⟨_, none, _, _, _⟩ => []

end

/-- Every `View<T>` in a type views a viewable `T`: `str` or a `List<U>`; any other `T`
is E0420 where the type is written (views.viewable-types). -/
def Ty.ViewsViewable (τ : Ty) : Prop := ∀ υ ∈ τ.views, υ = .str ∨ ∃ U, υ = .list U

/-- A type that a body may write: each of its row variables is one of the
function's, written or implicit (effects.row-variables and effects.non-escaping-parameters), and each
of its type parameters one of the function's (declarations.function-declarations). A row may hold
variables beside any `raise` label; effects.catch-around-row-variables checks such a row only
where a `catch` meets it. An error type names no type parameter: generic error
types are outside the calculus. Each of its views views a viewable type
(views.viewable-types). -/
def Ty.WellFormed (scope : RowScope) (τ : Ty) : Prop :=
  (∀ ρ ∈ τ.rows, ∀ v ∈ ρ.vars, v ∈ scope.vars) ∧
    (∀ T ∈ τ.params, T ∈ scope.types.map TypeParam.name) ∧ (∀ ρ ∈ τ.rows, ρ.ParamFree) ∧
      τ.ViewsViewable

/-- An instantiation of row variables, as a call gives it (effects.inference). -/
abbrev RowSubst := List (Name × Row)

mutual

/-- Replaces the row variables of a type by their instantiation. -/
def Ty.substRows (s : RowSubst) : Ty → Ty
  | .list τ => .list (τ.substRows s)
  | .tuple τs => .tuple (substTysRows s τs)
  | .record R τs => .record R (substTysRows s τs)
  | .variant T τs => .variant T (substTysRows s τs)
  | .map κ τ => .map (κ.substRows s) (τ.substRows s)
  | .set τ => .set (τ.substRows s)
  | .view τ => .view (τ.substRows s)
  | .shared τ => .shared (τ.substRows s)
  | .fn ps r ρ => .fn (substParamRows s ps) (r.substRows s) (ρ.substRows s)
  | τ => τ

/-- Replaces the row variables of a list of types. -/
def substTysRows (s : RowSubst) : List Ty → List Ty
  | [] => []
  | τ :: τs => τ.substRows s :: substTysRows s τs

/-- Replaces the row variables of a list of parameter types. -/
def substParamRows (s : RowSubst) : List (Mode × Ty) → List (Mode × Ty)
  | [] => []
  | (m, τ) :: ps => (m, τ.substRows s) :: substParamRows s ps

/-- Replaces each row variable of a row that the instantiation names by the
row it stands for, whose elements join the row's: a variable carries the declared effects
of that row as it carries `io` (handlers.rows-pass-effects-on). The result keeps the row's
own `raise` label, or else the first that a variable brings; the use that
instantiates the variables makes sure all of them agree
(`Row.KeepsOneRaise`). Its `resume` is its own, which names no row variable,
since the rows that instantiate variables hold none. -/
def Row.substRows (s : RowSubst) : Row → Row
  | ⟨io, raise, vars, effects, resume⟩ =>
    let raise' := match raise with
      | some E => some (E.substRows s)
      | none => none
    ⟨io || vars.any (fun v => (s.lookup v).any (·.io)),
      raise' <|> vars.findSome? (fun v => (s.lookup v).bind (·.raise)),
      vars.flatMap (fun v => (s.lookup v).elim [v] (·.vars)),
      effects ++ vars.flatMap (fun v => (s.lookup v).elim [] (·.effects)), resume⟩

end

/-- The `raise` labels of `ρ` once `s` instantiates its variables: its own, and
those of the rows its variables stand for. -/
def Row.labels (s : RowSubst) (ρ : Row) : List Ty :=
  ρ.raise.toList.map (Ty.substRows s) ++ ρ.vars.filterMap fun v => (s.lookup v).bind (·.raise)

/-- Instantiating the row variables of `ρ` with `s` leaves it at most one
`raise` label: every label it then holds is the same type (effects.one-error-type).
The rows its variables stand for hold no `resume`, which only the body of a
handler's operation has (handlers.resuming). -/
def Row.KeepsOneRaise (s : RowSubst) (ρ : Row) : Prop :=
  (∀ E ∈ ρ.labels s, ∀ F ∈ ρ.labels s, E = F) ∧
    ∀ v ∈ ρ.vars, ∀ σ, s.lookup v = some σ → σ.resume = none

/-- Every row of `τ` keeps one `raise` label under `s`, so the instantiated
type is a type of the language. -/
def Ty.InstantiableBy (s : RowSubst) (τ : Ty) : Prop :=
  ∀ ρ ∈ τ.rows, ρ.KeepsOneRaise s

/-- Replaces the row variables of a parameter's type. -/
def Param.substRows (s : RowSubst) (p : Param) : Param :=
  { p with type := p.type.substRows s }

end Stilt
