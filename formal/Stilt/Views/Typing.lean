import Stilt.Theorems
import Stilt.Views.Syntax

/-!
# Typing views

The typing judgment of the calculus of views. It types the core calculus's
part as `Stilt.Typing` does, and gives the functions of a view their
signatures (views.making-view and views.functions-of-views). A view of a type that isn't viewable is
E0420 (views.viewable-types), and a view is no place (projections.places-through-views), so `v[i] = x` is E0401
(expressions.assignment). No type holds a view type, so E0421 can't arise (views.view-types).

`ViewAgreement` holds of every program that obeys the law of exclusivity,
whatever its types; typing shows that the programs of
`Stilt.Counterexamples.Views` are ones that the checker accepts but for the
rule each breaks.
-/

namespace Stilt.Views

/-- A binding's type, and whether the body can modify it: only a `var`
binding can (modes.what-can-be-modified). -/
abbrev Ctx := List (Name × VTy × Bool)

mutual

/-- `HasType D Γ e τ`: in the context `Γ`, `e` has the type `τ`. -/
inductive HasType (D : Decls) : Ctx → VExpr → VTy → Prop
  | var {Γ x τ m} : Γ.lookup x = some (τ, m) → HasType D Γ (.var x) τ
  | int {Γ k} : HasType D Γ (.int k) (.base .i64)
  | bool {Γ b} : HasType D Γ (.bool b) (.base .bool)
  | unit {Γ} : HasType D Γ .unit (.base .unit)
  /-- A record literal gives every field, in the order they are declared
  (expressions.struct-literal-fields). -/
  | record {Γ R r fields} : D.record? R = some r →
      fields.map Prod.fst = r.fields.map Prod.fst →
      (∀ fe ∈ fields, ∀ τ, r.fields.lookup fe.1 = some τ → HasType D Γ fe.2 (.base τ)) →
      HasType D Γ (.record R fields) (.base (.record R []))
  | list {Γ τ es} : (∀ e ∈ es, HasType D Γ e (.base τ)) →
      HasType D Γ (.list τ es) (.base (.list τ))
  | field {Γ e R r f τ} : HasType D Γ e (.base (.record R [])) → D.record? R = some r →
      r.fields.lookup f = some τ → HasType D Γ (.field e f) (.base τ)
  | index {Γ e i τ} : HasType D Γ e (.base (.list τ)) → HasType D Γ i (.base .i64) →
      HasType D Γ (.index e i) (.base τ)
  /-- `v[i]` on a `View<List<U>>` (views.functions-of-views). -/
  | viewIndex {Γ e i τ} : HasType D Γ e (.view (.list τ)) → HasType D Γ i (.base .i64) →
      HasType D Γ (.index e i) (.base τ)
  | letIn {Γ x τ init body σ} : HasType D Γ init τ →
      HasType D ((x, τ, false) :: Γ) body σ → HasType D Γ (.letIn x τ init body) σ
  | varIn {Γ x τ init body σ} : HasType D Γ init (.base τ) →
      HasType D ((x, .base τ, true) :: Γ) body σ → HasType D Γ (.varIn x τ init body) σ
  | assign {Γ target value τ} : Mutable D Γ target τ → HasType D Γ value (.base τ) →
      HasType D Γ (.assign target value) (.base .unit)
  | seq {Γ a b σ} : HasType D Γ a (.base .unit) → HasType D Γ b σ → HasType D Γ (.seq a b) σ
  | «if» {Γ c a b σ} : HasType D Γ c (.base .bool) → HasType D Γ a σ → HasType D Γ b σ →
      HasType D Γ (.if c σ a b) σ
  | forList {Γ x τ it body} : HasType D Γ it (.base (.list τ)) →
      HasType D ((x, .base τ, false) :: Γ) body (.base .unit) →
      HasType D Γ (.for x τ it body) (.base .unit)
  /-- `for x in v` over a `View<List<U>>` (views.for-over-view). -/
  | forView {Γ x τ it body} : HasType D Γ it (.view (.list τ)) →
      HasType D ((x, .base τ, false) :: Γ) body (.base .unit) →
      HasType D Γ (.for x τ it body) (.base .unit)
  /-- `View.of<T>(source: T, start: i64, end: i64) -> View<T>`, for a
  viewable `T` (views.viewable-types and views.making-view). -/
  | viewOf {Γ src start stop τ} : viewable τ = true → HasType D Γ src (.base τ) →
      HasType D Γ start (.base .i64) → HasType D Γ stop (.base .i64) →
      HasType D Γ (.viewOf src start stop) (.view τ)
  /-- `view(self, start: i64, end: i64) -> View<T>` (views.functions-of-views). -/
  | sub {Γ v start stop τ} : HasType D Γ v (.view τ) → HasType D Γ start (.base .i64) →
      HasType D Γ stop (.base .i64) → HasType D Γ (.sub v start stop) (.view τ)
  /-- `len(self) -> i64` (views.functions-of-views). -/
  | len {Γ v τ} : HasType D Γ v (.view τ) → HasType D Γ (.len v) (.base .i64)
  /-- `copy(self) -> T` (views.functions-of-views). -/
  | copy {Γ v τ} : HasType D Γ v (.view τ) → HasType D Γ (.copy v) (.base τ)

/-- `Mutable D Γ e τ`: `e` is a place of type `τ` that the body can modify: a
`var` binding followed by fields and indexes (expressions.mutable-places; modes.what-can-be-modified). A view is no place (projections.places-through-views). -/
inductive Mutable (D : Decls) : Ctx → VExpr → Ty → Prop
  | var {Γ x τ} : Γ.lookup x = some (.base τ, true) → Mutable D Γ (.var x) τ
  | field {Γ e R r f τ} : Mutable D Γ e (.record R []) → D.record? R = some r →
      r.fields.lookup f = some τ → Mutable D Γ (.field e f) τ
  | index {Γ e i τ} : Mutable D Γ e (.list τ) → HasType D Γ i (.base .i64) →
      Mutable D Γ (.index e i) τ

end

/-- The context of a function's body: its `let` parameters. -/
def VProgram.ctx (p : VProgram) : Ctx := p.args.map fun a => (a.1, .base a.2.1, false)

/-- A well-typed program: each argument has its parameter's type, and the
body has the result's. -/
def VProgram.WellTyped (p : VProgram) : Prop :=
  (∀ a ∈ p.args, ValueHasType p.decls a.2.2 a.2.1) ∧ HasType p.decls p.ctx p.body p.result

end Stilt.Views
