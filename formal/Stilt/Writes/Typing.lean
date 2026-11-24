import Stilt.Writes.Syntax

/-!
# Typing writable views

The typing judgment of the calculus of writable views, as
`Stilt.Views.Typing` types the views calculus. A `var` binding of a view type
is writable (projections.writable-bindings), `view.into` takes a place that the body can
modify, as an `inout` argument (projections.writable-views; modes.what-can-be-modified), and `v[i]` through a
writable binding is a place (projections.places-through-views). `WriteAgreement` holds of every program
that the checks accept, whatever its types; typing shows that the programs of
`Stilt.Counterexamples.Writes` are ones the checker accepts but for the rule
each breaks.
-/

namespace Stilt.Writes

open Stilt.Views (VTy viewable)

/-- A binding's type, and whether the body can modify it: only a `var`
binding can (modes.what-can-be-modified). -/
abbrev Ctx := List (Name × VTy × Bool)

mutual

/-- `HasType Γ e τ`: in the context `Γ`, `e` has the type `τ`. -/
inductive HasType : Ctx → WExpr → VTy → Prop
  | var {Γ x τ m} : Γ.lookup x = some (τ, m) → HasType Γ (.var x) τ
  | int {Γ k} : HasType Γ (.int k) (.base .i64)
  | list {Γ τ es} : (∀ e ∈ es, HasType Γ e (.base τ)) → HasType Γ (.list τ es) (.base (.list τ))
  | index {Γ e i τ} : HasType Γ e (.base (.list τ)) → HasType Γ i (.base .i64) →
      HasType Γ (.index e i) (.base τ)
  /-- `v[i]` on a `View<List<U>>` (views.functions-of-views). -/
  | viewIndex {Γ e i τ} : HasType Γ e (.view (.list τ)) → HasType Γ i (.base .i64) →
      HasType Γ (.index e i) (.base τ)
  | letIn {Γ x τ init body σ} : HasType Γ init τ → HasType ((x, τ, false) :: Γ) body σ →
      HasType Γ (.letIn x τ init body) σ
  /-- `var x: T = e`, of a value or of a view, which is then writable (projections.writable-bindings). -/
  | varIn {Γ x τ init body σ} : HasType Γ init τ → HasType ((x, τ, true) :: Γ) body σ →
      HasType Γ (.varIn x τ init body) σ
  | assign {Γ t v τ} : Mutable Γ t τ → HasType Γ v (.base τ) →
      HasType Γ (.assign t v) (.base .unit)
  /-- `v[i] = e` through a writable binding of a `View<List<U>>` (projections.places-through-views). -/
  | assignThrough {Γ v i e τ} : Γ.lookup v = some (.view (.list τ), true) →
      HasType Γ i (.base .i64) → HasType Γ e (.base τ) →
      HasType Γ (.assign (.index (.var v) i) e) (.base .unit)
  | seq {Γ a b σ} : HasType Γ a (.base .unit) → HasType Γ b σ → HasType Γ (.seq a b) σ
  /-- `View.of<T>(source: T, start: i64, end: i64) -> View<T>`, of a place of a
  viewable `T` (views.viewable-types and views.making-view). -/
  | viewOf {Γ src a b τ} : viewable τ = true → src.root?.isSome = true →
      HasType Γ src (.base τ) → HasType Γ a (.base .i64) → HasType Γ b (.base .i64) →
      HasType Γ (.viewOf src a b) (.view τ)
  /-- `view.into<U>(inout xs: List<U>, start: i64, end: i64) -> View<List<U>>`
  (projections.writable-views). -/
  | into {Γ src a b τ} : Mutable Γ src (.list τ) → HasType Γ a (.base .i64) →
      HasType Γ b (.base .i64) → HasType Γ (.into src a b) (.view (.list τ))
  /-- `view(self, start: i64, end: i64) -> View<T>` (views.functions-of-views). -/
  | sub {Γ v a b τ} : HasType Γ v (.view τ) → HasType Γ a (.base .i64) →
      HasType Γ b (.base .i64) → HasType Γ (.sub v a b) (.view τ)
  /-- `len(self) -> i64` (views.functions-of-views). -/
  | len {Γ v τ} : HasType Γ v (.view τ) → HasType Γ (.len v) (.base .i64)

/-- `Mutable Γ e τ`: `e` is a place of type `τ` that the body can modify: a
`var` binding of a value followed by indexes (expressions.mutable-places; modes.what-can-be-modified). -/
inductive Mutable : Ctx → WExpr → Ty → Prop
  | var {Γ x τ} : Γ.lookup x = some (.base τ, true) → Mutable Γ (.var x) τ
  | index {Γ e i τ} : Mutable Γ e (.list τ) → HasType Γ i (.base .i64) →
      Mutable Γ (.index e i) τ

end

/-- A well-typed program: its body has the type of its value. -/
def WProgram.WellTyped (p : WProgram) : Prop := HasType [] p.body p.result

end Stilt.Writes
