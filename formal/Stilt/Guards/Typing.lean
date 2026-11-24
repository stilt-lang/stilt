import Stilt.Guards.Match

/-!
# Typing guards and list patterns

Values of types, patterns checked against the type of the value they match
with the names they bind (patterns.pattern-types), and expressions, a guard of
type `bool` among them, typed with those names in scope (patterns.match). The
alternatives of an or-pattern bind the same names with the same types
(patterns.or-patterns). A list pattern's elements match the list's element
type, and `..rest` binds a list of it.
-/

namespace Stilt.Guards

/-- The variables in scope, innermost first, with their types. -/
abbrev Ctx := List (Name × Ty)

mutual

/-- A value of a type. -/
inductive ValTy : Val → Ty → Prop
  | int {k} : ValTy (.int k) .int
  | bool {b} : ValTy (.bool b) .bool
  | unit : ValTy .unit .unit
  | tuple {vs ts} : ValsTy vs ts → ValTy (.tuple vs) (.tuple ts)
  | list {vs τ} : (∀ v ∈ vs, ValTy v τ) → ValTy (.list vs) (.list τ)
  | none {τ} : ValTy .none (.option τ)
  | some {v τ} : ValTy v τ → ValTy (.some v) (.option τ)

/-- Values of types, position by position. -/
inductive ValsTy : List Val → List Ty → Prop
  | nil : ValsTy [] []
  | cons {v vs τ τs} : ValTy v τ → ValsTy vs τs → ValsTy (v :: vs) (τ :: τs)

end

mutual

/-- `PatTy p τ Δ`: the pattern `p` matches values of type `τ` and binds the
variables `Δ`. -/
inductive PatTy : Pat → Ty → Ctx → Prop
  | wild {τ} : PatTy .wild τ []
  | bind {x τ} : PatTy (.bind x) τ [(x, τ)]
  | int {k} : PatTy (.int k) .int []
  | bool {b} : PatTy (.bool b) .bool []
  | unit : PatTy .unit .unit []
  | const {n c τ} : ValTy c τ → PatTy (.const n c) τ []
  | tuple {ps ts Δ} : PatsTy ps ts Δ → PatTy (.tuple ps) (.tuple ts) Δ
  | none {τ} : PatTy .none (.option τ) []
  | some {p τ Δ} : PatTy p τ Δ → PatTy (.some p) (.option τ) Δ
  | list {ps τ Δ} : PatsTy ps (List.replicate ps.length τ) Δ → PatTy (.list ps) (.list τ) Δ
  | prefix {ps τ Δ} :
      PatsTy ps (List.replicate ps.length τ) Δ → PatTy (.prefix ps none) (.list τ) Δ
  | prefixRest {ps τ Δ r} :
      PatsTy ps (List.replicate ps.length τ) Δ →
      PatTy (.prefix ps (some r)) (.list τ) (Δ ++ [(r, .list τ)])
  | or {p q τ Δ Δ'} :
      PatTy p τ Δ → PatTy q τ Δ' → (∀ x, Δ'.lookup x = Δ.lookup x) → PatTy (.or p q) τ Δ

/-- Patterns of types, position by position, binding what each binds in turn. -/
inductive PatsTy : List Pat → List Ty → Ctx → Prop
  | nil : PatsTy [] [] []
  | cons {p ps τ τs Δ Δ'} : PatTy p τ Δ → PatsTy ps τs Δ' → PatsTy (p :: ps) (τ :: τs) (Δ ++ Δ')

end

/-- `HasType Γ e τ`: with the variables `Γ` in scope, `e` has type `τ`. -/
inductive HasType : Ctx → Expr → Ty → Prop
  | num {Γ k} : HasType Γ (.num k) .int
  | bool {Γ b} : HasType Γ (.bool b) .bool
  | unit {Γ} : HasType Γ .unit .unit
  | var {Γ x τ} : Γ.lookup x = some τ → HasType Γ (.var x) τ
  | add {Γ a b} : HasType Γ a .int → HasType Γ b .int → HasType Γ (.add a b) .int
  | lt {Γ a b} : HasType Γ a .int → HasType Γ b .int → HasType Γ (.lt a b) .bool
  | print {Γ a b σ τ} : HasType Γ a σ → HasType Γ b τ → HasType Γ (.print a b) τ

/-- An arm of a `match` on values of type `τ` whose arms have type `σ`: its
pattern's names are in scope in its guard, of type `bool`, and its body
(patterns.match). -/
def ArmTy (Γ : Ctx) (τ σ : Ty) (a : Arm) : Prop :=
  ∃ Δ, PatTy a.pat τ Δ ∧ (∀ g, a.guard = some g → HasType (Δ ++ Γ) g .bool) ∧
    HasType (Δ ++ Γ) a.body σ

/-- Variables whose values have the types of a context. -/
def EnvOk (ρ : Env) (Γ : Ctx) : Prop :=
  ∀ x τ, Γ.lookup x = some τ → ∃ v, ρ.lookup x = some v ∧ ValTy v τ

/-- The bindings of a way of a pattern that binds `Δ`: a value of its type for
each name of `Δ`, and nothing else. -/
structure Agree (w : Env) (Δ : Ctx) : Prop where
  bound : ∀ x τ, Δ.lookup x = some τ → ∃ v, w.lookup x = some v ∧ ValTy v τ
  unbound : ∀ x, Δ.lookup x = none → w.lookup x = none

end Stilt.Guards
