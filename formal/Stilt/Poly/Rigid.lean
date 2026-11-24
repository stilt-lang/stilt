/-!
# Rigid type parameters

polymorphism.rigid-types checks an argument given where a polymorphic function type
`fn<T>(…) -> …` is expected with `T` taken as a rigid type: a type distinct
from every other, which only itself is equal to. Each use of the argument then
instantiates `T` afresh (polymorphism.instantiation). This calculus states the fact that rule rests
on: a term that type checks with a rigid parameter still type checks, at the
instantiated type, once any type replaces the parameter, so checking it once
covers every use.

Its types are `i64`, type parameters, named by their indexes, and function
types; its terms are variables, by de Bruijn index, integer literals, closures
whose parameter's type is written, as an expected type gives a closure's
parameter its type, and calls. Bounds are left out: the rigid type's bounds
are what the expected type gives, and the substitution keeps none of the
types it doesn't touch.
-/

namespace Stilt.Poly

/-- A type of the calculus. -/
inductive Ty where
  | int : Ty
  /-- A type parameter: a rigid type, equal only to itself. -/
  | param : Nat → Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq, Repr

/-- `t.subst p s` is `t` with the parameter `p` replaced by `s`, as a use of a
polymorphic value instantiates it (polymorphism.instantiation). -/
def Ty.subst : Ty → Nat → Ty → Ty
  | .int, _, _ => .int
  | .param q, p, s => if q = p then s else .param q
  | .arrow a b, p, s => .arrow (a.subst p s) (b.subst p s)

/-- Whether the parameter `p` occurs in a type. -/
def Ty.mentions : Ty → Nat → Bool
  | .int, _ => false
  | .param q, p => q = p
  | .arrow a b, p => a.mentions p || b.mentions p

/-- A term of the calculus. -/
inductive Tm where
  | var : Nat → Tm
  | lit : Int → Tm
  /-- A closure, with the type of its parameter. -/
  | lam : Ty → Tm → Tm
  | app : Tm → Tm → Tm
  deriving DecidableEq, Repr

/-- A term with the parameter `p` replaced by `s` in the types it writes. -/
def Tm.substTy : Tm → Nat → Ty → Tm
  | .var n, _, _ => .var n
  | .lit k, _, _ => .lit k
  | .lam a b, p, s => .lam (a.subst p s) (b.substTy p s)
  | .app f x, p, s => .app (f.substTy p s) (x.substTy p s)

/-- The typing judgment: the types of the variables in scope, innermost
first, a term and its type. A parameter's type is equal only to itself, so a
term of a rigid type uses it only as itself (polymorphism.rigid-types). -/
inductive HasType : List Ty → Tm → Ty → Prop where
  | var {Γ : List Ty} {n : Nat} {t : Ty} : Γ[n]? = some t → HasType Γ (.var n) t
  | lit {Γ : List Ty} {k : Int} : HasType Γ (.lit k) .int
  | lam {Γ : List Ty} {a t : Ty} {b : Tm} :
      HasType (a :: Γ) b t → HasType Γ (.lam a b) (.arrow a t)
  | app {Γ : List Ty} {f x : Tm} {a t : Ty} :
      HasType Γ f (.arrow a t) → HasType Γ x a → HasType Γ (.app f x) t

/-- `Accepts Γ p e τ`: `e`, checked where `fn<T>` with body `τ` is expected,
with `T` the parameter `p`, which no type in scope names: a rigid type that
nothing outside the argument knows (polymorphism.rigid-types). -/
def Accepts (Γ : List Ty) (p : Nat) (e : Tm) (τ : Ty) : Prop :=
  (∀ t ∈ Γ, t.mentions p = false) ∧ HasType Γ e τ

/-- A type that doesn't name `p` is kept by replacing it. -/
theorem Ty.subst_unmentioned {t : Ty} {p : Nat} (s : Ty) (h : t.mentions p = false) :
    t.subst p s = t := by
  induction t with
  | int => rfl
  | param q =>
      have hq : q ≠ p := by simpa [Ty.mentions] using h
      simp [Ty.subst, hq]
  | arrow a b iha ihb =>
      simp only [Ty.mentions, Bool.or_eq_false_iff] at h
      simp [Ty.subst, iha h.1, ihb h.2]

/-- `RigidSubst`: replacing a type parameter by any type keeps a typing,
with the parameter replaced in the context and the type too. -/
theorem HasType.substTy {Γ : List Ty} {e : Tm} {t : Ty} (h : HasType Γ e t)
    (p : Nat) (s : Ty) :
    HasType (Γ.map (·.subst p s)) (e.substTy p s) (t.subst p s) := by
  induction h with
  | var hn => exact .var (by simp [List.getElem?_map, hn])
  | lit => exact .lit
  | lam _ ih => exact .lam ih
  | app _ _ ihf ihx => exact .app ihf ihx

/-- `RigidInstance`: an argument accepted with `T` rigid has, at each use,
the type that instantiating `T` with any type gives (polymorphism.instantiation and polymorphism.rigid-types),
in the scope it was checked in. -/
theorem Accepts.instance {Γ : List Ty} {p : Nat} {e : Tm} {τ : Ty}
    (h : Accepts Γ p e τ) (s : Ty) : HasType Γ (e.substTy p s) (τ.subst p s) := by
  have hΓ : Γ.map (·.subst p s) = Γ := by
    conv => rhs; rw [← List.map_id Γ]
    exact List.map_congr_left fun t ht => Ty.subst_unmentioned s (h.1 t ht)
  have := h.2.substTy p s
  rwa [hΓ] at this

/-! ## Examples: `fn twice(f: fn<T>(T) -> T, n: i64) -> i64` -/

/-- `T → T`, the body of `fn<T>(T) -> T`, with `T` the parameter 0. -/
def idTy : Ty := .arrow (.param 0) (.param 0)

/-- `|x| x`, whose parameter takes the rigid `T`. -/
def identity : Tm := .lam (.param 0) (.var 0)

theorem identity_accepted : Accepts [] 0 identity idTy :=
  ⟨by simp, .lam (.var rfl)⟩

/-- At `f(n)`, `T` is `i64`, and `|x| x` has type `i64 → i64` there. -/
theorem identity_at_int :
    HasType [] (identity.substTy 0 .int) (.arrow .int .int) :=
  identity_accepted.instance .int

/-- At a use with `T` a function type, it has that type too. -/
theorem identity_at_arrow :
    HasType [] (identity.substTy 0 (.arrow .int .int))
      (.arrow (.arrow .int .int) (.arrow .int .int)) :=
  identity_accepted.instance (.arrow .int .int)

end Stilt.Poly
