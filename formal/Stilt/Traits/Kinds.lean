import Stilt.Traits.Syntax

/-!
# Kinds

traits.constructor-traits, traits.constructor-impls and traits.constructor-parameters give each type constructor an arity: a named
constructor its number of type parameters, a constructor trait's `Self` the
number of arguments the trait writes it with, and a constructor parameter
the arity of its bound. A kind is that number of arguments still to give, and
a type has kind 0. A constructor parameter written without its arguments or
with too many, and an impl of a constructor trait for a constructor of
another arity, are E0337.

`kindOf_subst` is what instantiating a constructor parameter at a call
relies on: a constructor of the parameter's arity, as the head of the
argument's type gives it, keeps the kind of every type it is substituted in.
-/

namespace Stilt.Traits

/-- The kind of a type, given the arity of each named constructor and the
kind of each parameter in scope, or `none` for an ill-kinded one: an argument
that isn't a type, or a type applied to one. A member type is a type, of a
type. -/
def kindOf (arity : Nat → Nat) (ctx : Nat → Option Nat) : Ty → Option Nat
  | .con c => some (arity c)
  | .param p => ctx p
  | .app f a =>
      match kindOf arity ctx f, kindOf arity ctx a with
      | some (n + 1), some 0 => some n
      | _, _ => none
  | .member _ _ x =>
      match kindOf arity ctx x with
      | some 0 => some 0
      | _ => none

/-- `KindPreserved`: substituting, for a parameter of kind `k`, a type of
the same kind keeps the kind of every type. -/
theorem kindOf_subst {arity : Nat → Nat} {ctx : Nat → Option Nat} {p k : Nat}
    {s : Ty} (hp : ctx p = some k) (hs : kindOf arity ctx s = some k) :
    ∀ t : Ty, kindOf arity ctx (t.subst p s) = kindOf arity ctx t := by
  intro t
  induction t with
  | con c => rfl
  | param q =>
      by_cases hq : q = p
      · subst hq; simp [Ty.subst, kindOf, hp, hs]
      · simp [Ty.subst, hq]
  | app f a ihf iha => simp only [Ty.subst, kindOf, ihf, iha]
  | member t k x ih => simp only [Ty.subst, kindOf, ih]

/-- A well-formed type, of kind 0, stays one under such a substitution. -/
theorem type_subst {arity : Nat → Nat} {ctx : Nat → Option Nat} {p k : Nat}
    {s t : Ty} (hp : ctx p = some k) (hs : kindOf arity ctx s = some k)
    (ht : kindOf arity ctx t = some 0) : kindOf arity ctx (t.subst p s) = some 0 := by
  rw [kindOf_subst hp hs t, ht]

/-- A type applied to an argument is ill kinded: `i64<str>`, or `F<i64, i64>`
for `F` of arity 1. -/
theorem app_of_type {arity : Nat → Nat} {ctx : Nat → Option Nat} {f : Ty}
    (hf : kindOf arity ctx f = some 0) (a : Ty) : kindOf arity ctx (.app f a) = none := by
  simp [kindOf, hf]

/-- A constructor as an argument is ill kinded: `List<Option>`. -/
theorem app_of_ctor {arity : Nat → Nat} {ctx : Nat → Option Nat} {a : Ty} {n : Nat}
    (ha : kindOf arity ctx a = some (n + 1)) (f : Ty) : kindOf arity ctx (.app f a) = none := by
  simp only [kindOf, ha]
  split <;> simp_all

/-! ## Examples: `fn doubled<F: Mappable>(xs: F<i64>) -> F<i64>` -/

/-- `i64` is constructor 0, `List` 1, `Map` 2. -/
def exArity : Nat → Nat
  | 1 => 1
  | 2 => 2
  | _ => 0

/-- `F` is parameter 0, a constructor parameter of arity 1. -/
def exCtx : Nat → Option Nat
  | 0 => some 1
  | _ => none

/-- `F<i64>`. -/
def fOfI64 : Ty := .app (.param 0) (.con 0)

theorem fOfI64_type : kindOf exArity exCtx fOfI64 = some 0 := rfl

/-- `F<i64, i64>` is rejected (E0337). -/
theorem fTwice_rejected : kindOf exArity exCtx (.app fOfI64 (.con 0)) = none := rfl

/-- `F` alone isn't a type (E0337). -/
theorem fAlone_not_type : kindOf exArity exCtx (.param 0) ≠ some 0 := by decide

/-- `doubled([1, 2])` takes `F` to be `List`, and `List<i64>` is a type. -/
theorem list_for_f : kindOf exArity exCtx (fOfI64.subst 0 (.con 1)) = some 0 :=
  type_subst rfl rfl fOfI64_type

/-- `Map`, of arity 2, can't stand for `F`: `Map<i64>` isn't a type, which is
why an impl of `Mappable` for `Map` is E0337. -/
theorem map_for_f : kindOf exArity exCtx (fOfI64.subst 0 (.con 2)) = some 1 := rfl

end Stilt.Traits
