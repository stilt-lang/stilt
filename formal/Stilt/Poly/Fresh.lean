import Stilt.Poly.Rigid

/-!
# Fresh types

meta.fresh-types gives the field, the element or the payload that an arm or a
loop body reads a fresh type: a rigid type of that arm, which no type outside
it names, and E0351 keeps a value whose type holds one from leaving it. The
arm is checked once, with the fresh type rigid, and each run gives it the type
the value really has, as a call gives a polymorphic argument its instance
(polymorphism.instantiation). So an arm is a closure whose parameter has the fresh
type, accepted where `fn<F>(F) -> τ` is expected.

This file states the fact both rules rest on, in the calculus of
[Rigid type parameters](Rigid.lean): when `τ` doesn't name the fresh type, every
run of the arm has the type `τ` that its check gave, whatever type the value
has; and when it does, as E0351 forbids, two runs of one arm have different
types, so no type outside the arm covers its value.
-/

namespace Stilt.Poly

/-- A term has at most one type in a scope, since a closure writes its
parameter's type. -/
theorem HasType.unique {Γ : List Ty} {e : Tm} {t t' : Ty} (h : HasType Γ e t)
    (h' : HasType Γ e t') : t = t' := by
  induction h generalizing t' with
  | var hn =>
      cases h' with
      | var hn' => rw [hn] at hn'; exact Option.some.inj hn'
  | lit => cases h'; rfl
  | lam _ ih =>
      cases h' with
      | lam hb => rw [ih hb]
  | app _ _ ihf _ =>
      cases h' with
      | app hf' _ =>
          have := ihf hf'
          injection this

/-- `FreshArm Γ p body τ`: an arm whose value has type `τ`, checked with the
value it reads bound to `body`'s variable 0 at the fresh type `p`, which no
type in scope names (meta.fresh-types). -/
def FreshArm (Γ : List Ty) (p : Nat) (body : Tm) (τ : Ty) : Prop :=
  Accepts Γ p (.lam (.param p) body) (.arrow (.param p) τ)

/-- The arm run on a value `v` that really has the type `s`: `p` is `s` in
the arm's code, and `v` is what it reads. -/
def FreshArm.runOn (p : Nat) (body : Tm) (s : Ty) (v : Tm) : Tm :=
  .app ((Tm.lam (.param p) body).substTy p s) v

/-- `FreshRun`: an arm whose type doesn't name its fresh type, as E0351
requires, has that type on every run, whatever type the value it reads has. -/
theorem FreshArm.run {Γ : List Ty} {p : Nat} {body : Tm} {τ : Ty}
    (h : FreshArm Γ p body τ) (hτ : τ.mentions p = false) {v : Tm} {s : Ty}
    (hv : HasType Γ v s) : HasType Γ (FreshArm.runOn p body s v) τ := by
  have hi := h.instance s
  simp only [Ty.subst, Ty.subst_unmentioned s hτ] at hi
  exact .app hi hv

/-! ## Without E0351: an arm whose value is what it reads -/

/-- `x => x`: the arm gives the value it reads, of the fresh type 0. -/
def leaking : Tm := .var 0

theorem leaking_checks : FreshArm [] 0 leaking (.param 0) :=
  ⟨by simp, .lam (.var rfl)⟩

/-- Run on an integer, the arm's value is an `i64`. -/
theorem leaking_at_int : HasType [] (FreshArm.runOn 0 leaking .int (.lit 1)) .int :=
  .app (.lam (.var rfl)) .lit

/-- Run on a function, the same arm's value is a function. -/
theorem leaking_at_arrow :
    HasType [] (FreshArm.runOn 0 leaking (.arrow .int .int) (.lam .int (.var 0)))
      (.arrow .int .int) :=
  .app (.lam (.var rfl)) (.lam (.var rfl))

/-- `FreshLeak`: no one type covers the arm's value on both runs, so the
type the arm's check gives can't be the value's, which is why E0351 stops a
value whose type holds a fresh type at the arm's end. -/
theorem leaking_has_no_type : ¬ ∃ t : Ty,
    HasType [] (FreshArm.runOn 0 leaking .int (.lit 1)) t ∧
    HasType [] (FreshArm.runOn 0 leaking (.arrow .int .int) (.lam .int (.var 0))) t := by
  rintro ⟨t, h1, h2⟩
  have e1 := leaking_at_int.unique h1
  have e2 := leaking_at_arrow.unique h2
  rw [← e1] at e2
  exact Ty.noConfusion e2

end Stilt.Poly
