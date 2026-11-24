import Stilt.Poly.Rigid

/-!
# A closure that fixes its rigid type

`Accepts.instance` needs `T` rigid. `|x| 0` given where `fn<T>(T) -> T` is
expected returns an `i64` where `T` is expected, which polymorphism.rigid-types rejects
(E0311, as `same(|x| 0)` in the conformance suite's `argument_errors.lt`).
Read with `T` fixed to `i64`, it has type `i64 → i64`; but a use that takes
`T` to be another type, as `twice` may, would then get a closure that returns
an `i64` where it expects that type.
-/

namespace Stilt.Poly

/-- `|x| 0`, whose parameter takes the rigid `T`. -/
def constZero : Tm := .lam (.param 0) (.lit 0)

/-- With `T` rigid, `|x| 0` doesn't have type `T → T`: E0311. -/
theorem constZero_rejected : ¬ Accepts [] 0 constZero idTy := by
  intro ⟨_, h⟩
  cases h with
  | lam hb => cases hb

/-- With `T` fixed to `i64`, `|x: i64| 0` has type `i64 → i64`. -/
theorem constZero_fixed : HasType [] (.lam .int (.lit 0)) (.arrow .int .int) :=
  .lam .lit

/-- Its use with `T` a function type has no type: the closure returns an
`i64` where a function is expected, which accepting it would let through. -/
theorem constZero_unsound :
    ¬ HasType [] (constZero.substTy 0 (.arrow .int .int))
      (idTy.subst 0 (.arrow .int .int)) := by
  simp only [constZero, idTy, Tm.substTy, Ty.subst, ite_true]
  intro h
  cases h with
  | lam hb => cases hb

end Stilt.Poly
