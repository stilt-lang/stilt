import Stilt.Traits.Members

/-!
# Parameters that `Self` doesn't determine

`normalize_deterministic` needs coherence, which traits.trait-arguments keeps by
having the impl's type fix the trait's arguments. Parameters that don't
depend on `Self`, as Rust's `From<T>` has, which traits.trait-parameters rules out
(reference/rationale/11-traits.md), allow `impl Convert<f64> for i64` beside
`impl Convert<str> for i64`, and then the member type `i64.T` normalizes to
both `f64` and `str`.
-/

namespace Stilt.Traits

/-- `Convert` is trait 0; `i64`, `f64` and `str` are constructors 0, 1 and
2. -/
def twoConverts : List Impl := [⟨0, 0, [.con 1]⟩, ⟨0, 0, [.con 2]⟩]

/-- The two impls break coherence: E0304. -/
theorem twoConverts_incoherent : ¬ Coherent twoConverts := by
  intro h
  have := h ⟨0, 0, [.con 1]⟩ (by simp [twoConverts]) ⟨0, 0, [.con 2]⟩
    (by simp [twoConverts]) rfl rfl
  simp at this

/-- The member type of `i64` normalizes to `f64`, through the first impl. -/
theorem converts_to_f64 : Normal twoConverts (.member 0 0 (.con 0)) (.con 1) :=
  .member (.con 0) rfl ⟨⟨0, 0, [.con 1]⟩, by simp [twoConverts], rfl, rfl, rfl⟩ (.con 1)

/-- And to `str`, through the second. -/
theorem converts_to_str : Normal twoConverts (.member 0 0 (.con 0)) (.con 2) :=
  .member (.con 0) rfl ⟨⟨0, 0, [.con 2]⟩, by simp [twoConverts], rfl, rfl, rfl⟩ (.con 2)

/-- `SelfDeterminedNeeded`: without coherence, normalization isn't unique,
so `normalize_deterministic` needs the parameters that `Self` determines. -/
theorem selfDetermined_needed :
    ∃ impls : List Impl, ∃ x y y' : Ty,
      ¬ Coherent impls ∧ Normal impls x y ∧ Normal impls x y' ∧ y ≠ y' :=
  ⟨twoConverts, _, _, _, twoConverts_incoherent, converts_to_f64, converts_to_str, by decide⟩

end Stilt.Traits
