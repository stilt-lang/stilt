import Stilt.Traits.Syntax

/-!
# Member types mean one type

traits.trait-arguments keeps traits.coherence: a trait has at most one impl per type
constructor, whatever arguments the impl gives the trait's parameters. Under
that coherence, the type a member type normalizes to is a function of the
type it is named on: `normalize_deterministic`. A call never depends on any
type but its receiver's, and each path names one impl (edits.one-part-per-path).
-/

namespace Stilt.Traits

/-- traits.coherence, and traits.trait-arguments: no two impls of one trait for one
type constructor. -/
def Coherent (impls : List Impl) : Prop :=
  ∀ i ∈ impls, ∀ j ∈ impls, i.trait = j.trait → i.head = j.head → i = j

/-- `Gives impls t k c targs r`: an impl of trait `t` for the constructor
`c`, applied to `targs`, gives the trait's parameter `k` the type `r`
(traits.trait-arguments and traits.member-types). -/
def Gives (impls : List Impl) (t k c : Nat) (targs : List Ty) (r : Ty) : Prop :=
  ∃ i ∈ impls, i.trait = t ∧ i.head = c ∧ (i.args[k]?).map (Ty.inst targs) = some r

/-- Normalization, which replaces each member type of a type headed by a
named constructor by what its impl gives, at any depth (traits.member-types). A
member type of a type parameter stays as it is, as the checker keeps it
abstract until a call instantiates the parameter. -/
inductive Normal (impls : List Impl) : Ty → Ty → Prop where
  | con (c : Nat) : Normal impls (.con c) (.con c)
  | param (p : Nat) : Normal impls (.param p) (.param p)
  | app {f f' a a' : Ty} :
      Normal impls f f' → Normal impls a a' → Normal impls (.app f a) (.app f' a')
  | abstract {t k : Nat} {x x' : Ty} :
      Normal impls x x' → x'.spine = none → Normal impls (.member t k x) (.member t k x')
  | member {t k c : Nat} {x x' r r' : Ty} {targs : List Ty} :
      Normal impls x x' → x'.spine = some (c, targs) → Gives impls t k c targs r →
      Normal impls r r' → Normal impls (.member t k x) r'

/-- Under coherence, what an impl gives a trait's parameter is a function of
the head constructor and its arguments. -/
theorem gives_unique {impls : List Impl} (h : Coherent impls) {t k c : Nat}
    {targs : List Ty} {r r' : Ty} :
    Gives impls t k c targs r → Gives impls t k c targs r' → r = r' := by
  rintro ⟨i, hi, ht, hc, hr⟩ ⟨j, hj, ht', hc', hr'⟩
  have hij : i = j := h i hi j hj (ht.trans ht'.symm) (hc.trans hc'.symm)
  subst hij
  rw [hr] at hr'
  exact Option.some.inj hr'

/-- `NormalizeDeterministic`: under coherence, a type normalizes to at most
one type. -/
theorem normalize_deterministic {impls : List Impl} (h : Coherent impls) :
    ∀ {x y y' : Ty}, Normal impls x y → Normal impls x y' → y = y' := by
  intro x y y' hy
  induction hy generalizing y' with
  | con c => intro hy'; cases hy'; rfl
  | param p => intro hy'; cases hy'; rfl
  | app _ _ ihf iha =>
      intro hy'
      cases hy' with
      | app hf ha => rw [ihf hf, iha ha]
  | abstract _ hs ih =>
      intro hy'
      cases hy' with
      | abstract hx _ => rw [ih hx]
      | member hx hs' _ _ => rw [ih hx] at hs; rw [hs] at hs'; cases hs'
  | member _ hs hg _ ihx ihr =>
      intro hy'
      cases hy' with
      | abstract hx hs' => rw [ihx hx] at hs; rw [hs] at hs'; cases hs'
      | member hx hs' hg' hr =>
          rw [ihx hx] at hs
          rw [hs] at hs'
          cases hs'
          exact ihr (gives_unique h hg hg' ▸ hr)

end Stilt.Traits
