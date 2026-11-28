import Stilt.Natives.Sorting

/-!
# Keys that sort

The keys among which the structural order is a total preorder (`KeysOrdered`), so that the
native sort gives them in order and stably: integers, Booleans and strings, each compared by
its `Ord.compare`, and floats, compared in the total order where every NaN is equal to every
other and greater than every other value, `-0.0` before `0.0` (traits.floats).
-/

namespace Stilt

/-- Keys that `f` sends to a type whose comparison is a total preorder, the structural order
of two of them being the comparison of their images, are ordered. -/
theorem KeysOrdered.of_cmp {α : Type} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    {orders : CtorOrders} {ks : List Value} (f : Value → α)
    (hf : ∀ a ∈ ks, ∀ b ∈ ks, a.order orders b = cmp (f a) (f b)) : KeysOrdered orders ks where
  swap a ha b hb := by rw [hf a ha b hb, hf b hb a ha]; exact Std.OrientedCmp.eq_swap
  trans a ha b hb c hc hab hbc := by
    rw [hf a ha b hb] at hab
    rw [hf b hb c hc] at hbc
    rw [hf a ha c hc]
    exact Std.TransCmp.isLE_trans hab hbc

/-- An integer's value, and 0 for any other value. -/
def Value.intOr : Value → Int
  | .int n => n
  | _ => 0

/-- A Boolean's value, and `false` for any other value. -/
def Value.boolOr : Value → Bool
  | .bool b => b
  | _ => false

/-- A string's scalar values, and none for any other value. -/
def Value.charsOr : Value → List Char
  | .str s => s.toList
  | _ => []

/-- Integer keys are ordered, by `Ord.compare` on integers. -/
theorem KeysOrdered.ints {orders : CtorOrders} {ks : List Value}
    (h : ∀ k ∈ ks, ∃ n, k = .int n) : KeysOrdered orders ks :=
  KeysOrdered.of_cmp (cmp := compare) Value.intOr fun a ha b hb => by
    obtain ⟨m, rfl⟩ := h a ha
    obtain ⟨n, rfl⟩ := h b hb
    simp only [Value.order, Value.intOr]

/-- Boolean keys are ordered, `false` before `true`. -/
theorem KeysOrdered.bools {orders : CtorOrders} {ks : List Value}
    (h : ∀ k ∈ ks, ∃ b, k = .bool b) : KeysOrdered orders ks :=
  KeysOrdered.of_cmp (cmp := compare) Value.boolOr fun a ha b hb => by
    obtain ⟨m, rfl⟩ := h a ha
    obtain ⟨n, rfl⟩ := h b hb
    simp only [Value.order, Value.boolOr]

/-- String keys are ordered, by their scalar values, which is the order of their bytes. -/
theorem KeysOrdered.strs {orders : CtorOrders} {ks : List Value}
    (h : ∀ k ∈ ks, ∃ s, k = .str s) : KeysOrdered orders ks :=
  KeysOrdered.of_cmp (cmp := compare) Value.charsOr fun a ha b hb => by
    obtain ⟨m, rfl⟩ := h a ha
    obtain ⟨n, rfl⟩ := h b hb
    simp only [Value.order, Value.charsOr]

/-- Where a float stands in `compare`'s order, as an integer: its place among the others, and
`2^64`, above every one of them, for a NaN. -/
def FloatVal.place (x : FloatVal) : Int := x.totalKey.getD (2 ^ 64)

theorem FloatVal.key_lt (sign b : Nat) (hs : sign ≤ 63) {a : Int}
    (h : FloatVal.totalKey.key sign b = some a) : a < 2 ^ 64 := by
  simp only [FloatVal.totalKey.key, Option.some.injEq] at h
  have hm : b % 2 ^ sign < 2 ^ sign := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hp : (2 : Nat) ^ sign ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) hs
  have hm' : ((b % 2 ^ sign : Nat) : Int) < 2 ^ 64 := by
    have : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
    exact_mod_cast (show b % 2 ^ sign < 2 ^ 64 by omega)
  subst h
  split <;> omega

/-- Every float that isn't NaN stands below `2^64`. -/
theorem FloatVal.totalKey_lt {x : FloatVal} {a : Int} (h : x.totalKey = some a) : a < 2 ^ 64 := by
  cases x with
  | f32 x =>
    simp only [FloatVal.totalKey] at h
    split at h
    · cases h
    · exact FloatVal.key_lt 31 _ (by decide) h
  | f64 x =>
    simp only [FloatVal.totalKey] at h
    split at h
    · cases h
    · exact FloatVal.key_lt 63 _ (by decide) h

/-- `compare` on floats is the comparison of their places. -/
theorem FloatVal.order_place (x y : FloatVal) : x.order y = Ord.compare x.place y.place := by
  unfold FloatVal.order FloatVal.place
  cases hx : x.totalKey <;> cases hy : y.totalKey
  · exact (Int.compare_eq_eq.2 rfl).symm
  · have := FloatVal.totalKey_lt hy
    exact (Int.compare_eq_gt.2 (by simp only [Option.getD_none, Option.getD_some]; omega)).symm
  · have := FloatVal.totalKey_lt hx
    exact (Int.compare_eq_lt.2 (by simp only [Option.getD_none, Option.getD_some]; omega)).symm
  · rfl

/-- The place of a float, and 0 for any other value. -/
def Value.floatPlace : Value → Int
  | .float x => x.place
  | _ => 0

/-- Float keys are ordered, in `compare`'s total order (traits.floats). -/
theorem KeysOrdered.floats {orders : CtorOrders} {ks : List Value}
    (h : ∀ k ∈ ks, ∃ x, k = .float x) : KeysOrdered orders ks :=
  KeysOrdered.of_cmp (cmp := compare) Value.floatPlace fun a ha b hb => by
    obtain ⟨x, rfl⟩ := h a ha
    obtain ⟨y, rfl⟩ := h b hb
    simp only [Value.order, Value.floatPlace]
    exact FloatVal.order_place x y

end Stilt
