import Stilt.Structural

/-!
# The native sort of lists

What `Op.sortedByKey` gives, the native that `sorted_by(key)` and `sorted_desc_by(key)` sort
with once `key` has given each element's key: the elements again, each once (a permutation),
in ascending or descending order of their keys by `Ord.compare`, and stably, two elements that
the order lets stand in either order keeping the order they had. The order is the one of the
prelude's structural impls of `Ord` (`Value.order`). A merge sort needs it to be a total
preorder among the keys it sorts, `KeysOrdered`: it is so of integers, Booleans, strings and
floats, by `Ord.compare` on each, floats in the total order where every NaN is equal to every
other and greater than every other value.
-/

namespace Stilt

/-- The keys and the elements of a sort, paired, in the order the sort gives them. -/
def sortedPairs (orders : CtorOrders) (descending : Bool) (ks xs : List Value) :
    List (Value × Value) :=
  (ks.zip xs).mergeSort fun a b => keyBefore orders descending a.1 b.1

theorem sortByKeys_pairs (orders : CtorOrders) (descending : Bool) (ks xs : List Value) :
    sortByKeys orders descending ks xs = (sortedPairs orders descending ks xs).map Prod.snd :=
  rfl

/-- Keys among which the structural order is a total preorder: comparing the other way
gives the opposite answer, and order at most is transitive. -/
structure KeysOrdered (orders : CtorOrders) (ks : List Value) : Prop where
  swap : ∀ a ∈ ks, ∀ b ∈ ks, a.order orders b = (b.order orders a).swap
  trans : ∀ a ∈ ks, ∀ b ∈ ks, ∀ c ∈ ks, (a.order orders b).isLE = true →
    (b.order orders c).isLE = true → (a.order orders c).isLE = true

theorem ne_gt_eq_isLE (o : Ordering) : (o != .gt) = o.isLE := by cases o <;> rfl

theorem swap_ne_lt_eq_isLE (o : Ordering) : (o.swap != .lt) = o.isLE := by cases o <;> rfl

theorem isLE_or_swap (o : Ordering) : o.isLE || o.swap.isLE := by cases o <;> rfl

namespace KeysOrdered

variable {orders : CtorOrders} {ks : List Value}

/-- `keyBefore`, among ordered keys, is order at most, read the other way when descending. -/
theorem keyBefore_eq (h : KeysOrdered orders ks) (d : Bool) {a b : Value} (ha : a ∈ ks)
    (hb : b ∈ ks) : keyBefore orders d a b = if d then (b.order orders a).isLE
      else (a.order orders b).isLE := by
  unfold keyBefore
  cases d
  · exact ne_gt_eq_isLE _
  · simp only [↓reduceIte]; rw [h.swap a ha b hb]; exact swap_ne_lt_eq_isLE _

theorem before_trans (h : KeysOrdered orders ks) (d : Bool) {a b c : Value} (ha : a ∈ ks)
    (hb : b ∈ ks) (hc : c ∈ ks) (hab : keyBefore orders d a b = true)
    (hbc : keyBefore orders d b c = true) : keyBefore orders d a c = true := by
  rw [h.keyBefore_eq d ha hb] at hab
  rw [h.keyBefore_eq d hb hc] at hbc
  rw [h.keyBefore_eq d ha hc]
  cases d
  · exact h.trans a ha b hb c hc hab hbc
  · exact h.trans c hc b hb a ha hbc hab

theorem before_total (h : KeysOrdered orders ks) (d : Bool) {a b : Value} (ha : a ∈ ks)
    (hb : b ∈ ks) : keyBefore orders d a b || keyBefore orders d b a := by
  rw [h.keyBefore_eq d ha hb, h.keyBefore_eq d hb ha]
  cases d
  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [h.swap b hb a ha]; exact isLE_or_swap _
  · simp only [↓reduceIte]; rw [h.swap a ha b hb]; exact isLE_or_swap _

end KeysOrdered

open Classical in
/-- The order of a sort, extended to every pair: one whose key isn't among `ks` after all
the others. Among pairs whose keys are, it is `keyBefore`. -/
noncomputable def keyLe (orders : CtorOrders) (d : Bool) (ks : List Value)
    (p q : Value × Value) : Bool :=
  if q.1 ∈ ks then (if p.1 ∈ ks then keyBefore orders d p.1 q.1 else false) else true

theorem keyLe_of_mem {orders : CtorOrders} {d : Bool} {ks : List Value} {p q : Value × Value}
    (hp : p.1 ∈ ks) (hq : q.1 ∈ ks) : keyLe orders d ks p q = keyBefore orders d p.1 q.1 := by
  simp [keyLe, hp, hq]

theorem keyLe_trans {orders : CtorOrders} {ks : List Value} (h : KeysOrdered orders ks) (d : Bool)
    (a b c : Value × Value) (hab : keyLe orders d ks a b = true)
    (hbc : keyLe orders d ks b c = true) : keyLe orders d ks a c = true := by
  unfold keyLe at *
  by_cases hc : c.1 ∈ ks
  · by_cases hb : b.1 ∈ ks
    · by_cases ha : a.1 ∈ ks
      · simp only [hc, hb, ha, ↓reduceIte] at hab hbc ⊢
        exact h.before_trans d ha hb hc hab hbc
      · simp [hb, ha] at hab
    · simp [hc, hb] at hbc
  · simp [hc]

theorem keyLe_total {orders : CtorOrders} {ks : List Value} (h : KeysOrdered orders ks) (d : Bool)
    (a b : Value × Value) : keyLe orders d ks a b || keyLe orders d ks b a := by
  unfold keyLe
  by_cases ha : a.1 ∈ ks <;> by_cases hb : b.1 ∈ ks <;> simp only [ha, hb, ↓reduceIte] <;>
    first | rfl | exact h.before_total d ha hb | simp

/-- The sort reads only its own pairs, whose keys are among `ks`, so it sorts as `keyLe`. -/
theorem sortedPairs_keyLe (orders : CtorOrders) (d : Bool) (ks xs : List Value) :
    sortedPairs orders d ks xs = (ks.zip xs).mergeSort (keyLe orders d ks) := by
  have := List.map_mergeSort (f := id) (l := ks.zip xs) (s := keyLe orders d ks)
    (r := fun a b => keyBefore orders d a.1 b.1) fun a ha b hb =>
      (keyLe_of_mem (List.of_mem_zip ha).1 (List.of_mem_zip hb).1).symm
  simpa [sortedPairs] using this

/-- std.list-sorting: the sort gives the elements again, each once. -/
theorem sortByKeys_perm (orders : CtorOrders) (d : Bool) {ks xs : List Value}
    (h : ks.length = xs.length) : (sortByKeys orders d ks xs).Perm xs := by
  rw [sortByKeys_pairs, sortedPairs]
  have hp := (List.mergeSort_perm (ks.zip xs) fun a b => keyBefore orders d a.1 b.1).map Prod.snd
  rwa [List.map_snd_zip (by omega)] at hp

/-- std.list-sorting: among ordered keys, the sort gives the elements in order of their
keys, ascending, or descending when `d` says so: each pair's key comes before every later
pair's. -/
theorem sortedPairs_sorted {orders : CtorOrders} {ks : List Value} (h : KeysOrdered orders ks)
    (d : Bool) (xs : List Value) :
    (sortedPairs orders d ks xs).Pairwise fun a b => keyBefore orders d a.1 b.1 := by
  have hs := List.pairwise_mergeSort (keyLe_trans h d) (keyLe_total h d) (ks.zip xs)
  rw [← sortedPairs_keyLe] at hs
  refine hs.imp_of_mem fun {a b} ha hb hab => ?_
  have ha' := (List.of_mem_zip ((List.mergeSort_perm _ _).mem_iff.1 ha)).1
  have hb' := (List.of_mem_zip ((List.mergeSort_perm _ _).mem_iff.1 hb)).1
  rwa [keyLe_of_mem ha' hb'] at hab

/-- std.list-sorting: the sort is stable. Two pairs in this order, the first's key before the
second's, as when the keys are equal, stay in this order. -/
theorem sortedPairs_stable {orders : CtorOrders} {ks : List Value} (h : KeysOrdered orders ks)
    (d : Bool) {xs : List Value} {a b : Value × Value} (hab : [a, b].Sublist (ks.zip xs))
    (hle : keyBefore orders d a.1 b.1 = true) : [a, b].Sublist (sortedPairs orders d ks xs) := by
  rw [sortedPairs_keyLe]
  have ha := (List.of_mem_zip (a := a.1) (b := a.2) (hab.subset (by simp))).1
  have hb := (List.of_mem_zip (a := b.1) (b := b.2) (hab.subset (by simp))).1
  exact List.pair_sublist_mergeSort (keyLe_trans h d) (keyLe_total h d)
    (by rw [keyLe_of_mem ha hb]; exact hle) hab

end Stilt
