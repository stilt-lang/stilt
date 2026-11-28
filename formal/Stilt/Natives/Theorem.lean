import Stilt.Natives.Panics
import Stilt.Natives.Keys
import Stilt.Natives.Clamp
import Stilt.Natives.Maps
import Stilt.Natives.Search

/-!
# What the natives keep

The rules of the standard library that the natives of the calculus keep, whatever program
runs them (`Natives.kept`): they panic only where their paragraphs say; the native sort gives
the elements again, in order of their keys, and stably; the natives `max` and `min` give
`clamp` the consequences its paragraph states; `insert` keeps a map's order; and `find` gives
the first occurrence.
-/

namespace Stilt

/-- The native sort, `sortedByKey`, gives the elements in the order of `sortedPairs`. -/
theorem Op.sortedByKey_apply (d : Bool) (orders : CtorOrders) (ks xs : List Value) :
    (Op.sortedByKey d orders).apply [.list ks, .list xs] =
      .ok (.list ((sortedPairs orders d ks xs).map Prod.snd)) :=
  rfl

/-- What the natives of the calculus keep of the standard library's paragraphs. -/
structure Natives.Kept : Prop where
  /-- std.no-panics-by-default (`Op.run_panics`). -/
  panics : ∀ (o : Op) (vs : List Value), (∀ v ∈ vs, v.Fits) → ∀ (w : World) (k : PanicKind),
    o.run vs w = .error (.panic k) → k ∈ o.panicKinds
  /-- std.lists: indexing and storing panic only with `bounds` (`Value.get_panics`,
  `Value.set_panics`). -/
  places : (∀ (v : Value) (p : Path) (k : PanicKind), v.get p = .error (.panic k) → k = .bounds) ∧
    ∀ (v : Value) (p : Path) (w : Value) (k : PanicKind), v.set p w = .error (.panic k) →
      k = .bounds
  /-- std.list-sorting: the native sort gives what `sortedPairs` orders
  (`Op.sortedByKey_apply`). -/
  sort : ∀ (d : Bool) (orders : CtorOrders) (ks xs : List Value),
    (Op.sortedByKey d orders).apply [.list ks, .list xs] =
      .ok (.list ((sortedPairs orders d ks xs).map Prod.snd))
  /-- std.list-sorting: each element once (`sortByKeys_perm`). -/
  perm : ∀ (orders : CtorOrders) (d : Bool) (ks xs : List Value), ks.length = xs.length →
    (sortByKeys orders d ks xs).Perm xs
  /-- std.list-sorting: in order of the keys (`sortedPairs_sorted`). -/
  sorted : ∀ (orders : CtorOrders) (ks : List Value), KeysOrdered orders ks → ∀ (d : Bool)
    (xs : List Value), (sortedPairs orders d ks xs).Pairwise fun a b => keyBefore orders d a.1 b.1
  /-- std.list-sorting: stably (`sortedPairs_stable`). -/
  stable : ∀ (orders : CtorOrders) (ks : List Value), KeysOrdered orders ks → ∀ (d : Bool)
    (xs : List Value) (a b : Value × Value), [a, b].Sublist (ks.zip xs) →
    keyBefore orders d a.1 b.1 = true → [a, b].Sublist (sortedPairs orders d ks xs)
  /-- traits.floats: integers, Booleans, strings and floats sort by `Ord.compare`, a total
  preorder (`KeysOrdered.ints`, `KeysOrdered.bools`, `KeysOrdered.strs`,
  `KeysOrdered.floats`). -/
  ordered : ∀ (orders : CtorOrders) (ks : List Value), ((∀ k ∈ ks, ∃ n, k = .int n) ∨
    (∀ k ∈ ks, ∃ b, k = .bool b) ∨ (∀ k ∈ ks, ∃ s, k = .str s) ∨
    (∀ k ∈ ks, ∃ x, k = .float x)) → KeysOrdered orders ks
  /-- std.clamp-and-sum: on integers, `hi` wins when `lo > hi` (`IntTy.clamp_hi`). -/
  clampHi : ∀ (k : IntTy) (x lo hi : Int), k.Contains x → k.Contains lo → k.Contains hi →
    hi < lo → k.clamp x lo hi = .ok hi
  /-- std.clamp-and-sum: on integers, between `lo` and `hi` (`IntTy.clamp_between`). -/
  clampBetween : ∀ (k : IntTy) (x lo hi : Int), k.Contains x → k.Contains lo → k.Contains hi →
    lo ≤ hi → ∃ r, k.clamp x lo hi = .ok r ∧ lo ≤ r ∧ r ≤ hi ∧ (lo ≤ x → x ≤ hi → r = x)
  /-- std.clamp-and-sum: on floats, a NaN stays NaN (`FloatVal.clamp_nan`). -/
  clampNan : ∀ (x lo hi z : FloatVal), x.clamp lo hi = some z →
    (x.isNaN = true ∨ lo.isNaN = true ∨ hi.isNaN = true) → z.isNaN = true ∧ (x.isNaN = true → z = x)
  /-- std.maps: `insert` keeps a key's position, a new key at the end (`Entries.keys_insert`). -/
  keysInsert : ∀ (k v : Value) (es : List (Value × Value)), (Entries.insert k v es).map Prod.fst =
    if Entries.has k es then es.map Prod.fst else es.map Prod.fst ++ [k]
  /-- std.maps: a key inserted again after its removal goes to the end
  (`Entries.keys_insert_remove`). -/
  keysReinsert : ∀ (k v : Value) (es : List (Value × Value)),
    (Entries.insert k v (Entries.remove k es)).map Prod.fst =
      (Entries.remove k es).map Prod.fst ++ [k]
  /-- std.maps: after `insert`, the key finds its value (`Entries.find_insert`). -/
  findInsert : ∀ (k v : Value) (es : List (Value × Value)), k.keyEq k = true →
    Entries.find k (Entries.insert k v es) = some v
  /-- std.str-search: `find` gives the first occurrence, or none (`Str.find_first`). -/
  findFirst : ∀ s sub : String,
    (∀ n, Str.find false s sub = some n →
      sub.toUTF8.toList.isPrefixOf (s.toUTF8.toList.drop n) = true ∧
      ∀ j < n, sub.toUTF8.toList.isPrefixOf (s.toUTF8.toList.drop j) = false) ∧
    (Str.find false s sub = none →
      ∀ j ≤ s.toUTF8.toList.length, sub.toUTF8.toList.isPrefixOf (s.toUTF8.toList.drop j) = false)

/-- **The natives keep their paragraphs**: std.no-panics-by-default, for the natives of the
calculus (`Op.run_panics`); std.list-sorting, for the native sort that `sorted_by`,
`sorted_desc_by`, `sorted`, `sorted_desc` and the verbs that store what they give sort with,
which gives the elements again, each once, in ascending or descending order of their keys by
`Ord.compare`, and stably, among keys that `Ord.compare` orders totally, as it does integers,
Booleans, strings and floats (traits.floats); and std.clamp-and-sum, for `clamp`, written in
Stilt on the natives `max` and `min`, so a NaN stays NaN, and on integers `hi` wins when
`lo > hi`; std.maps, whose `insert` keeps a key's position and puts a new one at the end; and
std.str-search, whose `find` gives the first occurrence. The model states less than std.list-sorting: that `sorted_with` sorts is its source's,
and that keys of compound types are totally ordered is left out. It states less than
std.clamp-and-sum: that `hi` wins on floats, and `sum`, written in Stilt, are left out. -/
theorem Natives.kept : Natives.Kept where
  panics o _ hvs w _ h := o.run_panics hvs w h
  places := ⟨fun v p _ h => v.get_panics p h, fun v p w _ h => v.set_panics p w h⟩
  sort := Op.sortedByKey_apply
  perm orders d _ _ h := sortByKeys_perm orders d h
  sorted _ _ h d xs := sortedPairs_sorted h d xs
  stable _ _ h d _ _ _ hab hle := sortedPairs_stable h d hab hle
  ordered _ _ h := by
    rcases h with h | h | h | h
    · exact KeysOrdered.ints h
    · exact KeysOrdered.bools h
    · exact KeysOrdered.strs h
    · exact KeysOrdered.floats h
  clampHi k _ _ _ hx hlo hhi h := k.clamp_hi hx hlo hhi h
  clampBetween k _ _ _ hx hlo hhi h := k.clamp_between hx hlo hhi h
  clampNan _ _ _ _ h hn := FloatVal.clamp_nan h hn
  keysInsert := Entries.keys_insert
  keysReinsert := Entries.keys_insert_remove
  findInsert k v es hk := Entries.find_insert hk v es
  findFirst := Str.find_first

end Stilt
