import Stilt.Maps

/-!
# Insertion order

What the natives of maps keep of a map's order (std.maps): `insert` and `m[k] = v` leave the keys
in their order, a new key at the end; a key removed and inserted again goes to the end; and
after `insert`, the key finds the value inserted.
-/

namespace Stilt

namespace Entries

/-- std.maps: a key that already has an entry keeps its position, and a new key goes at the
end. -/
theorem keys_insert (k v : Value) (es : List (Value × Value)) :
    (Entries.insert k v es).map Prod.fst =
      if Entries.has k es then es.map Prod.fst else es.map Prod.fst ++ [k] := by
  unfold Entries.insert
  split
  · simp only [List.map_map]
    exact List.map_congr_left fun e _ => by simp only [Function.comp_apply]; split <;> rfl
  · simp

/-- A map without the key `k` has no entry for it. -/
theorem has_remove (k : Value) (es : List (Value × Value)) :
    Entries.has k (Entries.remove k es) = false := by
  simp [Entries.has, Entries.remove]

/-- std.maps: a key inserted again after its removal goes to the end. -/
theorem keys_insert_remove (k v : Value) (es : List (Value × Value)) :
    (Entries.insert k v (Entries.remove k es)).map Prod.fst =
      (Entries.remove k es).map Prod.fst ++ [k] := by
  rw [keys_insert, has_remove]; rfl

/-- std.maps: after `insert`, a key that equals itself, as every value of a key type does, finds
the value inserted. -/
theorem find_insert {k : Value} (hk : k.keyEq k = true) (v : Value) (es : List (Value × Value)) :
    Entries.find k (Entries.insert k v es) = some v := by
  unfold Entries.insert Entries.find
  split
  · rename_i hh
    rw [List.find?_map]
    have hp : ((fun e : Value × Value => k.keyEq e.1) ∘
        fun e : Value × Value => if k.keyEq e.1 then (e.1, v) else e) =
        fun e : Value × Value => k.keyEq e.1 := by
      funext e; simp only [Function.comp_apply]; split <;> rfl
    rw [hp]
    cases hf : es.find? (fun e => k.keyEq e.1) with
    | none =>
      simp only [Entries.has, List.any_eq_true] at hh
      obtain ⟨e, he, hke⟩ := hh
      exact absurd hke (List.find?_eq_none.1 hf e he)
    | some e =>
      have := List.find?_some hf
      simp [this]
  · rename_i hh
    have hn : es.find? (fun e => k.keyEq e.1) = none := by
      rw [List.find?_eq_none]
      intro e he hke
      exact hh (by simp only [Entries.has, List.any_eq_true]; exact ⟨e, he, hke⟩)
    simp [List.find?_append, hn, hk]

end Entries

end Stilt
