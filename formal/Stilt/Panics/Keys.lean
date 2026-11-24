import Stilt.Panics.Tests
import Stilt.Maps.Parts
import Stilt.Panics.Ops

/-!
# Keys that tests guard

`m.contains(k)` that holds shows that the map `m` holds has the key `k`, a
variable or a literal, so `m[k]` that follows, while neither is written, finds
the key and doesn't panic with `missing-key` (facts.keys).
-/

namespace Stilt

theorem Entries.find_of_has {v : Value} {es : List (Value × Value)} (h : Entries.has v es = true) :
    ∃ w, Entries.find v es = some w := by
  unfold Entries.has at h
  unfold Entries.find
  obtain ⟨e, he, hp⟩ := List.any_eq_true.1 h
  have : (es.find? fun e => v.keyEq e.1).isSome := List.find?_isSome.2 ⟨e, he, hp⟩
  obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1 this
  exact ⟨e'.2, by rw [he']; rfl⟩

variable {D : Decls} {w : WriteBack}

/-- A key reaches its value in the frame, which it leaves as it was. -/
theorem eval_key_reaches {n : Nat} {k : Expr} {kt : KeyTerm} (hk : k.keyTerm? = some kt)
    {s s' : Copy.State} {v : Value} (h : (eval D (Copy.memoryWith w) n k s).Reaches v s') :
    s' = s ∧ kt.value s.1 = some v := by
  cases k <;> simp only [Expr.keyTerm?, Option.some.injEq, reduceCtorEq] at hk <;> subst hk
  · obtain ⟨rfl, hl⟩ := eval_var_reaches h; exact ⟨rfl, hl⟩
  · obtain ⟨rfl, rfl⟩ := eval_int_reaches h; exact ⟨rfl, rfl⟩
  · cases n <;> cases h; exact ⟨rfl, rfl⟩

/-- `m.contains(k)` that reaches `true` leaves the frame as it was, with `m`
holding a map that has `k`'s value. -/
theorem eval_contains_true {n : Nat} {m : Name} {k : Expr} {kt : KeyTerm} (hk : k.keyTerm? = some kt)
    {s s' : Copy.State} (h : (eval D (Copy.memoryWith w) n (.op (.map .contains) [.var m, k]) s).Reaches (.bool true) s') :
    (Known.has m kt).Holds s'.1 := by
  obtain ⟨_, vs, h₁, h₂⟩ := eval_op_reaches h (fun _ h => by cases h)
  obtain ⟨u, s₁, u', h₃, h₄, rfl⟩ := Eval.list_pair_reaches h₁
  obtain ⟨rfl, hl⟩ := eval_var_reaches h₃
  obtain ⟨rfl, hv⟩ := eval_key_reaches hk h₄
  simp only [Op.apply, MapOp.apply, onMap] at h₂
  split at h₂
  · rename_i es d hm
    simp only [Except.ok.injEq, Value.bool.injEq] at h₂
    exact ⟨u, u', es, d, hl, hv, hm, h₂⟩
  · cases h₂

/-- `m[k]` on a map that has the key doesn't fault. -/
theorem index_calm {m : Name} {k : Expr} {kt : KeyTerm} (hk : k.keyTerm? = some kt) {n : Nat}
    {s s' : Copy.State} {vs : List Value} (hz : (Known.has m kt).Holds s.1)
    (h : (Eval.list (eval D (Copy.memoryWith w) n) [.var m, k] s).Reaches vs s') :
    Calm (Op.apply (.map .index) vs) := by
  obtain ⟨u, s₁, u', h₃, h₄, rfl⟩ := Eval.list_pair_reaches h
  obtain ⟨rfl, hl⟩ := eval_var_reaches h₃
  obtain ⟨rfl, hv⟩ := eval_key_reaches hk h₄
  obtain ⟨mv, v, es, d, hm, hkv, hmap, hhas⟩ := hz
  rw [hl] at hm; cases hm
  rw [hv] at hkv; cases hkv
  obtain ⟨x, hx⟩ := Entries.find_of_has hhas
  simp only [Op.apply, MapOp.apply, onMap, hmap, Entries.index, hx]
  exact Calm.ok _

end Stilt
