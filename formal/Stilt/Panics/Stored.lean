import Stilt.Panics.Facts

/-!
# Keys that stores give

A store `m = m.insert(k, v)`, as the export writes `m[k] = v` and `m.insert(k, v)`, leaves the
map `m` holds with the key `k`, a variable or a literal that `v` doesn't write (facts.keys):
the insert of a key that equals itself finds it again, and a key that doesn't, such as a
float's NaN, is stuck, which no well-typed program is (`Value.Typed.keyEq_of_key`).
-/

namespace Stilt

theorem Expr.storedKey?_spec {e : Expr} {m : Name} {kt : KeyTerm} (h : e.storedKey? = some (m, kt)) :
    ∃ k v, e = .assign ⟨m, []⟩ (.op (.map .insert) [.var m, k, v]) ∧ k.keyTerm? = some kt ∧
      m ∉ kt.reads ∧ ∀ x ∈ kt.reads, x ∉ v.writes := by
  unfold Expr.storedKey? at h
  split at h
  · rename_i m'' a k v
    split at h
    · rename_i m' kt ha hk
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨rfl, hm, hv⟩ := hc
        exact ⟨k, v, by rw [Expr.eq_of_readVar? ha], hk, hm, by simpa using hv⟩
      · cases h
    · cases h
  · cases h

theorem Eval.list_triple_reaches {σ : Type} {run : Expr → Eval σ Value} {a b c : Expr} {s s' : σ}
    {vs : List Value} (h : (Eval.list run [a, b, c] s).Reaches vs s') :
    ∃ u s₁ v s₂ x, (run a s).Reaches u s₁ ∧ (run b s₁).Reaches v s₂ ∧ (run c s₂).Reaches x s' ∧
      vs = [u, v, x] := by
  unfold Eval.list at h
  obtain ⟨u, s₁, h₁, h₂⟩ := Eval.bind_reaches h
  obtain ⟨us, s₂, h₃, h₄⟩ := Eval.bind_reaches h₂
  obtain ⟨v, s₃, x, h₅, h₆, rfl⟩ := Eval.list_pair_reaches h₃
  obtain ⟨rfl, rfl⟩ := Eval.pure_reaches h₄
  exact ⟨u, s₁, v, s₃, x, h₁, h₅, h₆, rfl⟩

theorem Entries.has_insert {k v : Value} {es : List (Value × Value)} (hk : k.keyEq k = true) :
    Entries.has k (Entries.insert k v es) = true := by
  unfold Entries.insert
  split
  · rename_i h
    unfold Entries.has at h ⊢
    obtain ⟨e, he, hp⟩ := List.any_eq_true.1 h
    refine List.any_eq_true.2 ⟨if k.keyEq e.1 then (e.1, v) else e, List.mem_map_of_mem he, ?_⟩
    simp [hp]
  · simp [Entries.has, hk]

variable {D : Decls} {w : WriteBack}

/-- After a store `m = m.insert(k, v)` reaches its end, the map `m` holds has the key `k`. -/
theorem eval_stored_holds {n : Nat} {e : Expr} {m : Name} {kt : KeyTerm}
    (he : e.storedKey? = some (m, kt)) {s s' : Copy.State} {u : Value}
    (h : (eval D (Copy.memoryWith w) n e s).Reaches u s') : (Known.has m kt).Holds s'.1 := by
  obtain ⟨k, v, rfl, hk, hm, hv⟩ := Expr.storedKey?_spec he
  cases n with
  | zero => cases h
  | succ n =>
    change (Eval.assign (Copy.memoryWith w) (eval D (Copy.memoryWith w) n) m []
      (.op (.map .insert) [.var m, k, v]) s).Reaches _ _ at h
    unfold Eval.assign Eval.path at h
    obtain ⟨p, s₀, h₀, h₁⟩ := Eval.bind_reaches h
    obtain ⟨rfl, rfl⟩ := Eval.pure_reaches h₀
    obtain ⟨mv', s₁, h₂, h₃⟩ := Eval.bind_reaches h₁
    obtain ⟨_, s₂, h₄, h₅⟩ := Eval.bind_reaches h₃
    obtain ⟨rfl, rfl⟩ := Eval.pure_reaches h₅
    obtain ⟨n', vs, hl, ha⟩ := eval_op_reaches h₂ (fun _ h => by cases h)
    obtain ⟨mv, t₁, kv, t₂, vv, hr₁, hr₂, hr₃, rfl⟩ := Eval.list_triple_reaches hl
    obtain ⟨e₁, -⟩ := eval_var_reaches hr₁
    obtain ⟨e₂, hkv⟩ := eval_key_reaches hk hr₂
    subst e₁ e₂
    have kk := (hr₃.keeps (eval_keeps D w n' v v.writes v.resizes (List.Subset.refl _)
      (List.Subset.refl _) _)).2
    simp only [Op.apply, MapOp.apply, onMap] at ha
    split at ha
    · rename_i es d _
      split at ha
      · rename_i hkk
        simp only [Except.ok.injEq] at ha
        subst ha
        simp only [Eval.update, Eval.Keeps.memoryWith_write] at h₄
        unfold Copy.write at h₄
        cases hm₁ : s₁.1.lookup m with
        | none =>
          simp only [hm₁] at h₄
          exact nomatch h₄
        | some old =>
          simp only [hm₁, Value.set, Functor.map, Except.map] at h₄
          obtain ⟨-, rfl⟩ := h₄.inv
          refine ⟨_, kv, _, d, lookup_assocSet_self _ _ _ (by simp [hm₁]), ?_, Value.map?_mapOf _ _,
            Entries.has_insert hkk⟩
          cases kt with
          | var x =>
            simp only [KeyTerm.reads, List.mem_singleton, forall_eq] at hm hv
            simp only [KeyTerm.value] at hkv ⊢
            rw [lookup_assocSet_ne _ _ (Ne.symm hm), kk.lookup hv, hkv]
          | int _ | bool _ => exact hkv
      · cases ha
    · cases ha

end Stilt
