import Stilt.Panics.Keys
import Stilt.Panics.Kept

/-!
# What a condition's facts mean

When a condition reaches the Boolean `b`, the facts it gives for `b` hold
(`eval_facts`): a test's, by how it runs (`eval_zeroTest`); a conjunct's of an
`&&` that holds, or a disjunct's of an `||` that doesn't, for the variables
that the operands after it don't write (`eval_keeps`); and through `!`.
-/

namespace Stilt

theorem Eval.asBool_done {σ : Type} {v : Value} {s s' : σ} {b : Bool}
    (h : Eval.asBool v s = .done b s') : v = .bool b ∧ s' = s := by
  cases v <;> cases h
  exact ⟨rfl, rfl⟩

theorem eval_bool_reaches {σ : Type} {D : Decls} {M : Memory σ} {n : Nat} {c : Bool} {s s' : σ}
    {v : Value} (h : (eval D M n (.bool c) s).Reaches v s') : v = .bool c := by
  cases n <;> cases h
  rfl

theorem Op.not_apply {v w : Value} (h : Op.apply .not [v] = .ok w) : ∃ b, v = .bool b ∧ w = .bool (!b) := by
  cases v with
  | bool b =>
    refine ⟨b, rfl, ?_⟩
    simp only [Op.apply, Op.applyScalars, Value.scalar?, List.mapM_cons, List.mapM_nil, Op.compute] at h
    cases h
    rfl
  | _ => simp [Op.apply, Op.applyScalars, Value.scalar?, Op.compute] at h <;> exact nomatch h

variable {D : Decls} (w : WriteBack)

/-- When a condition reaches `b`, the facts it gives for `b` hold. -/
theorem eval_facts : ∀ n (c : Expr) (b : Bool) (s s' : Copy.State),
    (eval D (Copy.memoryWith w) n c s).Reaches (.bool b) s' → Frame.Meets (c.factsAs b) s'.1
  | 0, _, _, _, _, h => nomatch h
  | n + 1, c, b, s, s', h => by
    unfold Expr.factsAs
    split
    · rename_i a τ x y
      change (Eval.bind (Eval.bind (eval D (Copy.memoryWith w) n a) Eval.asBool)
        (fun v => if v then eval D (Copy.memoryWith w) n x else eval D (Copy.memoryWith w) n y) s).Reaches _ _ at h
      obtain ⟨va, s₁, h₁, h₂⟩ := Eval.bind_reaches h
      obtain ⟨vb, s₂, h₃, h₄⟩ := Eval.bind_reaches h₁
      obtain ⟨hvb, hs⟩ := Eval.asBool_reaches h₄
      subst hvb hs
      have ka := eval_facts n a va s s₁ h₃
      split
      · rename_i hb
        simp only [Bool.and_eq_true] at hb
        obtain ⟨rfl, hy⟩ := hb
        cases va
        · rw [Expr.eq_of_isBool hy] at h₂
          exact absurd (eval_bool_reaches h₂) (by simp)
        · have k := h₂.keeps (eval_keeps D w n x x.writes x.resizes (List.Subset.refl _) (List.Subset.refl _) s₁)
          exact (ka.keep k.2).append (eval_facts n x true s₁ s' h₂)
      · split
        · rename_i _ hb
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hb
          obtain ⟨rfl, hx⟩ := hb
          cases va
          · have k := h₂.keeps (eval_keeps D w n y y.writes y.resizes (List.Subset.refl _) (List.Subset.refl _) s₁)
            exact (ka.keep k.2).append (eval_facts n y false s₁ s' h₂)
          · rw [Expr.eq_of_isBool hx] at h₂
            exact absurd (eval_bool_reaches h₂) (by simp)
        · exact Frame.Meets.nil _
    · rename_i o es
      unfold opFacts
      split
      · rename_i a
        change (Eval.bind (Eval.list (eval D (Copy.memoryWith w) n) [a])
          (fun vs => Eval.world (Copy.memoryWith w) (Op.run .not vs)) s).Reaches _ _ at h
        simp only [Eval.world_memoryWith_of_ne w (o := .not) (fun _ h => by cases h)] at h
        obtain ⟨vs, s₁, h₁, h₂⟩ := Eval.bind_reaches h
        obtain ⟨v, h₃, rfl⟩ := Eval.list_single_reaches h₁
        obtain ⟨hv, rfl⟩ := Eval.ofExcept_reaches h₂
        obtain ⟨b', rfl, hu⟩ := Op.not_apply hv
        simp only [Value.bool.injEq] at hu
        subst hu
        simpa using eval_facts n a b' s _ h₃
      · rename_i cmp k l r
        cases hz : (Expr.op (.compare cmp k) [l, r]).test? with
        | none => exact Frame.Meets.nil _
        | some t =>
          obtain ⟨rfl, r', hv, hran⟩ := eval_test hz h
          simp only [Value.bool.injEq] at hv
          subst hv
          cases t with
          | zero c x left =>
            obtain ⟨a, hl, hr⟩ := hran
            have hz := Cmp.facts_zero (Cmp.norm_ints hr.symm)
            intro f hf
            simp only [testFacts, List.mem_append] at hf
            rcases hf with hf | hf <;> split at hf <;> simp only [List.mem_singleton, List.not_mem_nil] at hf <;>
              subst hf
            · rename_i hc; exact ⟨a, hl, hz.1 hc⟩
            · rename_i hc; exact ⟨a, hl, hz.2 hc⟩
          | len c x xs left =>
            obtain ⟨a, vs, hl, hx, hr⟩ := hran
            have hlt := Cmp.norm_ints hr.symm
            intro f hf
            simp only [testFacts] at hf
            split at hf
            · rename_i hc
              simp only [beq_iff_eq] at hc
              rw [hc] at hlt
              simp only [List.mem_singleton] at hf
              subst hf
              exact ⟨a, vs, hl, hx, by simpa [Cmp.ints] using hlt⟩
            · cases hf
      · rename_i a k
        split
        · rename_i hb
          subst hb
          unfold containsFacts
          split
          · rename_i m kt ha hk
            intro f hf
            simp only [List.mem_singleton] at hf
            subst hf
            rw [Expr.eq_of_readVar? ha] at h
            exact eval_contains_true hk h
          · exact Frame.Meets.nil _
        · exact Frame.Meets.nil _
      · exact Frame.Meets.nil _
    · exact Frame.Meets.nil _

end Stilt
