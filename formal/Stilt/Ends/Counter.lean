import Stilt.Ends.NoCont
import Stilt.Panics.Facts
import Stilt.Panics.Kept

/-!
# What a counting loop's turn does

In copy-in, copy-out: a bound that ends with an integer has the value
`Bound.val` gives, which only the variables it reads decide (`eval_bound`,
`Bound.val_congr`); a condition that counts and holds compares the counter's
integer with the bound's (`eval_count`); and a body that steps the counter and
ends, or continues, has moved it toward the bound (`eval_steps`).
-/

namespace Stilt

theorem Cmp.mirror_ints (c : Cmp) (x y : Int) : c.mirror.ints x y = c.ints y x := by
  cases c <;> simp only [Cmp.mirror, Cmp.ints] <;> first
    | rfl
    | exact Bool.eq_iff_iff.2 (by simp only [beq_iff_eq, bne_iff_ne, ne_eq]; constructor <;> intro h <;> omega)

theorem Expr.bound?_spec {e : Expr} {b : Bound} (h : e.bound? = some b) : e = b.toExpr := by
  unfold Expr.bound? at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · cases h; rfl
  · rename_i o k a c
    split at h
    · split at h
      · rename_i a' c' ha hc
        cases h
        simp only [Bound.toExpr, Expr.bound?_spec ha, Expr.bound?_spec hc]
      · cases h
    · cases h
  · cases h

/-- Frames that agree on what a bound reads give it the same value. -/
theorem Bound.val_congr {s s' : Copy.Frame} :
    ∀ (b : Bound), (∀ x ∈ b.reads, s'.lookup x = s.lookup x) → b.val s' = b.val s
  | .lit _, _ => rfl
  | .var x, h => by simp only [Bound.val, h x (by simp [Bound.reads])]
  | .len xs, h => by simp only [Bound.val, h xs (by simp [Bound.reads])]
  | .arith o k a b, h => by
    have ha := Bound.val_congr a fun x hx => h x (by simp [Bound.reads, hx])
    have hb := Bound.val_congr b fun x hx => h x (by simp [Bound.reads, hx])
    simp only [Bound.val, ha, hb]

variable {D : Decls} {w : WriteBack}

/-- A bound that reaches a value leaves the frame as it was, and an integer it
reaches is its value. -/
theorem eval_bound : ∀ (b : Bound) {n : Nat} {s s' : Copy.State} {v : Value},
    (eval D (Copy.memoryWith w) n b.toExpr s).Reaches v s' → s' = s ∧ ∀ y, v = .int y → b.val s.1 = some y
  | .lit k, _, _, _, _, h => by
    obtain ⟨rfl, rfl⟩ := eval_int_reaches h
    exact ⟨rfl, fun y hy => by cases hy; rfl⟩
  | .var x, _, _, _, _, h => by
    obtain ⟨rfl, hl⟩ := eval_var_reaches h
    exact ⟨rfl, fun y hy => by subst hy; simp [Bound.val, hl]⟩
  | .len xs, _, _, _, _, h => by
    obtain ⟨m, us, h₁, h₂⟩ := eval_op_reaches h (fun _ h => by cases h)
    obtain ⟨u, h₃, rfl⟩ := Eval.list_single_reaches h₁
    obtain ⟨rfl, hl⟩ := eval_var_reaches h₃
    refine ⟨rfl, fun y hy => ?_⟩
    subst hy
    cases u with
    | list vs =>
      simp only [Op.apply, ListOp.apply, onList, Value.list?] at h₂
      simp only [Bound.val, hl]
      cases hc : IntTy.i64.check vs.length with
      | error f => rw [hc] at h₂; cases h₂
      | ok r => rw [hc] at h₂; cases h₂; rfl
    | _ => simp [Op.apply, ListOp.apply, onList, Value.list?] at h₂
  | .arith o k a b, _, _, _, _, h => by
    obtain ⟨m, us, h₁, h₂⟩ := eval_op_reaches h (fun _ h => by cases h)
    obtain ⟨u, s₁, u', h₃, h₄, rfl⟩ := Eval.list_pair_reaches h₁
    obtain ⟨rfl, ha⟩ := eval_bound a h₃
    obtain ⟨rfl, hb⟩ := eval_bound b h₄
    obtain ⟨x, y, r, rfl, rfl, hr, rfl⟩ := arith_apply h₂
    refine ⟨rfl, fun z hz => ?_⟩
    cases hz
    simp [Bound.val, ha x rfl, hb y rfl, hr, Except.toOption]

/-- A condition that counts and holds compares the counter's integer with the
bound's, by each of its readings. -/
theorem eval_count : ∀ {c : Expr} {v : Name} {cmp : Cmp} {b : Bound} {n : Nat} {s s' : Copy.State},
    (v, cmp, b) ∈ c.countings → (eval D (Copy.memoryWith w) n c s).Reaches (.bool true) s' →
    ∃ x y, s.1.lookup v = some (.int x) ∧ b.val s.1 = some y ∧ cmp.ints x y = true := by
  intro c v cmp b n s s' hc h
  unfold Expr.countings at hc
  split at hc
  · rename_i c' k l r
    obtain ⟨m, us, h₁, h₂⟩ := eval_op_reaches h (fun _ h => by cases h)
    obtain ⟨u, s₁, u', h₃, h₄, rfl⟩ := Eval.list_pair_reaches h₁
    obtain ⟨x', y', rfl, rfl, hr⟩ := compare_apply h₂
    simp only [Value.bool.injEq] at hr
    rcases List.mem_append.1 hc with hc | hc
    · split at hc
      · rename_i v' b' _ hl hr' _
        simp only [List.mem_singleton, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl, rfl⟩ := hc
        rw [Expr.eq_of_readVar? hl] at h₃
        rw [Expr.bound?_spec hr'] at h₄
        obtain ⟨rfl, hlv⟩ := eval_var_reaches h₃
        obtain ⟨rfl, hb⟩ := eval_bound _ h₄
        exact ⟨x', y', hlv, hb y' rfl, hr.symm⟩
      · cases hc
    · split at hc
      · rename_i v' b' _ hr' hl _
        simp only [List.mem_singleton, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl, rfl⟩ := hc
        rw [Expr.bound?_spec hl] at h₃
        rw [Expr.eq_of_readVar? hr'] at h₄
        obtain ⟨rfl, hb⟩ := eval_bound _ h₃
        obtain ⟨rfl, hlv⟩ := eval_var_reaches h₄
        exact ⟨y', x', hlv, hb x' rfl, by rw [Cmp.mirror_ints]; exact hr.symm⟩
      · cases hc
  · rename_i a τ x y
    split at hc
    · rename_i hy
      rw [Expr.eq_of_isBool hy] at h
      cases n with
      | zero => cases h
      | succ m =>
        change (Eval.bind (Eval.bind (eval D (Copy.memoryWith w) m a) Eval.asBool)
          (fun g => if g then eval D (Copy.memoryWith w) m x else eval D (Copy.memoryWith w) m (.bool false)) s).Reaches _ _ at h
        obtain ⟨g, s₁, h₁, h₂⟩ := Eval.bind_reaches h
        obtain ⟨u, s₂, h₃, h₄⟩ := Eval.bind_reaches h₁
        obtain ⟨rfl, rfl⟩ := Eval.asBool_reaches h₄
        cases g
        · exact absurd (eval_bool_reaches h₂) (by simp)
        · exact eval_count hc h₃
    · cases hc
  · cases hc

/-- The value a step gives the counter. -/
def stepped (grow : Bool) (x k : Int) : Int := if grow then x + k else x - k

/-- A step that ends has moved the counter by a positive amount. -/
theorem eval_isStep {e : Expr} {v : Name} {grow : Bool} (he : e.isStep v grow = true) {n : Nat}
    {s s' : Copy.State} {x : Int} {u : Value} (hx : s.1.lookup v = some (.int x))
    (h : eval D (Copy.memoryWith w) n e s = .done u s') :
    ∃ k, 0 < k ∧ s'.1.lookup v = some (.int (stepped grow x k)) := by
  unfold Expr.isStep at he
  split at he
  · rename_i y p value
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at he
    obtain ⟨⟨h1, rfl⟩, hm⟩ := he
    rw [h1] at h
    unfold Expr.movesBy at hm
    split at hm
    · rename_i o kt l r
      simp only [Bool.and_eq_true, beq_iff_eq, Option.any_eq_true, decide_eq_true_eq] at hm
      obtain ⟨⟨hl, k, hr, hk⟩, ho⟩ := hm
      rw [Expr.eq_of_readVar? hl] at h
      have hr' : r = .int k := by cases r <;> simp_all [Expr.intLit?]
      rw [hr'] at h
      cases n with
      | zero => cases h
      | succ m =>
        change (Eval.path (eval D (Copy.memoryWith w) m) [] >>= fun p =>
          eval D (Copy.memoryWith w) m (.op (.arith o kt) [.var v, .int k]) >>= fun val =>
          Eval.update (fun s => (Copy.memoryWith w).write s v p val) >>= fun _ => Pure.pure Value.unit) s = _ at h
        obtain ⟨p, s₁, h₁, h₂⟩ := Eval.bind_done h
        cases h₁
        obtain ⟨val, s₂, h₃, h₄⟩ := Eval.bind_done h₂
        obtain ⟨m', us, h₅, h₆⟩ := eval_op_reaches (.of_eq h₃) (fun _ h => by cases h)
        obtain ⟨a, s₃, b, h₇, h₈, rfl⟩ := Eval.list_pair_reaches h₅
        obtain ⟨rfl, hl⟩ := eval_var_reaches h₇
        obtain ⟨hb, rfl⟩ := eval_int_reaches h₈
        subst hb
        rw [hx] at hl
        cases hl
        obtain ⟨x', k', r, hx', hk', hr, rfl⟩ := arith_apply h₆
        cases hx'; cases hk'
        obtain ⟨_, s₄, h₉, h₁₀⟩ := Eval.bind_done h₄
        cases h₁₀
        unfold Eval.update at h₉
        split at h₉
        · rename_i s₅ hw
          cases h₉
          simp only [Eval.Keeps.memoryWith_write, Copy.write, hx] at hw
          simp only [Value.set, Functor.map, Except.map, Except.ok.injEq] at hw
          subst hw
          refine ⟨k, hk, ?_⟩
          rw [lookup_assocSet_self _ _ _ (by simp [hx])]
          cases grow <;> simp only [Bool.false_eq_true, ↓reduceIte] at ho <;> subst ho <;>
            simp only [IntTy.arith, IntTy.check] at hr <;> split at hr <;> cases hr <;> rfl
        · rename_i f _; cases f <;> cases h₉
    · cases hm
  · cases he

/-- A block that steps the counter and ends, or continues, has moved it by a
positive amount. -/
theorem eval_steps : ∀ {e : Expr} {v : Name} {grow : Bool}, e.steps v grow = true → ∀ {n : Nat}
    {s s' : Copy.State} {x : Int}, s.1.lookup v = some (.int x) →
    ((∃ u, eval D (Copy.memoryWith w) n e s = .done u s') ∨
      eval D (Copy.memoryWith w) n e s = .jumped .cont s') →
    ∃ k, 0 < k ∧ s'.1.lookup v = some (.int (stepped grow x k)) := by
  intro e v grow he n s s' x hx h
  unfold Expr.steps at he
  split at he
  · rename_i a b
    cases n with
    | zero => rcases h with ⟨_, h⟩ | h <;> cases h
    | succ m =>
      have hseq : eval D (Copy.memoryWith w) (m + 1) (.seq a b) s =
          Eval.bind (eval D (Copy.memoryWith w) m a) (fun _ => eval D (Copy.memoryWith w) m b) s := rfl
      rw [hseq] at h
      unfold Eval.bind Outcome.bind at h
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at he
      rcases he with ⟨ha, hvb⟩ | ⟨⟨hca, hva⟩, hb⟩
      · cases hm : eval D (Copy.memoryWith w) m a s <;> rw [hm] at h <;> (try dsimp only at h) <;>
          (try (rcases h with ⟨_, h⟩ | h <;> cases h; done))
        · rename_i u₁ s₁
          obtain ⟨k, hk, hl⟩ := eval_steps ha hx (.inl ⟨u₁, hm⟩)
          have keep := eval_keeps D w m b b.writes b.resizes (List.Subset.refl _) (List.Subset.refl _) s₁
          refine ⟨k, hk, ?_⟩
          rcases h with ⟨u, h⟩ | h <;> rw [h] at keep
          · rw [keep.2.lookup hvb, hl]
          · rw [keep.lookup hvb, hl]
        · rename_i j s₁
          rcases h with ⟨_, h⟩ | h <;> cases h
          exact eval_steps ha hx (.inr hm)
      · cases hm : eval D (Copy.memoryWith w) m a s <;> rw [hm] at h <;> (try dsimp only at h) <;>
          (try (rcases h with ⟨_, h⟩ | h <;> cases h; done))
        · rename_i u₁ s₁
          have keep := eval_keeps D w m a a.writes a.resizes (List.Subset.refl _) (List.Subset.refl _) s
          rw [hm] at keep
          exact eval_steps hb (by rw [keep.2.lookup hva, hx]) h
        · rename_i j s₁
          rcases h with ⟨_, h⟩ | h <;> cases h
          exact absurd hm ((eval_noCont D _ m a hca s).ne s')
  · rcases h with ⟨u, h⟩ | h
    · exact eval_isStep he hx h
    · have hc : e.contFree = true := by
        unfold Expr.isStep at he
        split at he
        · rename_i y p value
          simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at he
          obtain ⟨⟨-, rfl⟩, hm⟩ := he
          unfold Expr.movesBy at hm
          split at hm
          · rename_i o kt l r
            simp only [Bool.and_eq_true, beq_iff_eq, Option.any_eq_true, decide_eq_true_eq] at hm
            obtain ⟨⟨hl, k, hr, -⟩, -⟩ := hm
            rw [Expr.eq_of_readVar? hl]
            cases r <;> simp_all [Expr.intLit?, Expr.contFree, pathContFree, exprsContFree]
          · cases hm
        · cases he
      exact absurd h ((eval_noCont D _ n _ hc s).ne s')

end Stilt
