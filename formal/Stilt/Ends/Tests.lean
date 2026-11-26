import Stilt.Ends.Descent

/-!
# Tests that guard a counter

A test that held, read as a comparison of a counter with its bound toward which it goes,
shows the counter short of its bound (`Roles.Inv.held`), and so does the negation of a
comparison that failed, `n <= 0` in its `else` branch (`eval_negated`): the test's
variables keep their values after it, since nothing writes a variable with a role
(facts.guarding-tests and facts.shrinking-recursion).
-/

namespace Stilt

theorem Cmp.negate_ints (c : Cmp) (x y : Int) : c.negate.ints x y = !c.ints x y := by
  cases c <;> simp only [Cmp.negate, Cmp.ints] <;> first
    | (simp only [bne, Bool.not_not])
    | (simp only [bne])
    | (rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]; omega)

/-- A comparison that counts toward `grow` and holds puts its left side short of its right. -/
theorem Cmp.counts_guard {c : Cmp} {grow : Bool} {x y : Int} (hc : c.counts = some grow)
    (h : c.ints x y = true) : if grow then x ≤ y else y ≤ x := by
  cases c <;> simp only [Cmp.counts, Option.some.injEq, reduceCtorEq] at hc <;> subst hc <;>
    simp only [Cmp.ints, decide_eq_true_eq] at h <;> simp only [↓reduceIte, Bool.false_eq_true] <;>
    omega

variable {D : Decls} {w : WriteBack}

/-- A comparison that failed makes its negation hold, from the same state, at the same fuel. -/
theorem eval_negated {c : Expr} {n : Nat} {s s' : Copy.State} {r : Name × Cmp × Bound}
    (hr : r ∈ c.negated.countings)
    (h : eval D (Copy.memoryWith w) n c s = .done (.bool false) s') :
    eval D (Copy.memoryWith w) n c.negated s = .done (.bool true) s' := by
  unfold Expr.negated at hr ⊢
  split at hr
  · rename_i cmp t l r'
    cases n with
    | zero => cases h
    | succ m =>
      change Eval.bind (Eval.list (eval D (Copy.memoryWith w) m) [l, r']) (fun vs =>
        Eval.world (Copy.memoryWith w) (Op.run (.compare cmp t) vs)) s = _ at h
      change Eval.bind (Eval.list (eval D (Copy.memoryWith w) m) [l, r']) (fun vs =>
        Eval.world (Copy.memoryWith w) (Op.run (.compare cmp.negate t) vs)) s = _
      obtain ⟨vs, s₁, h₁, h₂⟩ := Eval.bind_done h
      rw [Eval.world_memoryWith_of_ne w (fun _ h => by cases h)] at h₂
      obtain ⟨ha, rfl⟩ := Eval.ofExcept_done h₂
      obtain ⟨_, _, _, -, -, rfl⟩ := Eval.list_pair_reaches (.of_eq h₁)
      obtain ⟨x, y, rfl, rfl, hv⟩ := compare_apply ha
      simp only [Value.bool.injEq] at hv
      unfold Eval.bind Outcome.bind
      rw [h₁]
      dsimp only
      rw [Eval.world_memoryWith_of_ne w (fun _ h => by cases h)]
      have : Op.apply (.compare cmp.negate t) [.int x, .int y] = .ok (.bool (cmp.negate.ints x y)) := by
        simp [Op.apply, Op.applyScalars, Value.scalar?, Op.compute, Functor.map, Except.map,
          Scalar.value]
      rw [this, Cmp.negate_ints, ← hv]
      rfl
  · simp [Expr.countings] at hr

variable {me : Option (Name × Descent)} {R : Roles} {m : Meas}

/-- A test that held, from a frame that meets the roles, gives the frame the code after it
runs in the roles with its counter guarded, when nothing it ran wrote a variable with a
role. -/
theorem Roles.Inv.held {c : Expr} {n : Nat} {s s₁ : Copy.State} {W L : List Name}
    (hfit : ∀ f d, me = some (f, d) → m.Fits d) (hI : R.Inv s.1 m)
    (hc : ∀ r ∈ c.countings, ∃ s₂, (eval D (Copy.memoryWith w) n c s).Reaches (.bool true) s₂)
    (hk : Frame.Keeps W L s.1 s₁.1) (hA : R.Avoids W) : (R.held me c).Inv s₁.1 m := by
  have hI₁ : R.Inv s₁.1 m := hI.keep hA hk
  unfold Roles.held
  split
  · rename_i f k grow b
    split
    · rename_i v cmp bnd hfind
      have hmem := List.mem_of_find?_eq_some hfind
      have hg := List.find?_some hfind
      obtain ⟨s₂, hreach⟩ := hc _ hmem
      obtain ⟨x, y, hx, hy, hxy⟩ := eval_count hmem hreach
      simp only [guardReading, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hg
      obtain ⟨⟨hrole, hcounts⟩, hbnd⟩ := hg
      have hfit' := hfit _ _ rfl
      have hne : R.of v ≠ .other := by rcases hrole with h | h <;> rw [h] <;> exact nofun
      have hx₁ : s₁.1.lookup v = some (.int x) := by rw [hk.lookup (hA v hne), hx]
      have hstart : m.start = some x := by
        obtain ⟨u, hu, hh⟩ := hI v hne
        rw [hx] at hu
        cases hu
        rcases hrole with h | h <;> rw [h] at hh
        · exact hh.symm
        · obtain ⟨x', y', hs, -, he, -⟩ := hh
          cases he
          exact hs
      have hlimit : m.limit = some y := by
        cases b with
        | lit c₀ =>
          cases bnd <;> simp only [beq_iff_eq, reduceCtorEq] at hbnd
          subst hbnd
          simp only [Bound.val, Option.some.injEq] at hy
          subst hy
          exact hfit'.2.1 _ rfl
        | param j =>
          cases bnd <;> simp only [beq_iff_eq, reduceCtorEq] at hbnd
          rename_i q
          obtain ⟨u, hu, hh⟩ := hI q (by rw [hbnd]; exact nofun)
          rw [hbnd] at hh
          simp only [Bound.val, hu] at hy
          cases u <;> simp only [reduceCtorEq] at hy
          cases hy
          exact hh.symm
      intro z hz
      simp only [Roles.of_cons] at hz ⊢
      by_cases hzv : z = v
      · subst hzv
        simp only [↓reduceIte]
        refine ⟨.int x, hx₁, x, y, hstart, hlimit, rfl, ?_, ?_⟩
        · rw [hfit'.1]; exact Cmp.counts_guard hcounts hxy
        · rw [hfit'.1]; exact hfit'.2.2 x y hstart hlimit
      · simp only [hzv, ↓reduceIte] at hz ⊢
        exact hI₁ z hz
    · exact hI₁
  · exact hI₁

/-- The roles after a test avoid what the roles before it avoid. -/
theorem Roles.Avoids.held {c : Expr} {W : List Name} (hA : R.Avoids W) : (R.held me c).Avoids W := by
  unfold Roles.held
  split
  · split
    · rename_i v cmp bnd hfind
      have hg := List.find?_some hfind
      simp only [guardReading, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hg
      refine hA.cons fun _ => hA v ?_
      rcases hg.1.1 with h | h <;> rw [h] <;> exact nofun
    · exact hA
  · exact hA

end Stilt
