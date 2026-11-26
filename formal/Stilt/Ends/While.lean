import Stilt.Ends.Runs
import Stilt.Ends.Counter

/-!
# Counting loops halt

A `while` that counts halts from every state, in copy-in, copy-out
(`Halts.whileCounts`). Its counter's distance from its bound, in turns, is a
number that every turn the loop goes on after brings down: the condition held,
so the counter hadn't passed the bound; the body stepped the counter toward
it; and neither wrote what the bound reads, so the bound kept its value
(`Bound.val_congr`). A turn that doesn't go on ends the loop.
-/

namespace Stilt

/-- How many turns at most a counter at `x` has left before it passes `y`. -/
def countDistance (grow : Bool) (x y : Int) : Nat := (if grow then y - x + 1 else x - y + 1).toNat

/-- The distance of a frame's counter from its bound, `0` when either has no integer. -/
def Bound.distance (v : Name) (grow : Bool) (b : Bound) (s : Copy.Frame) : Nat :=
  match s.lookup v, b.val s with
  | some (.int x), some y => countDistance grow x y
  | _, _ => 0

/-- A step after a test that held brings the distance down. -/
theorem countDistance_step {cmp : Cmp} {grow : Bool} (hg : cmp.counts = some grow) {x y k : Int}
    (hxy : cmp.ints x y = true) (hk : 0 < k) :
    countDistance grow (stepped grow x k) y < countDistance grow x y := by
  cases cmp <;> simp only [Cmp.counts, Option.some.injEq, reduceCtorEq] at hg <;> subst hg <;>
    simp only [Cmp.ints, decide_eq_true_eq] at hxy <;>
    simp only [countDistance, stepped, ↓reduceIte, Bool.false_eq_true] <;> omega

variable {D : Decls} {w : WriteBack}

/-- The frame a family's run reaches, at some fuel. -/
theorem done_at {α : Type} {F : Nat → Eval Copy.State α} {s s' : Copy.State} {a : α}
    (h : ∃ N, ∀ n, N ≤ n → F n s = .done a s') : ∃ n, F n s = .done a s' :=
  let ⟨N, hN⟩ := h
  ⟨N, hN N (Nat.le_refl _)⟩

/-- A condition that counts and holds, and what it leaves the body. -/
theorem count_holds {c : Expr} {v : Name} {cmp : Cmp} {b : Bound} (hc : (v, cmp, b) ∈ c.countings)
    (hvc : v ∉ c.writes) (hrc : ∀ x ∈ b.reads, x ∉ c.writes) {n : Nat} {s s₁ : Copy.State} {g : Bool}
    (h : (eval D (Copy.memoryWith w) n c >>= Eval.asBool) s = .done g s₁) (hg : g = true) :
    ∃ x y, s.1.lookup v = some (.int x) ∧ b.val s.1 = some y ∧ s₁.1.lookup v = some (.int x) ∧
      b.val s₁.1 = some y ∧ cmp.ints x y = true := by
  subst hg
  obtain ⟨u, s₂, h₁, h₂⟩ := Eval.bind_done h
  obtain ⟨rfl, rfl⟩ := Eval.asBool_done h₂
  obtain ⟨x, y, hx, hy, hxy⟩ := eval_count hc (.of_eq h₁)
  have keep := eval_keeps D w n c c.writes c.resizes (List.Subset.refl _) (List.Subset.refl _) s
  rw [h₁] at keep
  refine ⟨x, y, hx, hy, by rw [keep.2.lookup hvc, hx], ?_, hxy⟩
  rw [Bound.val_congr b fun z hz => keep.2.lookup (hrc z hz), hy]

/-- A turn that goes on has stepped the counter, and kept the bound. -/
theorem turn_steps {body : Expr} {v : Name} {grow : Bool} {b : Bound} (hs : body.steps v grow = true)
    (hrb : ∀ x ∈ b.reads, x ∉ body.writes) {n : Nat} {s₁ s₂ : Copy.State} {x y : Int}
    (hx : s₁.1.lookup v = some (.int x)) (hy : b.val s₁.1 = some y)
    (h : Eval.turn (eval D (Copy.memoryWith w) n body) s₁ = .done true s₂) :
    ∃ k, 0 < k ∧ s₂.1.lookup v = some (.int (stepped grow x k)) ∧ b.val s₂.1 = some y := by
  have keep := eval_keeps D w n body body.writes body.resizes (List.Subset.refl _) (List.Subset.refl _) s₁
  unfold Eval.turn Outcome.turn at h
  have hgo : (∃ u, eval D (Copy.memoryWith w) n body s₁ = .done u s₂) ∨
      eval D (Copy.memoryWith w) n body s₁ = .jumped .cont s₂ := by
    split at h <;> simp only [Outcome.done.injEq, reduceCtorEq, Bool.false_eq_true, false_and] at h
    · rename_i u s' he; exact .inl ⟨u, by rw [he, h.2]⟩
    · rename_i s' he; exact .inr (by rw [he, h.2])
  obtain ⟨k, hk, hl⟩ := eval_steps hs hx hgo
  have hk₂ : Frame.Keeps body.writes body.resizes s₁.1 s₂.1 := by
    rcases hgo with ⟨u, he⟩ | he <;> rw [he] at keep
    · exact keep.2
    · exact keep
  exact ⟨k, hk, hl, by rw [Bound.val_congr b fun z hz => hk₂.lookup (hrb z hz), hy]⟩

/-- A `while` that counts halts from every state, given that its condition and body do. -/
theorem Halts.whileCounts {c body : Expr}
    (hcH : ∀ s, Halts (fun n => eval D (Copy.memoryWith w) n c) (fun _ => True) s)
    (hbH : ∀ s, Halts (fun n => eval D (Copy.memoryWith w) n body) (fun _ => True) s)
    (hct : Expr.countsIn c body = true) (s : Copy.State) :
    Halts (fun n => eval D (Copy.memoryWith w) n (.while c body)) (fun _ => True) s := by
  unfold Expr.countsIn at hct
  obtain ⟨⟨v, cmp, b⟩, hc, hct⟩ := List.any_eq_true.1 hct
  dsimp only at hct
  split at hct
  · rename_i grow hg
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hct
    obtain ⟨⟨hs, hvc⟩, hreads⟩ := hct
    suffices H : ∀ T (s : Copy.State), b.distance v grow s.1 < T →
        Halts (fun n => eval D (Copy.memoryWith w) n (.while c body)) (fun _ => True) s from
      H _ s (Nat.lt_succ_self _)
    intro T
    induction T with
    | zero => intro s h; exact absurd h (Nat.not_lt_zero _)
    | succ T ihT =>
      intro s hdist
      apply Halts.succ
      have hW : (fun n => eval D (Copy.memoryWith w) (n + 1) (.while c body)) = fun n =>
          (eval D (Copy.memoryWith w) n c >>= Eval.asBool) >>= fun g =>
            if g then (Eval.turn (eval D (Copy.memoryWith w) n body) >>= fun g' =>
              if g' then eval D (Copy.memoryWith w) n (.while c body) else Pure.pure Value.unit)
            else Pure.pure Value.unit := by
        funext n; rfl
      rw [hW]
      refine Halts.bind (Halts.bind (hcH s) fun u _ _ _ => Halts.const (Eval.Ends.asBool u))
        fun g s₁ _ hd => ?_
      cases g
      · exact Halts.const (Eval.Ends.pure trivial)
      · obtain ⟨n₁, h₁⟩ := done_at hd
        obtain ⟨x, y, hx, hy, hx₁, hy₁, hxy⟩ := count_holds hc hvc (fun z hz => (hreads z hz).2) h₁ rfl
        refine Halts.bind (Halts.turn (hbH s₁)) fun g' s₂ _ hd₂ => ?_
        cases g'
        · exact Halts.const (Eval.Ends.pure trivial)
        · obtain ⟨n₂, h₂⟩ := done_at hd₂
          obtain ⟨k', hk', hl, hb₂⟩ := turn_steps hs (fun z hz => (hreads z hz).1) hx₁ hy₁ h₂
          have hlt : b.distance v grow s₂.1 < T := by
            have e₂ : b.distance v grow s₂.1 = countDistance grow (stepped grow x k') y := by
              simp [Bound.distance, hl, hb₂]
            have e₁ : b.distance v grow s.1 = countDistance grow x y := by simp [Bound.distance, hx, hy]
            have := countDistance_step hg hxy hk'
            omega
          exact ihT s₂ hlt
  · cases hct

end Stilt
