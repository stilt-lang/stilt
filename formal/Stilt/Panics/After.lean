import Stilt.Panics.Conds
import Stilt.Panics.Stored
import Stilt.Selection

/-!
# The code after an `if` that jumps

When the then-branch of an `if` always jumps, ending in `return`, `break`,
`continue` or `raise`, the code after the `if` runs only when the condition
was false, so it may count on the facts that the condition's negation gives
(facts.guarding-tests): `if d == 0 { return 0 }` followed by `n / d`.
-/

namespace Stilt

variable {lim : Limited}

/-- Bindings around a step that never reaches a value keep it so. -/
theorem withVars_not_reaches {σ : Type} {M : Memory σ} {m : Eval σ Value}
    (hm : ∀ s v s', ¬ (m s).Reaches v s') :
    ∀ (bs : List (Name × Value)) s v s', ¬ (Eval.withVars M bs m s).Reaches v s'
  | [], s, v, s' => hm s v s'
  | (x, u) :: bs, s, v, s' => fun h => by
    obtain ⟨_, h', _⟩ := Outcome.Reaches.unbind M h
    exact withVars_not_reaches hm bs _ _ _ h'

/-- Code that always jumps never reaches a value, in any model of memory. -/
theorem eval_not_reaches {σ : Type} {D : Decls} {M : Memory σ} :
    ∀ n (e : Expr), e.alwaysJumps = true → ∀ s v s', ¬ (eval D M n e s).Reaches v s'
  | 0, _, _, _, _, _ => fun h => nomatch h
  | n + 1, e, he, s, v, s' => fun h => by
    cases e <;> simp only [Expr.alwaysJumps, reduceCtorEq] at he
    case «break» => exact nomatch h
    case «continue» => exact nomatch h
    case «return» e =>
      obtain ⟨_, _, _, h₂⟩ := Eval.bind_reaches (m := eval D M n e) (f := fun v => Eval.jump (.ret v)) h
      exact nomatch h₂
    case raise e =>
      obtain ⟨_, _, _, h₂⟩ := Eval.bind_reaches (m := eval D M n e) (f := Eval.throw) h
      exact nomatch h₂
    case seq a b =>
      obtain ⟨_, _, _, h₂⟩ := Eval.bind_reaches (m := eval D M n a) (f := fun _ => eval D M n b) h
      exact eval_not_reaches n b he _ _ _ h₂
    case letIn x τ init b =>
      obtain ⟨u, _, _, h₂⟩ := Eval.bind_reaches (m := eval D M n init)
        (f := fun v => Eval.withInit M x init v (eval D M n b)) h
      obtain ⟨_, h₃, _⟩ := Outcome.Reaches.unbind M h₂
      exact eval_not_reaches n b he _ _ _ h₃
    case varIn x τ init b =>
      obtain ⟨u, _, _, h₂⟩ := Eval.bind_reaches (m := eval D M n init)
        (f := fun v => Eval.withInit M x init v (eval D M n b)) h
      obtain ⟨_, h₃, _⟩ := Outcome.Reaches.unbind M h₂
      exact eval_not_reaches n b he _ _ _ h₃
    case «match» e τ arms =>
      obtain ⟨u, s'', _, h₂⟩ := Eval.bind_reaches (m := eval D M n e)
        (f := fun u => Eval.select M (eval D M n) arms u) h
      refine Eval.select_of (fun m => ∀ s v s', ¬ (m s).Reaches v s')
        (.inl fun _ _ _ h => nomatch h) (.inl fun _ _ _ h => nomatch h)
        (fun arm ha _ _ _ _ => withVars_not_reaches (fun s₁ v₁ s₁' => eval_not_reaches n arm.body
          (armsAlwaysJump_mem he ha) s₁ v₁ s₁') _)
        (fun arm ha _ _ _ _ _ m hm s₁ v₁ s₁' h₃ => ?_) s'' v s' h₂
      obtain ⟨b, s₂, _, h₄⟩ := Eval.bind_reaches h₃
      cases b
      · exact hm _ _ _ h₄
      · exact withVars_not_reaches (fun s₃ v₃ s₃' => eval_not_reaches n arm.body
          (armsAlwaysJump_mem he ha) s₃ v₃ s₃') _ _ _ _ h₄
    case «if» c τ a b =>
      simp only [Bool.and_eq_true] at he
      obtain ⟨g, s'', _, h₂⟩ := Eval.bind_reaches (m := Eval.bind (eval D M n c) Eval.asBool)
        (f := fun g => if g then eval D M n a else eval D M n b) h
      cases g
      · exact eval_not_reaches n b he.2 s'' v s' h₂
      · exact eval_not_reaches n a he.1 s'' v s' h₂

/-- After code reaches a value, the facts it gives the code after it hold: a store's key, the
negation of the condition of an `if` whose then-branch always jumps, but for what its
else-branch writes, the facts both paths of another `if` give, and those of a sequence's
parts, the first part's that the second doesn't write. -/
theorem after_holds {D : Decls} (w : WriteBack) : ∀ (n : Nat) (a : Expr) (s : Copy.State) {v : Value}
    {s' : Copy.State}, (eval D (Copy.memoryWith w) n a s).Reaches v s' → Frame.Meets a.after s'.1
  | 0, _, _, _, _, h => nomatch h
  | n + 1, a, s, v, s', h => by
    unfold Expr.after
    refine Frame.Meets.append ?_ ?_
    · split
      · rename_i m kt hk
        intro f hf
        simp only [List.mem_singleton] at hf
        subst hf
        exact eval_stored_holds hk h
      · exact Frame.Meets.nil _
    cases a
    case «if» c τ t e =>
      change (Eval.bind (Eval.bind (eval D (Copy.memoryWith w) n c) Eval.asBool)
        (fun b => if b then eval D (Copy.memoryWith w) n t else eval D (Copy.memoryWith w) n e) s).Reaches
          _ _ at h
      obtain ⟨b, s₁, h₁, h₂⟩ := Eval.bind_reaches h
      obtain ⟨u, s₂, h₃, h₄⟩ := Eval.bind_reaches h₁
      obtain ⟨hu, hs⟩ := Eval.asBool_reaches h₄
      subst hu
      have hneg : b = false → Frame.Meets (withoutNames c.negFacts e.writes ++ e.after) s'.1 := by
        intro hb
        subst hb
        have k := h₂.keeps (eval_keeps D w n e e.writes e.resizes (List.Subset.refl _)
          (List.Subset.refl _) s₁)
        exact ((eval_facts w n c false s s₁ (by rw [hs]; exact h₃)).keep k.2).append
          (after_holds w n e s₁ h₂)
      dsimp only
      split
      · rename_i ht
        cases b
        · exact (hneg rfl).mono (List.subset_append_left _ _)
        · exact absurd h₂ (eval_not_reaches n t ht s₁ v s')
      · intro f hf
        rw [List.mem_filter] at hf
        cases b
        · exact hneg rfl f (by simpa using hf.2)
        · exact after_holds w n t s₁ h₂ f hf.1
    case seq a b =>
      change ((Eval.bind (eval D (Copy.memoryWith w) n a) fun _ => eval D (Copy.memoryWith w) n b) s).Reaches
        _ _ at h
      obtain ⟨_, s₁, h₁, h₂⟩ := Eval.bind_reaches h
      have k := h₂.keeps (eval_keeps D w n b b.writes b.resizes (List.Subset.refl _)
        (List.Subset.refl _) s₁)
      exact (after_holds w n b s₁ h₂).append ((after_holds w n a s h₁).keep k.2)
    case assign p _ => obtain ⟨_, _⟩ := p; exact Frame.Meets.nil _
    all_goals (dsimp only; exact Frame.Meets.nil _)

end Stilt
