import Stilt.Panics.Conds

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
      unfold Eval.select at h₂
      cases hsel : selectArm arms u with
      | none => rw [hsel] at h₂; exact nomatch h₂
      | some au =>
        obtain ⟨arm, us⟩ := au
        rw [hsel] at h₂
        dsimp only at h₂
        split at h₂
        · exact withVars_not_reaches (fun s₁ v₁ s₁' => eval_not_reaches n arm.body
            (armsAlwaysJump_mem he (selectArm_mem hsel).1) s₁ v₁ s₁') _ s'' v s' h₂
        · exact nomatch h₂
    case «if» c τ a b =>
      simp only [Bool.and_eq_true] at he
      obtain ⟨g, s'', _, h₂⟩ := Eval.bind_reaches (m := Eval.bind (eval D M n c) Eval.asBool)
        (f := fun g => if g then eval D M n a else eval D M n b) h
      cases g
      · exact eval_not_reaches n b he.2 s'' v s' h₂
      · exact eval_not_reaches n a he.1 s'' v s' h₂

/-- After an `if` whose then-branch always jumps reaches a value, the facts of
its condition's negation hold, but those of what its else-branch writes. -/
theorem after_holds {D : Decls} (w : WriteBack) (n : Nat) (a : Expr) (s : Copy.State) {v : Value}
    {s' : Copy.State} (h : (eval D (Copy.memoryWith w) n a s).Reaches v s') :
    Frame.Meets a.after s'.1 := by
  cases a
  case «if» c τ t e =>
    simp only [Expr.after]
    split
    · rename_i ht
      cases n with
      | zero => cases h
      | succ m =>
        change (Eval.bind (Eval.bind (eval D (Copy.memoryWith w) m c) Eval.asBool)
          (fun b => if b then eval D (Copy.memoryWith w) m t else eval D (Copy.memoryWith w) m e) s).Reaches
            _ _ at h
        obtain ⟨b, s₁, h₁, h₂⟩ := Eval.bind_reaches h
        obtain ⟨u, s₂, h₃, h₄⟩ := Eval.bind_reaches h₁
        obtain ⟨hu, hs⟩ := Eval.asBool_reaches h₄
        subst hu
        cases b
        · have k := h₂.keeps (eval_keeps D w m e e.writes e.resizes (List.Subset.refl _)
            (List.Subset.refl _) s₁)
          exact (eval_facts w m c false s s₁ (by rw [hs]; exact h₃)).keep k.2
        · exact absurd h₂ (eval_not_reaches m t ht s₁ v s')
    · exact Frame.Meets.nil _
  case assign p _ => obtain ⟨_, _⟩ := p; exact Frame.Meets.nil _
  all_goals exact Frame.Meets.nil _

end Stilt
