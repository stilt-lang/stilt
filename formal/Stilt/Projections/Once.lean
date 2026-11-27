import Stilt.Projections.Yield

/-!
# Every path runs the `yield`s its check counts

`eval_yielding`: a run, with any fuel, of code of a projection's body that passes `Expr.once`
yields as its paths do. Code that runs no `yield` keeps what it doesn't write
(`keeps_yielding`); a block runs its statements in turn, a binding's scope ends with its rest,
an `if` and a `match` run one branch, a `catch` runs its handler from what its operand kept, a
`raise` and a panic end their paths, a `return` gives the value kept once a `yield` has run, and
a `yield` keeps the access's value (`yield_yielding`).
-/

namespace Stilt

/-- Running code that passes `Expr.once` yields as its paths do. -/
def YieldingRun (run : Expr → Eval Copy.State Value) : Prop :=
  ∀ (e : Expr) (res k : Name) (caught : Bool) (n : Nat) (N : List Name), n ≤ 1 →
    e.once res k caught n ≠ none →
      Eval.Yielding res N n (e.once res k caught n) (fun _ => True) (run e)

variable (D : Decls)

theorem Expr.isYielded_eq {res : Name} {e : Expr} (h : e.isYielded res = true) :
    e = .form .yielded (.index (.var res) (.int 0)) := by
  unfold Expr.isYielded at h
  split at h
  · rename_i x
    simp only [beq_iff_eq] at h
    rw [h]
  · cases h

theorem Expr.yieldOperand?_eq {res : Name} {m a : Expr} (h : m.yieldOperand? res = some a) :
    m = .assign ⟨res, []⟩ (.op (.list .push) [.var res, .try a]) := by
  unfold Expr.yieldOperand? at h
  split at h
  · rename_i x y a'
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      cases h
      rw [hc.1, hc.2]
    · cases h
  · cases h

theorem select_yielding (fuel : Nat) (ih : YieldingRun (eval D Copy.memory fuel)) {arms : List Arm}
    {res k : Name} {caught : Bool} {n : Nat} {N : List Name} (hn : n ≤ 1)
    (hr : armsOnce res k caught n arms ≠ none) (v : Value) :
    Eval.Yielding res N n (armsOnce res k caught n arms) (fun _ => True)
      (Eval.select Copy.memory (eval D Copy.memory fuel) arms v) := by
  refine Eval.select_of (Eval.Yielding res N n (armsOnce res k caught n arms) (fun _ => True))
    (.inl fun s _ => Outcome.Yielding.fault .stuck s) (.inl fun s _ => Outcome.Yielding.fault .stuck s)
    (fun arm ha _ us _ _ => ?_) (fun arm ha g hg us _ _ m hm => ?_)
  · obtain ⟨hb, _, hbody, hm⟩ := armsOnce_mem hr ha
    refine Eval.Yielding.withVars _ (fun p hp => fun he => hb (he ▸ (List.of_mem_zip hp).1)) ?_
    exact Eval.Yielding.mono (fun _ h => h) hm (ih _ _ _ _ _ _ hn hbody)
  · obtain ⟨hb, hgd, hbody, hm'⟩ := armsOnce_mem hr ha
    have hz : ∀ p ∈ arm.binders.zip us, p.1 ≠ res := fun p hp he => hb (he ▸ (List.of_mem_zip hp).1)
    unfold Eval.tryWay
    refine Eval.Yielding.bind (r := some (some n)) (P := fun _ => True)
      (Eval.Yielding.withVars _ hz (Eval.Yielding.bind (keeps_yielding D fuel (hgd g hg) hn)
        fun u _ _ _ hk => by cases hk; exact Eval.Yielding.asBool u hn)) fun b _ _ _ hk => ?_
    cases hk
    cases b
    · exact hm
    · exact Eval.Yielding.withVars _ hz
        (Eval.Yielding.mono (fun _ h => h) hm' (ih _ _ _ _ _ _ hn hbody))

/-- A `catch` whose operand runs no `yield`. -/
theorem tryCatch_yielding (fuel : Nat) (ih : YieldingRun (eval D Copy.memory fuel))
    {e h : Expr} {x res k : Name} {caught : Bool} {n : Nat} {N : List Name} (hn : n ≤ 1)
    (hx : x ≠ res) (he : e.keeps res k true n = true)
    (hr : Yields.join (some (some n)) (h.once res k caught n) ≠ none) :
    Eval.Yielding res N n (Yields.join (some (some n)) (h.once res k caught n)) (fun _ => True)
      (Eval.handle (eval D Copy.memory fuel e) fun err =>
        Eval.withVar Copy.memory x err (eval D Copy.memory fuel h)) := by
  intro s hs
  have hj := (Yields.join_left hr).2 n rfl
  exact Outcome.Yielding.handle_of_keeps (Expr.keeps_parts he).1 hn hs hj
    (fun err s' hs' => Eval.Yielding.withVar hx err
      (Eval.Yielding.mono (fun _ h => h) (Yields.join_right hr).2
        (ih _ _ _ _ _ _ hn (Yields.join_right hr).1)) s' hs')
    (eval_keeps D .leftToRight fuel e e.writes e.resizes (fun _ h => h) (fun _ h => h) s)
    (eval_exits D Copy.memory fuel false (n == 1) e (Expr.keeps_parts he).2 s)

/-- A panic, which ends its paths. -/
theorem panic_noDone (fuel : Nat) {o : Op} (ho : o.isPanic = true) (es : List Expr) (s : Copy.State) :
    (eval D Copy.memory (fuel + 1) (.op o es) s).NoDone := by
  obtain ⟨p, rfl⟩ : ∃ p, o = .panic p := by
    cases o <;> first | exact ⟨_, rfl⟩ | simp [Op.isPanic] at ho
  show ((Eval.list (eval D Copy.memory fuel) es s).bind fun vs s' =>
    Eval.world Copy.memory ((Op.panic p).run vs) s').NoDone
  refine Outcome.NoDone.bind fun vs s' => ?_
  obtain ⟨fr, w⟩ := s'
  have h : (Op.panic p).run vs w = .error (.panic p) := rfl
  show (Eval.world Copy.frames.withWorld ((Op.panic p).run vs) (fr, w)).NoDone
  rw [Eval.world_error h]
  trivial

open Eval.Yielding in
/-- **Every path through a projection's body runs the `yield`s its check counts**, with any
fuel (projections.once-on-every-path). -/
theorem eval_yielding : ∀ fuel, YieldingRun (eval D Copy.memory fuel)
  | 0 => fun _ _ _ _ _ _ _ _ _ _ => trivial
  | fuel + 1 => fun e res k caught n N hn hr => by
    have ih := eval_yielding fuel
    cases e
    case seq a b =>
      simp only [Expr.once] at hr ⊢
      have hr' := Yields.andThen_ne hr
      refine bind (ih a res k caught n N hn hr'.1) fun _ m _ hm1 hm => ?_
      rw [hr'.2 m hm]
      exact ih b res k caught m N hm1 (hr'.2 m hm ▸ hr)
    case letIn x τ init body | varIn x τ init body =>
      simp only [Expr.once] at hr ⊢
      split at hr
      · rename_i hc
        simp only [hc, ↓reduceIte] at hr ⊢
        simp only [Bool.and_eq_true, bne_iff_ne] at hc
        have hr' := Yields.andThen_ne hr
        refine bind (ih init res k caught n N hn hr'.1) fun v m _ hm1 hm => ?_
        rw [hr'.2 m hm]
        exact withInit hc.1 init v (ih body res k caught m (x :: N) hm1 (hr'.2 m hm ▸ hr))
      · exact absurd rfl hr
    case «if» c τ a b =>
      simp only [Expr.once] at hr ⊢
      split at hr
      · rename_i hc
        simp only [hc, ↓reduceIte] at hr ⊢
        refine bind (r := some (some n)) (P := fun _ => True) (bind (keeps_yielding D fuel hc hn)
          fun u _ _ _ hk => by cases hk; exact asBool u hn) fun b _ _ _ hk => ?_
        cases hk
        cases b
        · exact mono (fun _ h => h) (Yields.join_right hr).2 (ih _ _ _ _ _ _ hn (Yields.join_right hr).1)
        · exact mono (fun _ h => h) (Yields.join_left hr).2 (ih _ _ _ _ _ _ hn (Yields.join_left hr).1)
      · exact absurd rfl hr
    case «match» e τ arms =>
      simp only [Expr.once] at hr ⊢
      split at hr
      · rename_i hc
        simp only [hc, ↓reduceIte] at hr ⊢
        exact bind (keeps_yielding D fuel hc hn) fun v _ _ _ hk => by
          cases hk; exact select_yielding D fuel ih hn hr v
      · exact absurd rfl hr
    case tryCatch e E x h τ =>
      simp only [Expr.once] at hr ⊢
      split at hr
      · rename_i hc
        simp only [hc, ↓reduceIte] at hr ⊢
        simp only [Bool.and_eq_true, bne_iff_ne] at hc
        exact tryCatch_yielding D fuel ih hn hc.1.1 hc.2 hr
      · exact absurd rfl hr
    case raise e =>
      simp only [Expr.once] at hr ⊢
      split at hr
      · rename_i hc
        simp only [hc, ↓reduceIte]
        simp only [Bool.and_eq_true] at hc
        exact bind (keeps_yielding D fuel hc.2 hn) fun v m _ hm1 _ s hs => ⟨m, hm1, hs⟩
      · exact absurd rfl hr
    case «try» e =>
      simp only [Expr.once] at hr ⊢
      split at hr
      · rename_i hc
        subst hc
        simp only [↓reduceIte] at hr ⊢
        exact ih e res k true n N hn hr
      · exact absurd rfl hr
    case «return» e =>
      simp only [Expr.once] at hr ⊢
      split at hr
      · rename_i hc
        simp only [hc, ↓reduceIte]
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨hy, rfl⟩ := hc
        rw [Expr.isYielded_eq hy]
        refine bind (keeps_yielding' D fuel (e := .form .yielded (.index (.var res) (.int 0)))
          (by simp [Expr.writes]) (by simp [Expr.exits]) hn) fun v m _ _ hm s hs => ?_
        cases hm
        exact hs
      · exact absurd rfl hr
    case «break» => exact absurd rfl hr
    case «continue» => exact absurd rfl hr
    case op o es =>
      by_cases hp : o.isPanic = true
      · have h' : (Expr.op o es).once res k caught n =
            if (Expr.op o es).keeps res k caught n then some none else none := by
          simp [Expr.once, hp]
        rw [h'] at hr ⊢
        split at hr
        · rename_i hc
          simp only [hc, ↓reduceIte]
          intro s hs
          exact Outcome.Yielding.of_noDone (panic_noDone D fuel hp es s)
            (keeps_yielding D (fuel + 1) hc hn s hs)
        · exact absurd rfl hr
      · have h' : (Expr.op o es).once res k caught n =
            Yields.kept n ((Expr.op o es).keeps res k caught n) := by
          simp [Expr.once, hp]
        exact kept_yielding D (fuel + 1) h' hn hr
    case form f m =>
      cases f
      case «yield» =>
        simp only [Expr.once] at hr ⊢
        split at hr
        · rename_i a ha
          try simp only [ha]
          split at hr
          · rename_i hc
            simp only [hc, ↓reduceIte]
            simp only [Bool.and_eq_true, beq_iff_eq] at hc
            obtain ⟨rfl, hy⟩ := hc
            rw [Expr.yieldOperand?_eq ha]
            simp only [Expr.yieldOperand, Bool.and_eq_true] at hy
            exact yield_yielding D (by simpa using hy.1.1.2) hy.1.2 fuel
          · exact absurd rfl hr
        · exact absurd rfl hr
      case letElse | orElse | compound | intFloat | optionField | spawn | await | scope | scopeSpawn
          | async | lazyNew | lazyGet =>
        exact ih m res k caught n N hn hr
      case project | writes | through => exact kept_yielding D (fuel + 1) rfl hn hr
      case yielded | projection => exact absurd rfl hr
    all_goals exact kept_yielding D (fuel + 1) rfl hn hr

end Stilt
