import Stilt.Ends.While

/-!
# Bodies that halt

Code free of `div` halts from every state whose frame meets its roles, given that the calls
it may make halt (`CallsHalt`): of a function ranked below the one whose body it is, and of
that function itself on an argument at the descending position smaller than the one the
body was called with (`eval_halts`). The proof goes by induction on the depth of the code,
case by case on the expression, as `Stilt.Ends.Runs` runs its parts.
-/

namespace Stilt

/-- The calls that code where `me` says may make halt: of every function it may name, on any
arguments, and of the function whose body it is, on arguments smaller than `m` at its
descending position. -/
def CallsHalt (D : Decls) (w : WriteBack) (lim : Limited) (B : Name → Nat)
    (me : Option (Name × Nat)) (m : Nat) : Prop :=
  (∀ g types rows passed s, lim.names B me g = true →
    Halts (fun n => Eval.call D (Copy.memoryWith w) (eval D (Copy.memoryWith w) n)
      (.function g types rows) passed) (fun _ => True) s) ∧
  (∀ f k, me = some (f, k) → ∀ types rows passed s, Passed.sizeAt passed k < m →
    Halts (fun n => Eval.call D (Copy.memoryWith w) (eval D (Copy.memoryWith w) n)
      (.function f types rows) passed) (fun _ => True) s)

/-- Binding a `let` or a `var` in copy-in, copy-out pushes it on the frame. -/
theorem Copy.bindInit_fst (w : WriteBack) (s : Copy.State) (x : Name) (init : Expr) (v : Value) :
    ((Copy.memoryWith w).bindInit s x init v).1 = (x, v) :: s.1 := by
  cases init <;> rfl

variable {D : Decls} {w : WriteBack} {lim : Limited} {B : Name → Nat} {me : Option (Name × Nat)}
  {m : Nat}

open Halts in
/-- A call of a named function, free of `div` where `me` says, halts. -/
theorem halts_callFn (hC : CallsHalt D w lim B me m) {k : Nat} (ih : HaltsRun D w lim B me m k)
    {f : Name} {types : List Ty} {rows : List Row} {as : List Arg} {R : Roles}
    (hcd : (if Expr.isSelf me (.fnRef f types rows) then descends me R as
      else Expr.divFree lim B me R (.fnRef f types rows)) = true)
    (had : argsDivFree lim B me R as = true) (han : argsDepth as ≤ k) (hA : R.Avoids (argsWrites as))
    (s : Copy.State) (hI : R.Inv s.1 m) :
    Halts (fun n => eval D (Copy.memoryWith w) n (.fnRef f types rows) >>= fun f =>
      Eval.args (eval D (Copy.memoryWith w) n) as >>= fun passed =>
        Eval.callAs D (Copy.memoryWith w) (eval D (Copy.memoryWith w) n) false f passed)
      (fun _ => True) s := by
  have hf : Halts (fun n => eval D (Copy.memoryWith w) n (.fnRef f types rows))
      (fun v => v = .function f types rows) s :=
    ⟨1, .done (.function f types rows) s, rfl, fun n hle => by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rfl⟩
  refine bind hf fun v s' hv hdv => ?_
  have hI' : R.Inv s'.1 m := hI.afterEval (e := .fnRef f types rows) (fun _ _ h => nomatch h) hdv
  refine bind (args ih as had han hA s' hI') fun passed s'' _ hdp => callAs _ _ _ false _ passed ?_
  subst hv
  split at hcd
  · rename_i hself
    obtain ⟨⟨f', k'⟩, hme, hk⟩ := (Option.any_eq_true _ _).1 (by simpa [descends] using hcd)
    obtain ⟨_, hme', hmf⟩ := (Option.any_eq_true _ _).1 (by simpa [Expr.isSelf] using hself)
    rw [hme] at hme'
    cases hme'
    subst hme
    simp only [beq_iff_eq] at hmf
    subst hmf
    obtain ⟨N, hN⟩ := hdp
    exact hC.2 _ k' rfl types rows passed s'' (args_descend N k' as hI' hA hk (hN N (Nat.le_refl _)))
  · exact hC.1 f types rows passed s'' hcd

open Halts in
/-- Evaluating an expression free of `div` where `me` says, within the depth of its text,
halts from every state whose frame meets its roles. -/
theorem eval_halts (hC : CallsHalt D w lim B me m) : ∀ k, HaltsRun D w lim B me m k
  | 0, e, _, _, hn, _, _, _ => absurd hn (by have := e.one_le_depth; omega)
  | k + 1, e, R, hd, hn, hA, s, hI => by
    have ih := eval_halts hC k
    apply Halts.succ
    cases e <;> try simp only [Expr.divFree, Expr.depth, Bool.and_eq_true, Nat.max_le,
      Nat.add_le_add_iff_right] at hd hn
    all_goals try simp only [Expr.writes] at hA
    case var x => exact const (Eval.Ends.inspect _ fun _ _ _ => trivial)
    case move x => exact const (Eval.Ends.inspect _ fun _ _ _ => trivial)
    case int k => exact const (Eval.Ends.pure trivial)
    case bool b => exact const (Eval.Ends.pure trivial)
    case unit => exact const (Eval.Ends.pure trivial)
    case record R' _ fs =>
      exact bind (fields ih fs hd hn hA s hI) fun _ _ _ _ => const (Eval.Ends.declare D R' _)
    case variant T _ C es =>
      exact bind (list ih es hd hn hA s hI) fun _ _ _ _ => const (Eval.Ends.pure trivial)
    case list τ es =>
      exact bind (list ih es hd hn hA s hI) fun _ _ _ _ => const (Eval.Ends.pure trivial)
    case op o es =>
      exact bind (list ih es hd hn hA s hI) fun _ _ _ _ => const (Eval.Ends.world _ _)
    case view es =>
      exact bind (list ih es hd hn hA s hI) fun _ _ _ _ =>
        const (Eval.Ends.ofExcept _ fun _ _ => trivial)
    case field e f =>
      exact bind (ih e R hd hn hA s hI) fun _ _ _ _ => const (Eval.Ends.ofExcept _ fun _ _ => trivial)
    case index e i =>
      have hA₁ : R.Avoids e.writes := hA.mono (List.subset_append_left _ _)
      exact bind (ih e R hd.1 hn.1 hA₁ s hI) fun _ s' _ hd' =>
        bind (bind (ih i R hd.2 hn.2 (hA.mono (List.subset_append_right _ _)) s'
          (hI.afterEval hA₁ hd')) fun v _ _ _ => const (Eval.Ends.asInt v)) fun _ _ _ _ =>
          const (Eval.Ends.ofExcept _ fun _ _ => trivial)
    case fnRef f types rows => exact const (Eval.Ends.pure trivial)
    case method t m τ =>
      refine const (m := Eval.method D t m τ) ?_
      unfold Eval.method
      split
      · split
        · exact Eval.Ends.pure trivial
        · exact Eval.Ends.fail _
      · exact Eval.Ends.fail _
    case closure ps result ρ body =>
      exact bind (const (Eval.Ends.inspect _ fun _ _ _ => trivial)) fun _ _ _ _ =>
        const (Eval.Ends.pure trivial)
    case call callee as _ =>
      obtain ⟨⟨hc, hcd⟩, had⟩ := hd
      obtain ⟨hcn, han, hbn⟩ := hn
      have hA' : R.Avoids (argsWrites as) := hA.mono (List.subset_append_right _ _)
      cases callee
      case fnRef f types rows => exact halts_callFn hC ih hcd had han hA' s hI
      case closure ps result ρ body =>
        have hf : Halts (fun n => eval D (Copy.memoryWith w) n (.closure ps result ρ body))
            (fun v => ∃ c, v = .closure c ps result ρ body) s :=
          Halts.succ (bind (const (Eval.Ends.inspect _ fun _ _ _ => trivial)) fun c _ _ _ =>
            const (Eval.Ends.pure ⟨c, rfl⟩))
        refine bind hf fun v s' hv hdv => bind (args ih as had han hA' s'
          (hI.afterEval (e := .closure ps result ρ body) (fun _ _ h => nomatch h) hdv))
          fun passed s'' _ _ => callAs _ _ _ false _ passed ?_
        obtain ⟨c, rfl⟩ := hv
        simp only [Expr.isSelf, Expr.divFree, Bool.false_eq_true, ↓reduceIte] at hcd
        simp only [Expr.bodyDepth] at hbn
        exact invoke _ c ps passed fun s₀ =>
          ih body [] hcd hbn (Roles.Avoids.nil _) s₀ (Roles.Inv.nil _ _)
      all_goals simp [Expr.callable] at hc
    case letIn x τ init body =>
      have hA₁ : R.Avoids init.writes := hA.mono (List.subset_append_left _ _)
      refine bind (ih init R hd.1 hn.1 hA₁ s hI) fun v s' _ hdv => withInit _ x init v
        (ih body _ hd.2 hn.2 ?_ _ ?_)
      · refine (hA.mono (List.subset_append_right _ _)).cons fun hr => ?_
        split at hr
        · simpa using ‹(decide ¬x ∈ body.writes) = true›
        · exact absurd rfl hr
      · rw [Copy.bindInit_fst]
        refine (hI.afterEval hA₁ hdv).cons ?_
        split
        · exact roleIn_bounds hI hdv
        · trivial
    case varIn x τ init body =>
      have hA₁ : R.Avoids init.writes := hA.mono (List.subset_append_left _ _)
      refine bind (ih init R hd.1 hn.1 hA₁ s hI) fun v s' _ hdv => withInit _ x init v
        (ih body _ hd.2 hn.2 ((hA.mono (List.subset_append_right _ _)).cons fun h => absurd rfl h)
          _ ?_)
      rw [Copy.bindInit_fst]
      exact (hI.afterEval hA₁ hdv).cons trivial
    case assign p value =>
      obtain ⟨x, ps⟩ := p
      simp only [Expr.divFree, Expr.depth, Expr.writes, Bool.and_eq_true, Nat.max_le,
        Nat.add_le_add_iff_right] at hd hn hA
      exact assign ih x hd.1 hn.1 hd.2 hn.2 (hA.mono (List.subset_cons_self _ _)) s hI
    case seq a b =>
      have hA₁ : R.Avoids a.writes := hA.mono (List.subset_append_left _ _)
      exact bind (ih a R hd.1 hn.1 hA₁ s hI) fun _ s' _ hd' =>
        ih b R hd.2 hn.2 (hA.mono (List.subset_append_right _ _)) s' (hI.afterEval hA₁ hd')
    case «if» c τ a b =>
      have hA₁ : R.Avoids c.writes := hA.mono (List.subset_append_left _ _)
      have hA₂ : R.Avoids (a.writes ++ b.writes) := hA.mono (List.subset_append_right _ _)
      exact bind (bind (ih c R hd.1.1 hn.1 hA₁ s hI) fun v _ _ _ => const (Eval.Ends.asBool v))
        fun v s' _ hd' =>
          have hI' := hI.after (keepsBool D w · c) hA₁ hd'
          ite v (ih a R hd.1.2 hn.2.1 (hA₂.mono (List.subset_append_left _ _)) s' hI')
            (ih b R hd.2 hn.2.2 (hA₂.mono (List.subset_append_right _ _)) s' hI')
    case «match» e τ arms =>
      have hA₁ : R.Avoids e.writes := hA.mono (List.subset_append_left _ _)
      exact bind (ih e R hd.1 hn.1 hA₁ s hI) fun v s' _ hdv =>
        select ih hd.2 hn.2 (hA.mono (List.subset_append_right _ _)) v (roleIn_bounds hI hdv) s'
          (hI.afterEval hA₁ hdv)
    case «for» x τ e body =>
      exact loop ih x hd.1 hn.1 (hA.mono (List.subset_append_left _ _)) hd.2 hn.2 s hI
    case raise e => exact bind (ih e R hd hn hA s hI) fun v _ _ _ => const (Eval.Ends.throw v)
    case «try» e => exact ih e R hd hn hA s hI
    case tryCatch e E x h τ =>
      exact handle (ih e R hd.1 hn.1 (hA.mono (List.subset_append_left _ _)) s hI) fun err s' =>
        withVar _ x err (ih h [] hd.2 hn.2 (Roles.Avoids.nil _) _ (Roles.Inv.nil _ _))
    case «while» c body =>
      exact shift (Halts.whileCounts
        (fun s => ih c [] hd.1.1 hn.1 (Roles.Avoids.nil _) s (Roles.Inv.nil _ _))
        (fun s => ih body [] hd.1.2 hn.2 (Roles.Avoids.nil _) s (Roles.Inv.nil _ _)) hd.2 s)
    case «loop» body => simp at hd
    case «break» => exact const (Eval.Ends.jump _)
    case «continue» => exact const (Eval.Ends.jump _)
    case «return» e => exact bind (ih e R hd hn hA s hI) fun v _ _ _ => const (Eval.Ends.jump _)
    case perform => cases hd
    case withH E c h b =>
      have hA₁ : R.Avoids h.writes := hA.mono (List.subset_append_left _ _)
      exact bind (ih h R hd.1 hn.1 hA₁ s hI) fun hv s' _ hd' => letGo _ (handleWith _ E c hv
        (ih b R hd.2 hn.2 (hA.mono (List.subset_append_right _ _)) s' (hI.afterEval hA₁ hd')))
    case held ns hs b =>
      exact bind (list ih hs hd.1 hn.1 (hA.mono (List.subset_append_left _ _)) s hI)
        fun vs _ _ _ => held _ (fun s₀ => ih b [] hd.2 hn.2 (Roles.Avoids.nil _) s₀
          (Roles.Inv.nil _ _)) _ vs

end Stilt
