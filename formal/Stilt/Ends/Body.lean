import Stilt.Ends.While
import Stilt.Ends.Tests

/-!
# Bodies that halt

Code free of `div` halts from every state whose frame meets its roles, given that the calls
it may make halt (`CallsHalt`): of a function ranked below the one whose body it is, and of
that function itself on arguments whose measure is smaller than the call's the body runs, each
on arguments that pass function values that halt where the function's body calls through its
parameters, and through a non-escaping parameter, whose value the call vouches halts
(`eval_halts`). An argument written as a closure literal free of `div`, a function that asks
nothing of its arguments, or such a parameter halts so (`haltingArg_halts`). The proof goes by induction on the depth of the code,
case by case on the expression, as `Stilt.Ends.Runs` runs its parts.
-/

namespace Stilt

/-- A function value that halts: a call of it, on any arguments and from any state, halts,
from some fuel on. -/
def Value.Halting (D : Decls) (w : WriteBack) (v : Value) : Prop :=
  ∀ (passed : List Passed) (s : Copy.State),
    Halts (fun n => Eval.call D (Copy.memoryWith w) (eval D (Copy.memoryWith w) n) v passed)
      (fun _ => True) s

/-- The arguments at the positions `ks` pass function values that halt, by value. -/
def Passed.HaltAt (D : Decls) (w : WriteBack) (ks : List Nat) (passed : List Passed) : Prop :=
  ∀ k ∈ ks, ∃ a u, passed[k]? = some a ∧ (a = .value u ∨ ∃ z, a = .moved z u) ∧ u.Halting D w

/-- The calls that code where `me` says may make halt: of every function it may name, on
arguments that halt where the function's body calls through its parameters (`H`), and of the
function whose body it is, on such arguments whose measure is smaller than the call's, of
which `m` is what the body knows; and the function values that the body's non-escaping
parameters hold halt. -/
structure CallsHalt (D : Decls) (w : WriteBack) (lim : Limited) (B : Name → Nat)
    (H : Name → List Nat) (me : Option (Name × Descent)) (m : Meas) : Prop where
  names : ∀ g types rows passed s, lim.names B me g = true → Passed.HaltAt D w (H g) passed →
    Halts (fun n => Eval.call D (Copy.memoryWith w) (eval D (Copy.memoryWith w) n)
      (.function g types rows) passed) (fun _ => True) s
  self : ∀ f d, me = some (f, d) → ∀ types rows passed s, d.measure passed < m.size →
    Passed.HaltAt D w (H f) passed →
    Halts (fun n => Eval.call D (Copy.memoryWith w) (eval D (Copy.memoryWith w) n)
      (.function f types rows) passed) (fun _ => True) s
  fits : ∀ f d, me = some (f, d) → m.Fits d
  fns : ∀ u, m.fns u → u.Halting D w

/-- Binding a `let` or a `var` in copy-in, copy-out pushes it on the frame. -/
theorem Copy.bindInit_fst (w : WriteBack) (s : Copy.State) (x : Name) (init : Expr) (v : Value) :
    ((Copy.memoryWith w).bindInit s x init v).1 = (x, v) :: s.1 := by
  cases init <;> rfl

variable {D : Decls} {w : WriteBack} {lim : Limited} {B : Name → Nat} {H : Name → List Nat}
  {me : Option (Name × Descent)} {m : Meas}

/-- An argument that `p` accepts at a position, among arguments free of `div` within a depth,
is free of `div` within it too. -/
theorem argWith_strengthen {p : Expr → Bool} {R : Roles} {K : Nat} :
    ∀ (j : Nat) (as : List Arg), argWith p j as = true → argsDivFree lim B H me R as = true →
      argsDepth as ≤ K →
        argWith (fun e => p e && e.divFree lim B H me R && decide (e.depth ≤ K)) j as = true
  | 0, .value e :: as, hp, hd, hn => by
    simp only [argWith, argsDivFree, argsDepth, Bool.and_eq_true, Nat.max_le,
      decide_eq_true_eq] at hp hd hn ⊢
    exact ⟨⟨hp, hd.1⟩, hn.1⟩
  | j + 1, .value e :: as, hp, hd, hn => by
    simp only [argWith, argsDivFree, argsDepth, Bool.and_eq_true, Nat.max_le] at hp hd hn ⊢
    exact argWith_strengthen j as hp hd.2 hn.2
  | j + 1, .inout ⟨x, ps⟩ :: as, hp, hd, hn => by
    simp only [argWith, argsDivFree, argsDepth, Bool.and_eq_true, Nat.max_le] at hp hd hn ⊢
    exact argWith_strengthen j as hp hd.2 hn.2
  | 0, .inout _ :: _, hp, _, _ | 0, [], hp, _, _ | _ + 1, [], hp, _, _ => by simp [argWith] at hp

open Halts in
/-- An argument whose sites are counted where it is written gives a function value that
halts: a closure literal free of `div`, a function that asks no argument to halt, or a
non-escaping parameter, whose value halts as the call vouches (facts.div). -/
theorem haltingArg_halts (hC : CallsHalt D w lim B H me m) {k : Nat} (ih : HaltsRun D w lim B H me m k)
    {R : Roles} {e : Expr} (he : haltingArg lim B H me R e = true)
    (hd : e.divFree lim B H me R = true) (hn : e.depth ≤ k) {n : Nat} {s s' : Copy.State}
    {u : Value} (hI : R.Inv s.1 m) (h : eval D (Copy.memoryWith w) n e s = .done u s') :
    u.Halting D w := by
  cases n with
  | zero => cases h
  | succ n =>
  cases e
  case closure ps result ρ body =>
    obtain ⟨c, s₁, -, h₂⟩ := Eval.bind_done h
    have hu : u = .closure c ps result ρ body := by cases h₂; rfl
    subst hu
    simp only [Expr.divFree] at hd
    simp only [Expr.depth] at hn
    intro passed s₀
    exact invoke _ c ps passed fun s₁ =>
      ih body [] hd (by omega) (Roles.Avoids.nil _) s₁ (Roles.Inv.nil _ _)
  case fnRef g types rows =>
    simp only [haltingArg, Bool.and_eq_true, List.isEmpty_iff] at he
    have hu : u = .function g types rows := by cases h; rfl
    subst hu
    intro passed s₀
    exact hC.names g types rows passed s₀ he.2 fun j hj => by rw [he.1] at hj; cases hj
  case var x =>
    have hx : R.of x = .halting := by simpa [haltingArg, Expr.haltingIn] using he
    have := eval_roleIn (n + 1) (.var x) hI (by simp [Expr.roleIn, hx]) h
    simp only [Expr.roleIn, hx] at this
    exact hC.fns u this
  case move x =>
    have hx : R.of x = .halting := by simpa [haltingArg, Expr.haltingIn] using he
    have := eval_roleIn (n + 1) (.move x) hI (by simp [Expr.roleIn, hx]) h
    simp only [Expr.roleIn, hx] at this
    exact hC.fns u this
  case assign t _ => cases t; simp [haltingArg, Expr.haltingIn] at he
  all_goals simp [haltingArg, Expr.haltingIn] at he

/-- A call that passes, at the positions `ks`, arguments whose sites are counted where they
are written, passes function values that halt there. -/
theorem args_haltAt (hC : CallsHalt D w lim B H me m) {k : Nat} (ih : HaltsRun D w lim B H me m k)
    {R : Roles} {ks : List Nat} {as : List Arg} {N : Nat} {s s' : Copy.State}
    {passed : List Passed} (hall : (ks.all fun j => argWith (haltingArg lim B H me R) j as) = true)
    (had : argsDivFree lim B H me R as = true) (han : argsDepth as ≤ k)
    (hA : R.Avoids (argsWrites as)) (hI : R.Inv s.1 m)
    (h : Eval.args (eval D (Copy.memoryWith w) N) as s = .done passed s') :
    Passed.HaltAt D w ks passed := by
  intro j hj
  have hw := argWith_strengthen (K := k) j as (List.all_eq_true.1 hall j hj) had han
  obtain ⟨e, s₁, u, s₂, hok, hI₁, h₁, hk⟩ := args_at N j as hI hA hw h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  refine ⟨_, u, hk, ?_, haltingArg_halts hC ih hok.1.1 hok.1.2 hok.2 hI₁ h₁⟩
  cases e <;> simp [Passed.ofArg]

open Halts in
/-- A call of a named function, free of `div` where `me` says, halts. -/
theorem halts_callFn (hC : CallsHalt D w lim B H me m) {k : Nat} (ih : HaltsRun D w lim B H me m k)
    {f : Name} {types : List Ty} {rows : List Row} {as : List Arg} {R : Roles}
    (hcd : (if Expr.isSelf me (.fnRef f types rows) then descends me R as
      else Expr.divFree lim B H me R (.fnRef f types rows)) = true)
    (had : argsDivFree lim B H me R as = true)
    (hph : (Expr.fnRef f types rows).passesHalting lim B H me R as = true) (han : argsDepth as ≤ k)
    (hA : R.Avoids (argsWrites as)) (s : Copy.State) (hI : R.Inv s.1 m) :
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
  obtain ⟨N, hN⟩ := hdp
  have hp := args_haltAt hC ih (by simpa [Expr.passesHalting] using hph) had han hA hI'
    (hN N (Nat.le_refl _))
  subst hv
  split at hcd
  · rename_i hself
    obtain ⟨⟨f', d⟩, hme, hk⟩ := (Option.any_eq_true _ _).1 (by simpa [descends] using hcd)
    obtain ⟨_, hme', hmf⟩ := (Option.any_eq_true _ _).1 (by simpa [Expr.isSelf] using hself)
    rw [hme] at hme'
    cases hme'
    subst hme
    simp only [beq_iff_eq] at hmf
    subst hmf
    refine hC.self _ d rfl types rows passed s'' ?_ hp
    cases d with
    | parts k' => exact args_descend N hI' hA hk (hN N (Nat.le_refl _))
    | shrinks k' grow b => exact args_shrink N (hC.fits _ _ rfl) hI' hA hk (hN N (Nat.le_refl _))
  · exact hC.names f types rows passed s'' hcd hp

open Halts in
/-- A call through a non-escaping parameter halts: the call that runs the body vouches that
the parameter's function value halts, on any arguments (facts.div). -/
theorem halts_callParam (hC : CallsHalt D w lim B H me m) {k : Nat} (ih : HaltsRun D w lim B H me m k)
    {x : Expr} {as : List Arg} {R : Roles} (hx : x.haltingIn R = true) (hxn : x.depth ≤ k)
    (had : argsDivFree lim B H me R as = true) (han : argsDepth as ≤ k) (hA : R.Avoids (argsWrites as))
    (s : Copy.State) (hI : R.Inv s.1 m) :
    Halts (fun n => eval D (Copy.memoryWith w) n x >>= fun f =>
      Eval.args (eval D (Copy.memoryWith w) n) as >>= fun passed =>
        Eval.callAs D (Copy.memoryWith w) (eval D (Copy.memoryWith w) n) false f passed)
      (fun _ => True) s := by
  have hr : x.roleIn R = .halting := by
    cases x <;> simp_all [Expr.haltingIn, Expr.roleIn]
  have hw : x.writes = [] := by cases x <;> simp_all [Expr.haltingIn, Expr.writes]
  have hx1 : Halts (fun n => eval D (Copy.memoryWith w) n x) (fun _ => True) s :=
    ih x R (by cases x <;> simp_all [Expr.haltingIn, Expr.divFree]) hxn
      (by rw [hw]; exact fun _ _ h => nomatch h) s hI
  refine bind hx1 fun u s' _ hdu => ?_
  obtain ⟨N, hN⟩ := hdu
  have hu : (x.roleIn R).Holds u m :=
    eval_roleIn N x hI (by rw [hr]; exact nofun) (hN N (Nat.le_refl _))
  rw [hr] at hu
  have hI' : R.Inv s'.1 m := hI.afterEval (e := x) (by rw [hw]; exact fun _ _ h => nomatch h) ⟨N, hN⟩
  exact bind (args ih as had han hA s' hI') fun passed s'' _ _ =>
    callAs _ _ _ false _ passed (hC.fns u hu passed s'')

open Halts in
/-- An `if`, free of `div` where `me` says, halts: a counter that its test, or the negation of a
comparison that failed, shows short of its bound is guarded in its branch. -/
theorem halts_if (hC : CallsHalt D w lim B H me m) {k : Nat} (ih : HaltsRun D w lim B H me m k)
    {c a b : Expr} {R : Roles} (hcd : c.divFree lim B H me R = true)
    (had : a.divFree lim B H me (R.held me c) = true)
    (hbd : b.divFree lim B H me (R.held me c.negated) = true) (hcn : c.depth ≤ k) (han : a.depth ≤ k)
    (hbn : b.depth ≤ k) (hA : R.Avoids (c.writes ++ (a.writes ++ b.writes))) (s : Copy.State)
    (hI : R.Inv s.1 m) :
    Halts (fun n => (eval D (Copy.memoryWith w) n c >>= Eval.asBool) >>= fun v =>
      if v then eval D (Copy.memoryWith w) n a else eval D (Copy.memoryWith w) n b)
      (fun _ => True) s := by
  have hA₁ : R.Avoids c.writes := hA.mono (List.subset_append_left _ _)
  have hA₂ : R.Avoids (a.writes ++ b.writes) := hA.mono (List.subset_append_right _ _)
  refine bind (bind (ih c R hcd hcn hA₁ s hI) fun v _ _ _ => const (Eval.Ends.asBool v))
    fun v s' _ hd' => ?_
  obtain ⟨N, hN⟩ := hd'
  obtain ⟨u, s₁, h₁, h₂⟩ := Eval.bind_done (hN N (Nat.le_refl _))
  obtain ⟨rfl, rfl⟩ := Eval.asBool_done h₂
  have hk : Frame.Keeps c.writes c.resizes s.1 s'.1 := by
    have := eval_keeps D w N c _ _ (List.Subset.refl _) (List.Subset.refl _) s
    rw [h₁] at this
    exact this.2
  cases v
  · exact ih b _ hbd hbn (hA₂.mono (List.subset_append_right _ _)).held s'
      (hI.held hC.fits (fun _ hr => ⟨s', .of_eq (eval_negated hr h₁)⟩) hk hA₁)
  · exact ih a _ had han (hA₂.mono (List.subset_append_left _ _)).held s'
      (hI.held hC.fits (fun _ _ => ⟨s', .of_eq h₁⟩) hk hA₁)

open Halts in
/-- Evaluating an expression free of `div` where `me` says, within the depth of its text,
halts from every state whose frame meets its roles. -/
theorem eval_halts (hC : CallsHalt D w lim B H me m) : ∀ k, HaltsRun D w lim B H me m k
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
      obtain ⟨⟨⟨hc, hcd⟩, had⟩, hph⟩ := hd
      obtain ⟨hcn, han, hbn⟩ := hn
      have hA' : R.Avoids (argsWrites as) := hA.mono (List.subset_append_right _ _)
      cases callee
      case fnRef f types rows => exact halts_callFn hC ih hcd had hph han hA' s hI
      case var x => exact halts_callParam hC ih (by simpa [Expr.callable] using hc) hcn had han hA' s hI
      case move x => exact halts_callParam hC ih (by simpa [Expr.callable] using hc) hcn had han hA' s hI
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
      all_goals simp [Expr.callable, Expr.haltingIn] at hc
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
        · exact roleIn_holds hI hdv
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
      exact halts_if hC ih hd.1.1 hd.1.2 hd.2 hn.1 hn.2.1 hn.2.2 hA s hI
    case «match» e τ arms =>
      have hA₁ : R.Avoids e.writes := hA.mono (List.subset_append_left _ _)
      exact bind (ih e R hd.1 hn.1 hA₁ s hI) fun v s' _ hdv =>
        select ih (roleIn_holds hI hdv) hd.2 hn.2 (hA.mono (List.subset_append_right _ _)) s'
          (hI.afterEval hA₁ hdv)
    case «for» x τ e body =>
      exact loop ih x hd.1 hn.1 (hA.mono (List.subset_append_left _ _)) hd.2 hn.2 s hI
    case raise e => exact bind (ih e R hd hn hA s hI) fun v _ _ _ => const (Eval.Ends.throw v)
    case «try» e => exact ih e R hd hn hA s hI
    case form _ e => exact ih e R hd hn hA s hI
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
