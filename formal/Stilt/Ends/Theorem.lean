import Stilt.Ends.While
import Stilt.Panics.Theorem
import Stilt.Soundness.Theorem

/-!
# What `without div` guarantees

**Without div** (facts.without-div): code free of `div` that names only functions
of a ranked set, free of `div` too, halts in copy-in, copy-out, whatever its order of
write-back: a call of a function of the set (`Decls.Ranked.call`), a run whose `main` is
such code (`Program.runCopyWith_halts`) and a program free of `div` whole
(`Program.DivFree.halts`), and in place when it is well typed and obeys the law
of exclusivity. The proof goes by induction on the fuel that the text bounds,
case by case on the expression: a part of an expression needs less than the
expression, a call's body needs no more than its function's bound, which the
call's own covers, a `for` loop runs its body at its own fuel, turn after
turn, and a `while` that counts takes a turn more of fuel for each turn it
makes, of which its values allow finitely many (`Halts.whileCounts`).

**Total** (facts.without-div): a well-typed program whose `main` is free of `panic`
and `div` ends with `()`, with an error of the type its row allows, or with a
panic of the kind `overflow` or `deadlock` (`Program.total_of`, `Program.total`), as
copy-in, copy-out runs it.
-/

namespace Stilt

variable {lim : Limited}

open Halts in
/-- Evaluating an expression free of `div` within the fuel its text bounds halts
from every state. -/
theorem eval_halts {D : Decls} {B : Name → Nat} (w : WriteBack) (hR : D.Ranked lim B) :
    ∀ k, HaltsRun lim B k fun n => eval D (Copy.memoryWith w) n
  | 0, e, _, hn, _ => absurd hn (by have := e.one_le_needs B; omega)
  | k + 1, e, hd, hn, s => by
    have ih := eval_halts w hR k
    apply Halts.succ
    cases e <;> try simp only [Expr.divFree, Expr.needs, Bool.and_eq_true, Nat.max_le,
      Nat.add_le_add_iff_right] at hd hn
    case var x => exact const (Eval.Ends.inspect _ fun _ _ _ => trivial)
    case move x => exact const (Eval.Ends.inspect _ fun _ _ _ => trivial)
    case int k => exact const (Eval.Ends.pure trivial)
    case bool b => exact const (Eval.Ends.pure trivial)
    case unit => exact const (Eval.Ends.pure trivial)
    case record R _ fs => exact bind (fields ih fs hd hn s) fun _ _ _ _ => const (Eval.Ends.declare D R _)
    case variant T _ C es => exact bind (list ih es hd hn s) fun _ _ _ _ => const (Eval.Ends.pure trivial)
    case list τ es => exact bind (list ih es hd hn s) fun _ _ _ _ => const (Eval.Ends.pure trivial)
    case op o es =>
      exact bind (list ih es hd hn s) fun _ _ _ _ => const (Eval.Ends.world _ _)
    case view es =>
      exact bind (list ih es hd hn s) fun _ _ _ _ => const (Eval.Ends.ofExcept _ fun _ _ => trivial)
    case field e f =>
      exact bind (ih e hd hn s) fun _ _ _ _ => const (Eval.Ends.ofExcept _ fun _ _ => trivial)
    case index e i =>
      exact bind (ih e hd.1 hn.1 s) fun _ s' _ _ =>
        bind (bind (ih i hd.2 hn.2 s') fun v _ _ _ => const (Eval.Ends.asInt v)) fun _ _ _ _ =>
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
      exact bind (const (Eval.Ends.inspect _ fun _ _ _ => trivial)) fun _ _ _ _ => const (Eval.Ends.pure trivial)
    case call callee as _ =>
      obtain ⟨⟨hc, hcd⟩, had⟩ := hd
      obtain ⟨hcn, han, hbn⟩ := hn
      cases callee
      case fnRef f types rows =>
        have hf : Halts (fun n => eval D (Copy.memoryWith w) n (.fnRef f types rows))
            (fun v => v = .function f types rows) s :=
          ⟨1, .done (.function f types rows) s, rfl, fun n hle => by
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            rfl⟩
        refine bind hf fun v s' hv _ => bind (args ih as had han s') fun passed s'' _ _ =>
          callAs _ _ _ false _ passed ?_
        subst hv
        show Halts (fun n => Eval.call D (Copy.memoryWith w) (eval D (Copy.memoryWith w) n)
          (.function f types rows) passed) _ s''
        unfold Eval.call
        dsimp only
        cases hfn : D.fn? f with
        | none => exact const (Eval.Ends.fail _)
        | some d =>
          simp only [Expr.divFree] at hcd
          obtain ⟨hdd, hdn⟩ := hR f d hfn hcd
          simp only [Expr.bodyNeeds] at hbn
          refine invoke _ [] d.params passed fun s₀ => ih _ ?_ ?_ s₀
          · rw [Expr.divFree_substRows, Expr.divFree_substTys]; exact hdd
          · rw [Expr.needs_substRows, Expr.needs_substTys]; omega
      case closure ps result ρ body =>
        have hf : Halts (fun n => eval D (Copy.memoryWith w) n (.closure ps result ρ body))
            (fun v => ∃ c, v = .closure c ps result ρ body) s :=
          Halts.succ (bind (const (Eval.Ends.inspect _ fun _ _ _ => trivial)) fun c _ _ _ =>
            const (Eval.Ends.pure ⟨c, rfl⟩))
        refine bind hf fun v s' hv _ => bind (args ih as had han s') fun passed s'' _ _ =>
          callAs _ _ _ false _ passed ?_
        obtain ⟨c, rfl⟩ := hv
        simp only [Expr.divFree] at hcd
        simp only [Expr.bodyNeeds] at hbn
        exact invoke _ c ps passed fun s₀ => ih body hcd hbn s₀
      all_goals simp [Expr.callable] at hc
    case letIn x τ init body =>
      exact bind (ih init hd.1 hn.1 s) fun v _ _ _ => withInit _ x init v (ih body hd.2 hn.2 _)
    case varIn x τ init body =>
      exact bind (ih init hd.1 hn.1 s) fun v _ _ _ => withInit _ x init v (ih body hd.2 hn.2 _)
    case assign p value =>
      obtain ⟨x, ps⟩ := p
      simp only [Expr.divFree, Expr.needs, Bool.and_eq_true, Nat.max_le,
        Nat.add_le_add_iff_right] at hd hn
      exact assign _ ih x hd.1 hn.1 hd.2 hn.2 s
    case seq a b => exact bind (ih a hd.1 hn.1 s) fun _ s' _ _ => ih b hd.2 hn.2 s'
    case «if» c τ a b =>
      exact bind (bind (ih c hd.1.1 hn.1 s) fun v _ _ _ => const (Eval.Ends.asBool v)) fun v s' _ _ =>
        ite v (ih a hd.1.2 hn.2.1 s') (ih b hd.2 hn.2.2 s')
    case «match» e τ arms => exact bind (ih e hd.1 hn.1 s) fun v s' _ _ => select _ ih hd.2 hn.2 v s'
    case «for» x τ e body => exact loop _ ih x hd.1 hn.1 hd.2 hn.2 s
    case raise e => exact bind (ih e hd hn s) fun v _ _ _ => const (Eval.Ends.throw v)
    case «try» e => exact ih e hd hn s
    case tryCatch e E x h τ =>
      exact handle (ih e hd.1 hn.1 s) fun err s' => withVar _ x err (ih h hd.2 hn.2 _)
    case «while» c body =>
      exact shift (Halts.whileCounts ih hd.1.1 hn.1 hd.1.2 hn.2 hd.2 s)
    case «loop» body => simp at hd
    case «break» => exact const (Eval.Ends.jump _)
    case «continue» => exact const (Eval.Ends.jump _)
    case «return» e => exact bind (ih e hd hn s) fun v _ _ _ => const (Eval.Ends.jump _)
    case perform => cases hd
    case withH E c h b =>
      exact bind (ih h hd.1 hn.1 s) fun hv s' _ _ => letGo _ (handleWith _ E c hv (ih b hd.2 hn.2 s'))
    case held ns hs b =>
      exact bind (list ih hs hd.1 hn.1 s) fun vs _ _ _ => held _ (fun s₀ => ih b hd.2 hn.2 s₀) _ vs

/-- **Without div**, for a call of a function that `lim` covers: on any arguments, from any
state, the call halts, never running out of fuel from some fuel on, and ending as no
performance. The function counts as one without `div` wherever it is named; it calls only
the functions `lim` covers, without recursion, and no function value it is given
(facts.without-div). -/
theorem Decls.Ranked.call {D : Decls} {B : Name → Nat} (hR : D.Ranked lim B) (w : WriteBack)
    {f : Name} {types : List Ty} {rows : List Row} (hf : lim.fn f = true) (passed : List Passed)
    (s : Copy.State) :
    Halts (fun n => Eval.call D (Copy.memoryWith w) (eval D (Copy.memoryWith w) n)
      (.function f types rows) passed) (fun _ => True) s := by
  unfold Eval.call
  dsimp only
  cases hfn : D.fn? f with
  | none => exact Halts.const (Eval.Ends.fail _)
  | some d =>
    obtain ⟨hdd, hdn⟩ := hR f d hfn hf
    refine Halts.invoke _ [] d.params passed fun s₀ => eval_halts w hR (B f) _ ?_ ?_ s₀
    · rw [Expr.divFree_substRows, Expr.divFree_substTys]; exact hdd
    · rw [Expr.needs_substRows, Expr.needs_substTys]; exact hdn

/-- **Without div**, for `main`: when the functions that `lim` covers are ranked and
`main`'s body is free of `div`, the run halts in copy-in, copy-out, whatever its order of
write-back, never running out of fuel from some fuel on. -/
theorem Program.runCopyWith_halts {p : Program} {B : Name → Nat} (hR : p.decls.Ranked lim B)
    (hm : p.main.divFree lim = true) (w : WriteBack) (input : String) :
    ∃ N, ∀ fuel, N ≤ fuel → p.runCopyWith w fuel input ≠ .outOfFuel := by
  obtain ⟨N, o, ho, hn⟩ := eval_halts w hR _ p.main hm (Nat.le_refl _) ([], World.start input)
  refine ⟨N, fun fuel hf => ?_⟩
  have h := hn fuel hf
  dsimp only at h
  unfold Program.runCopyWith Program.run
  rw [h]
  cases o <;> simp [Outcome.leaveBody, Outcome.Ends] at ho ⊢
  rename_i j _
  cases j <;> simp

/-- **Without div** for `main`, in place: on a well-typed program that obeys the law of
exclusivity, in-place mutation shows what copy-in, copy-out does. -/
theorem Program.runInPlace_halts {p : Program} {B : Name → Nat} (hR : p.decls.Ranked lim B)
    (hm : p.main.divFree lim = true) (hwt : p.WellTyped) (hex : p.Exclusive) (input : String) :
    ∃ N, ∀ fuel, N ≤ fuel → (p.runInPlace fuel input).observe ≠ .outOfFuel := by
  obtain ⟨N, hN⟩ := p.runCopyWith_halts hR hm .leftToRight input
  refine ⟨N, fun fuel hf h => ?_⟩
  rw [← inPlaceAgreement_observe p fuel input hwt hex] at h
  cases ho : p.runCopy fuel input <;> rw [ho] at h <;> simp only [Outcome.observe, reduceCtorEq] at h
  exact hN fuel hf ho

/-- **Without div**, in copy-in, copy-out with any order of write-back: a program
free of `div` halts, never running out of fuel from some fuel on. -/
theorem Program.DivFree.halts {p : Program} (hp : p.DivFree) (w : WriteBack) (input : String) :
    ∃ N, ∀ fuel, N ≤ fuel → p.runCopyWith w fuel input ≠ .outOfFuel :=
  let ⟨_, hR, hm⟩ := hp
  p.runCopyWith_halts hR hm w input

/-- **Without div**, in place: on a well-typed program that obeys the law of
exclusivity, in-place mutation shows what copy-in, copy-out does. -/
theorem Program.DivFree.haltsInPlace {p : Program} (hp : p.DivFree) (hwt : p.WellTyped)
    (hex : p.Exclusive) (input : String) :
    ∃ N, ∀ fuel, N ≤ fuel → (p.runInPlace fuel input).observe ≠ .outOfFuel :=
  let ⟨_, hR, hm⟩ := hp
  p.runInPlace_halts hR hm hwt hex input

/-- **Total**, for `main`: a well-typed program whose `main` is free of `panic`, naming only
functions that a cover of panic-free functions holds, and free of `div`, naming only
ranked functions, ends with `()`, with an error of the type its row allows, or with a panic
of the kind `overflow` or `deadlock`, as the reference interpreter runs it, with every fuel
from some fuel on (facts.without-div). -/
theorem Program.total_of {p : Program} {lim lim' : Limited} {B : Name → Nat} (hwt : p.WellTyped)
    (hD : p.decls.PanicCover lim) (hpm : p.main.panicFree lim = true) (hR : p.decls.Ranked lim' B)
    (hdm : p.main.divFree lim' = true) (input : String) : ∃ N, ∀ fuel, N ≤ fuel →
      (p.runCopy fuel input).observe = .returned .unit ∨
      (∃ e E, (p.runCopy fuel input).observe = .raised e ∧ p.row.raise = some E ∧
        Value.Typed p.decls e E.sem) ∨
      (p.runCopy fuel input).observe = .panicked .overflow ∨
      (p.runCopy fuel input).observe = .panicked .deadlock := by
  obtain ⟨N, hN⟩ := p.runCopyWith_halts hR hdm .leftToRight input
  refine ⟨N, fun fuel hf => ?_⟩
  have hs := typeSoundness p fuel input hwt
  have he := hN fuel hf
  cases ho : p.runCopy fuel input with
  | done v s =>
    rw [ho] at hs
    simp only [Outcome.Sound] at hs
    exact .inl (by rw [hs]; rfl)
  | raised e s =>
    rw [ho] at hs
    obtain ⟨E, hE, ht⟩ := hs
    exact .inr (.inl ⟨e, E, rfl, hE, ht⟩)
  | jumped j s => rw [ho] at hs; exact absurd hs id
  | panicked k s =>
    rcases p.runCopyWith_panicked hD hpm .leftToRight fuel input ho with ⟨rfl, _⟩ | rfl
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr rfl))
  | performed => rw [ho] at hs; exact absurd hs id
  | outOfFuel => exact absurd ho he
  | stuck => rw [ho] at hs; exact absurd hs id

/-- **Total**: a well-typed program free of `panic` and `div` ends with `()`, with an
error of the type its row allows, or with a panic of the kind `overflow` or `deadlock`,
as the reference interpreter runs it, with every fuel from some fuel on (facts.without-div). -/
theorem Program.total {p : Program} (hwt : p.WellTyped) (hpanic : p.PanicFree) (hdiv : p.DivFree)
    (input : String) : ∃ N, ∀ fuel, N ≤ fuel →
      (p.runCopy fuel input).observe = .returned .unit ∨
      (∃ e E, (p.runCopy fuel input).observe = .raised e ∧ p.row.raise = some E ∧
        Value.Typed p.decls e E.sem) ∨
      (p.runCopy fuel input).observe = .panicked .overflow ∨
      (p.runCopy fuel input).observe = .panicked .deadlock :=
  let ⟨_, hR, hm⟩ := hdiv
  p.total_of hwt hpanic.cover hpanic.2 hR hm input

end Stilt
