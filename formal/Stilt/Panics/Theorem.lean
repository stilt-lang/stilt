import Stilt.Panics.After
import Stilt.Panics.Stores
import Stilt.Panics.Handling
import Stilt.Panics.Holding
import Stilt.InPlace.Agreement

/-!
# What `without panic` guarantees

**Without panic** (effects.without-panic): code that holds no operation that adds the
implicit effect `panic`, divisors that tests guard counted as proved (facts.divisors), and
names only functions whose bodies are such code (`Decls.PanicCover`), never panics but with
the kinds `overflow` and `deadlock`, which `without panic` doesn't rule out
(effects.without-overflow and shared.when-on-value-already-held), and only with `deadlock`
when it holds no operation that can overflow either. A call of a covered function, on
panic-free arguments, ends so (`Decls.PanicCover.call`), and so does a run whose `main` is
such code (`Program.runCopyWith_panicked`), and a program whose every body and `main` are
(`Program.PanicFree`). It holds with every fuel, in copy-in, copy-out whatever its order of
write-back, and, on a well-typed program that obeys the law of exclusivity, in place too
(`inPlaceAgreement`).

The proof goes by induction on the fuel, case by case on the expression, as
`eval_agrees` does in `Stilt.InPlace.Agreement`: every value a run makes is
panic-free, so a call runs a panic-free body, every place it writes takes only
fields, and every fact that tests and range loops give holds until code writes
one of its variables (`eval_keeps`), so no divisor is zero and no index is out
of bounds.
-/

namespace Stilt

variable {lim : Limited}

theorem literalDivisor_spec {es : List Expr} (h : literalDivisor es = true) :
    ∃ a k, es = [a, .int k] ∧ k ≠ 0 := by
  rcases es with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · simp [literalDivisor] at h
  · simp [literalDivisor] at h
  · cases b <;> first
      | (simp [literalDivisor] at h; done)
      | exact ⟨a, _, rfl, by simpa [literalDivisor] using h⟩
  · simp [literalDivisor] at h

theorem Op.byDivisor_spec {o : Op} (h : o.byDivisor = true) :
    (∃ a k, o = .arith a k) ∨ ∃ m k, o = .intMethod m k := by
  cases o <;> first
    | (simp [Op.byDivisor] at h; done)
    | exact .inl ⟨_, _, rfl⟩
    | exact .inr ⟨_, _, rfl⟩

theorem guardedDivisor_spec {G : List Known} {es : List Expr} (h : guardedDivisor G es = true) :
    ∃ a d, es = [a, .var d] ∧ Known.nonzero d ∈ G ∧ d ∉ a.writes := by
  rcases es with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp only [guardedDivisor, reduceCtorEq] at h
  cases hb : b.readVar? with
  | none => simp [hb] at h
  | some d =>
    simp only [hb, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨a, d, by rw [Expr.eq_of_readVar? hb], h.1, h.2⟩

theorem guardedKey_spec {G : List Known} {es : List Expr} (h : guardedKey G es = true) :
    ∃ m k kt, es = [.var m, k] ∧ k.keyTerm? = some kt ∧ Known.has m kt ∈ G := by
  rcases es with _ | ⟨a, _ | ⟨k, _ | _⟩⟩ <;> simp only [guardedKey, reduceCtorEq] at h
  split at h
  · rename_i m kt ha hk
    exact ⟨m, k, kt, by rw [Expr.eq_of_readVar? ha], hk, by simpa using h⟩
  · cases h

theorem guardedIndex_spec {G : List Known} {e i : Expr} (h : guardedIndex G e i = true) :
    ∃ xs j k, e = .var xs ∧ i.offset? = some (j, k) ∧ Known.bounds G j xs k = true := by
  unfold guardedIndex at h
  split at h
  · rename_i xs j k he hi
    exact ⟨xs, j, k, Expr.eq_of_readVar? he, hi, h⟩
  · cases h

theorem guardedStore_spec {G : List Known} {x : Name} {ps : List Projection} {value : Expr}
    (h : guardedStore G ⟨x, ps⟩ value = true) :
    ∃ e j k, ps = [.index e] ∧ e.offset? = some (j, k) ∧ Known.bounds G j x k = true ∧
      x ∉ value.resizes := by
  unfold guardedStore at h
  split at h
  · rename_i e hp
    split at h
    · rename_i j k he
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨e, j, k, hp, he, h.1, h.2⟩
    · cases h
  · cases h

open Eval.PanicFree in
/-- Evaluating a panic-free expression, with any fuel, ends as panic-free code may. -/
theorem eval_panicFree {D : Decls} (hD : D.PanicCover lim) (w : WriteBack) :
    ∀ n, PanicFreeRun lim (eval D (Copy.memoryWith w) n)
  | 0, _, _, _ => outOfFuel
  | n + 1, G, e, he => by
    have ih := eval_panicFree hD w n
    have hk := eval_keeps D w n
    have keep : ∀ e : Expr, Eval.Keeps e.writes e.resizes (fun _ => True) (eval D (Copy.memoryWith w) n e) :=
      fun e => hk e _ _ (List.Subset.refl _) (List.Subset.refl _)
    cases e <;> try simp only [Expr.panicFreeIn, Bool.and_eq_true] at he
    case var x => exact read w x
    case move x => exact read w x
    case int k => exact pure .int
    case bool b => exact pure .bool
    case unit => exact pure .unit
    case record R fs =>
      exact bind (fields ih hk fs he) (Eval.Keeps.fields hk fs (List.Subset.refl _) (List.Subset.refl _))
        fun _ hw => declare D R hw
    case variant T C es =>
      exact bind (list ih hk es he) (Eval.Keeps.list hk es (List.Subset.refl _) (List.Subset.refl _))
        fun _ hvs => pure (.variant hvs)
    case list τ es =>
      exact bind (list ih hk es he) (Eval.Keeps.list hk es (List.Subset.refl _) (List.Subset.refl _))
        fun _ hvs => pure (.list hvs)
    case op o es =>
      have kl := Eval.Keeps.list hk es (List.Subset.refl _) (List.Subset.refl _)
      simp only [Op.panicFreeOn, Bool.or_eq_true, Bool.and_eq_true] at he
      rcases he with ⟨⟨(ho | ⟨hb, hl | hg⟩) | ⟨hi, hgk⟩, hov⟩, hes⟩
      · exact bind (list ih hk es hes) kl fun vs hvs =>
          run w (Op.apply_calmIn ho (by simpa using hov) vs) hvs fun _ _ _ h =>
            Op.run_hereditary Value.PanicFree.hereditary .unit hvs h
      · have hlo : lim.overflows = true :=
          hov.resolve_right (by simp [Op.overflowFree_of_byDivisor hb])
        obtain ⟨a, k, rfl, hk0⟩ := literalDivisor_spec hl
        simp only [exprsPanicFree, Bool.and_eq_true] at hes
        exact bind (pair (ih G a hes.1) (keep a) (intLit w n k) (keep _)) kl
          fun vs ⟨u, v, hvs, hu, hv⟩ => by
            subst hvs hv
            have hvs : ∀ x ∈ [u, Value.int k], x.PanicFree lim := by simp [hu, Value.PanicFree.int]
            exact run w ((Op.apply_calm_divisor (Op.byDivisor_spec hb) u hk0).allowing hlo) hvs
              fun _ _ _ h =>
              Op.run_hereditary Value.PanicFree.hereditary .unit hvs h
      · have hlo : lim.overflows = true :=
          hov.resolve_right (by simp [Op.overflowFree_of_byDivisor hb])
        obtain ⟨a, d, rfl, hd, hda⟩ := guardedDivisor_spec hg
        simp only [exprsPanicFree, Bool.and_eq_true] at hes
        exact bind (pair (ih G a hes.1) (keep a) (readNonzero w n (mem_withoutNames.2 ⟨hd, fun y hy => by
              simp only [Known.reads, List.mem_singleton] at hy; exact hy ▸ hda⟩))
            (keep _)) kl fun vs ⟨u, v, hvs, hu, ⟨k, hv, hk0⟩⟩ => by
            subst hvs hv
            have hvs : ∀ x ∈ [u, Value.int k], x.PanicFree lim := by simp [hu, Value.PanicFree.int]
            exact run w ((Op.apply_calm_divisor (Op.byDivisor_spec hb) u hk0).allowing hlo) hvs
              fun _ _ _ h =>
              Op.run_hereditary Value.PanicFree.hereditary .unit hvs h
      · obtain ⟨m, k, kt, rfl, hkt, hm⟩ := guardedKey_spec hgk
        simp only [beq_iff_eq] at hi
        subst hi
        exact bind (withDone (list ih hk _ hes) fun _ _ _ hz h => index_calm hkt (hz _ hm) h) kl
          fun vs ⟨hvs, hc⟩ => run w hc hvs fun _ _ _ h =>
            Op.run_hereditary Value.PanicFree.hereditary .unit hvs h
    case view es =>
      simp only [beq_iff_eq] at he
      exact bind (listSized ih hk es he.2)
        (Eval.Keeps.list hk es (List.Subset.refl _) (List.Subset.refl _)) fun vs hvs => by
          obtain ⟨hvs, hl⟩ := hvs
          rw [he.1] at hl
          match vs, hl with
          | [v], _ => exact ofExcept ⟨Calm.ok v, fun _ h => Op.apply_hereditary
              Value.PanicFree.hereditary hvs h⟩
    case field e f =>
      exact bind (ih G e he) (keep e) fun _ hv =>
        ofExcept (Value.PanicFree.get hv fun s hs => ⟨f, List.mem_singleton.1 hs⟩)
    case index e i =>
      obtain ⟨xs, j, k, rfl, hi, hb⟩ := guardedIndex_spec he.1
      exact index (n + 1) hi hb he.2
    case fnRef f types rows => exact pure (.function he)
    case method t m τ =>
      show Eval.PanicFree lim G (Value.PanicFree lim) (Eval.method D t m τ)
      unfold Eval.method
      split
      · rename_i h _
        split
        · rename_i i hi
          exact pure (.function (hD.methods t m h i he hi))
        · exact stuck
      · exact stuck
    case closure ps result ρ body =>
      exact bind (capture w _) (Eval.Keeps.inspect (W := []) (L := []) _ fun _ _ _ => trivial)
        fun _ hc => pure (.closure he hc)
    case call callee as _ =>
      exact bind (ih G callee he.1) (keep callee) fun _ hf =>
        bind (args ih hk as he.2) (Eval.Keeps.args hk as (List.Subset.refl _) (List.Subset.refl _)) fun _ hp => callAs w hD ih false hf hp
    case letIn x τ init body =>
      exact bind (ih G init he.1) (keep init) fun _ hv => withInit w hv (ih _ body he.2)
    case varIn x τ init body =>
      exact bind (ih G init he.1) (keep init) fun _ hv => withInit w hv (ih _ body he.2)
    case assign p value =>
      obtain ⟨x, ps⟩ := p
      have hor := he.1
      rw [Bool.or_eq_true] at hor
      rcases hor with hf | hg
      · simp only [Place.indexFree] at hf
        exact assign w ih hk x hf he.2
      · rw [Bool.and_eq_true] at hg
        obtain ⟨e, j, k, rfl, hi, hb, hres⟩ := guardedStore_spec hg.1
        have hov : (lim.overflows || e.isVar) = true := by simpa [Projection.byVar] using hg.2
        exact storeIndex n hi hb hres hov (ih G value he.2) (keep value)
    case seq a b =>
      exact bindAfterLen (ih G a he.1) (keep a) (fun s _ _ h => after_holds w n a s h) fun _ _ => ih _ b he.2
    case «if» c τ a b => exact cond w n ih he.1.1 (ih _ a he.1.2) (ih _ b he.2)
    case «match» e τ arms => exact bind (ih G e he.1) (keep e) fun _ hv => select w ih he.2 hv
    case «for» x τ e body =>
      exact loop w ih hk x (e.rangeFacts G x body) e.rangeAfter he.1 he.2
        (fun _ _ _ h vs hv => range_after n e h vs hv)
        (fun _ _ _ hz h vs hv u hu s'' hm => range_elem n x body e hz h vs hv u hu s'' hm)
    case raise e => exact bind (ih G e he) (keep e) fun _ hv => throw hv
    case «try» e => exact ih G e he
    case tryCatch e E x h τ => exact handle (ih G e he.1) (keep e) fun _ he' => withVar w he' (ih _ h he.2)
    case «while» c body =>
      have hl := ih [] (.while c body) (by simp [Expr.panicFreeIn, he.1, he.2])
      refine weaken (G' := []) ?_ (fun _ h => nomatch h)
      exact cond w n ih he.1
        (bind (turn (weaken (ih _ body he.2) (List.subset_append_right _ _)))
          (Eval.Keeps.turn (keep body)) fun g _ => ite g (weaken hl (fun _ h => nomatch h)) (pure .unit))
        (pure .unit)
    case «loop» body =>
      have hl := ih [] (.loop body) (by simpa [Expr.panicFreeIn] using he)
      exact weaken (G' := []) (bind (turn (ih [] body he)) (Eval.Keeps.turn (keep body)) fun g _ =>
        ite g (weaken hl (fun _ h => nomatch h)) (pure .unit)) (fun _ h => nomatch h)
    case «break» => exact jump trivial
    case «continue» => exact jump trivial
    case «return» e => exact bind (ih G e he) (keep e) fun _ hv => jump hv
    case perform op e => exact bind (ih G e he) (keep e) fun _ hv s hs _ => ⟨hv, hs, fun _ _ hw hx => ⟨hw, hs.1, hx⟩⟩
    case withH E c h b =>
      exact bind (ih G h he.1) (keep h) fun _ hh s hs hz => Outcome.PanicFree.letGo w _ <|
        Outcome.PanicFree.handleWith w hh (fun _ _ s' hc hv hs' =>
          callAs w hD ih c hc (fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact hv) s' hs'
            (Frame.Meets.nil _)) (ih _ b he.2 s hs hz)
    case held ns hs b =>
      exact bind (list ih hk hs he.1) (Eval.Keeps.list hk hs (List.Subset.refl _) (List.Subset.refl _))
        fun vs _ => held w (ns.map Prod.fst) vs (ih _ b he.2)

/-- **Without panic**, for a call of a function that `lim` covers: on panic-free arguments,
from a panic-free state, the call ends as panic-free code may. It panics only with
`overflow` or `deadlock`, and so does the rest of every performance it makes, resumed with
panic-free values. The function counts as one that can't panic wherever it is named, and
the function values it is given may have been made anywhere, panic-free as they are
(effects.without-panic and facts.calls-through-function-values). -/
theorem Decls.PanicCover.call {D : Decls} (hD : D.PanicCover lim) (w : WriteBack) (n : Nat)
    {f : Name} {types : List Ty} {rows : List Row} (hf : lim.fn f = true) {passed : List Passed}
    (hp : ∀ q ∈ passed, q.PanicFree lim) :
    Eval.PanicFree lim [] (Value.PanicFree lim)
      (Eval.call D (Copy.memoryWith w) (eval D (Copy.memoryWith w) n) (.function f types rows) passed) :=
  Eval.PanicFree.call w hD (eval_panicFree hD w n) (.function hf) hp

/-- **Without panic**, for `main`: when the functions that `lim` covers are panic-free and
`main`'s body is too, the run panics only with `deadlock`, or with `overflow` where `lim`
allows it, in copy-in, copy-out whatever its order of write-back (effects.without-panic
and effects.without-overflow). -/
theorem Program.runCopyWith_panicked {p : Program} (hD : p.decls.PanicCover lim)
    (hm : p.main.panicFree lim = true) (w : WriteBack) (fuel : Nat) (input : String)
    {k : PanicKind} {s : Copy.State} (h : p.runCopyWith w fuel input = .panicked k s) :
    (k = .overflow ∧ lim.overflows = true) ∨ k = .deadlock := by
  have hr := eval_panicFree hD w fuel [] p.main hm ([], World.start input)
    ⟨(fun _ h => nomatch h), World.All.start input⟩ (Frame.Meets.nil _)
  unfold Program.runCopyWith Program.run at h
  cases ho : eval p.decls (Copy.memoryWith w) fuel p.main ([], World.start input) <;> rw [ho] at h hr <;>
    simp only [Outcome.leaveBody] at h
  case panicked k' s' =>
    cases h
    exact hr.1
  case jumped j s' => cases j <;> cases h
  all_goals cases h

/-- **Without panic** for `main`, in place: on a well-typed program that obeys the law of
exclusivity, in-place mutation shows what copy-in, copy-out does. -/
theorem Program.runInPlace_panicked {p : Program} (hD : p.decls.PanicCover lim)
    (hm : p.main.panicFree lim = true) (hwt : p.WellTyped) (hex : p.Exclusive) (fuel : Nat)
    (input : String) {k : PanicKind} (h : (p.runInPlace fuel input).observe = .panicked k) :
    (k = .overflow ∧ lim.overflows = true) ∨ k = .deadlock := by
  rw [← inPlaceAgreement_observe p fuel input hwt hex] at h
  cases ho : p.runCopy fuel input <;> rw [ho] at h <;> simp only [Outcome.observe] at h
  case panicked k' s =>
    cases h
    exact p.runCopyWith_panicked hD hm .leftToRight fuel input ho
  all_goals cases h

/-- **Without panic**, in copy-in, copy-out with any order of write-back: a
panic-free program panics only with `overflow` or `deadlock` (effects.without-panic). -/
theorem Program.PanicFree.runCopyWith {p : Program} (hp : p.PanicFree) (w : WriteBack) (fuel : Nat)
    (input : String) {k : PanicKind} {s : Copy.State} (h : p.runCopyWith w fuel input = .panicked k s) :
    k = .overflow ∨ k = .deadlock :=
  (p.runCopyWith_panicked hp.cover hp.2 w fuel input h).imp_left And.left

/-- **Without panic**, as the reference interpreter runs programs. -/
theorem Program.PanicFree.runCopy {p : Program} (hp : p.PanicFree) (fuel : Nat) (input : String)
    {k : PanicKind} {s : Copy.State} (h : p.runCopy fuel input = .panicked k s) :
    k = .overflow ∨ k = .deadlock :=
  hp.runCopyWith .leftToRight fuel input h

/-- **Without panic**, in place: on a well-typed program that obeys the law of
exclusivity, in-place mutation shows what copy-in, copy-out does. -/
theorem Program.PanicFree.runInPlace {p : Program} (hp : p.PanicFree) (hwt : p.WellTyped)
    (hex : p.Exclusive) (fuel : Nat) (input : String) {k : PanicKind}
    (h : (p.runInPlace fuel input).observe = .panicked k) : k = .overflow ∨ k = .deadlock :=
  (p.runInPlace_panicked hp.cover hp.2 hwt hex fuel input h).imp_left And.left

end Stilt
