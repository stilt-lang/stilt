import Stilt.Alloc.Runs
import Stilt.Alloc.Limits
import Stilt.Limits

/-!
# What `without alloc` guarantees

**Without alloc** (facts.without-alloc): code that holds no operation making a value that
needs storage of its own, and names only functions whose bodies are such code
(`Decls.MakesCover`), counts no allocation when it runs. The counting evaluator
(`Count.eval`) runs it as the reference interpreter does, step for step, and ends with the
count it started with, from any state whose values allocate nothing when called, however the
run ends; and it never performs an operation, since only an allocating `with` could handle one
(`eval_counts`). A call of a covered function on arguments that allocate nothing when called,
wherever they were made (facts.calls-through-function-values), counts none
(`Decls.MakesCover.call`), and neither does a run whose `main` is such code
(`Program.runCounting_eq`).

The proof goes by induction on the fuel, case by case on the expression, as `eval_panicFree`
does in `Stilt.Panics.Theorem`: every value the run makes allocates nothing when called, so a
call runs a body of covered code.
-/

namespace Stilt

variable {D : Decls} {lim : Limited}

namespace Eval.Counts

variable {α : Type} {P : α → Prop}

/-- No allocation where the count isn't told of one. -/
theorem tickIf_bind {b : Bool} (hb : b = false) {m' : Eval Count.State α} {m : Eval Copy.State α}
    (h : Eval.Counts D lim P m' m) : Eval.Counts D lim P (Count.tickIf b >>= fun _ => m') m := by
  subst hb
  exact h

end Eval.Counts

open Eval.Counts in
/-- Code that makes no value needing storage counts no allocation, at every fuel. -/
theorem eval_counts (hD : D.MakesCover lim) : ∀ n, CountsRun D lim (Count.eval D n) (eval D Copy.memory n)
  | 0, _, _ => outOfFuel
  | n + 1, e, he => by
    have ih := eval_counts hD n
    cases e <;> try simp only [Expr.allocFreeIn, Bool.and_eq_true, Bool.not_eq_true',
      Bool.false_eq_true] at he
    case var x => exact read x
    case move x => exact read x
    case int k => exact pure .int
    case bool b => exact pure .bool
    case unit => exact pure .unit
    case record R _ fs => exact bind (fields ih fs he.2) fun _ hw => tickIf_bind he.1 (declare R hw)
    case variant T _ C es =>
      exact bind (list ih es he.2) fun _ hvs => tickIf_bind he.1 (pure (.variant hvs))
    case op o es => exact bind (list ih es he.2) fun _ hvs => tickIf_bind he.1 (run hvs)
    case view es =>
      exact bind (list ih es he) fun _ hvs =>
        ofExcept fun _ h => Op.apply_hereditary Value.AllocFree.hereditary hvs h
    case field e f =>
      exact bind (ih e he) fun _ hv => ofExcept fun _ h => Value.AllocFree.hereditary.part hv h
    case index e i =>
      exact bind (ih e he.1) fun _ hv => bind (bind (ih i he.2) fun k _ => asInt k) fun _ _ =>
        ofExcept fun _ h => Value.AllocFree.hereditary.part hv h
    case fnRef f types rows => exact pure (.function he)
    case method t m τ => exact method hD τ he
    case call callee as _ =>
      exact bind (ih callee he.1) fun _ hf => bind (args ih as he.2) fun _ hp =>
        callAs hD ih false hf hp
    case letIn x τ init body => exact bind (ih init he.1) fun _ hv => withInit hv (ih body he.2)
    case varIn x τ init body => exact bind (ih init he.1) fun _ hv => withInit hv (ih body he.2)
    case assign p value =>
      obtain ⟨x, ps⟩ := p
      simp only [Expr.allocFreeIn, Bool.and_eq_true] at he
      exact assign ih x he.1 he.2
    case seq a b => exact bind (ih a he.1) fun _ _ => ih b he.2
    case «if» c τ a b =>
      exact bind (bind (ih c he.1.1) fun v _ => asBool v) fun g _ =>
        ite g (ih a he.1.2) (ih b he.2)
    case «match» e τ arms => exact bind (ih e he.1) fun _ hv => select ih he.2 hv
    case «for» x τ e body => exact loop ih x he.1 he.2
    case raise e => exact bind (ih e he) fun _ hv => throw hv
    case «try» e => exact ih e he
    case form _ e => exact ih e he
    case tryCatch e E x h τ => exact handle (ih e he.1) fun _ herr => withVar herr (ih h he.2)
    case «while» c body =>
      have hl : (Expr.while c body).allocFreeIn D lim = true := by
        simp [Expr.allocFreeIn, he.1, he.2]
      exact bind (bind (ih c he.1) fun v _ => asBool v) fun g _ =>
        ite g (bind (turn (ih body he.2)) fun g' _ => ite g' (ih _ hl) (pure .unit)) (pure .unit)
    case «loop» body =>
      have hl : (Expr.loop body).allocFreeIn D lim = true := by simpa [Expr.allocFreeIn] using he
      exact bind (turn (ih body he)) fun g _ => ite g (ih _ hl) (pure .unit)
    case «break» => exact jump trivial
    case «continue» => exact jump trivial
    case «return» e => exact bind (ih e he) fun _ hv => jump hv
    case held ns hs b => exact bind (list ih hs he.1) fun vs _ => held (ih b he.2) _ vs

/-- **Without alloc**, for a call of a function that `lim` covers: on arguments that allocate
nothing when called, from a state whose values don't either, with any count, the counting
evaluator runs the call as the reference interpreter does and ends with the count it started
with. The function counts as one without `alloc` wherever it is named, and the function values
it is given may have been made anywhere (facts.without-alloc and
facts.calls-through-function-values). -/
theorem Decls.MakesCover.call (hD : D.MakesCover lim) (n : Nat) {f : Name} {types : List Ty}
    {rows : List Row} (hf : lim.fn f = true) {passed : List Passed}
    (hp : ∀ q ∈ passed, q.AllocFree D lim) :
    Eval.Counts D lim (Value.AllocFree D lim)
      (Eval.call D Count.memory (Count.eval D n) (.function f types rows) passed)
      (Eval.call D Copy.memory (eval D Copy.memory n) (.function f types rows) passed) :=
  Eval.Counts.call hD (eval_counts hD n) (.function hf) hp

/-- Runs `main` with the count of allocations, from none, on an input. -/
def Program.runCounting (p : Program) (fuel : Nat) (input : String := "") : Outcome Count.State Value :=
  (Count.eval p.decls fuel p.main (Count.lift 0 ([], World.start input))).leaveBody

theorem Outcome.leaveBody_atCount (c : Nat) :
    ∀ o : Outcome Copy.State Value, (o.atCount c).leaveBody = o.leaveBody.atCount c
  | .jumped (.ret _) _ | .jumped .brk _ | .jumped .cont _ | .done .. | .raised .. | .panicked ..
  | .performed .. | .outOfFuel | .stuck => rfl

/-- **Without alloc**, for `main`: when the functions that `lim` covers make no value needing
storage and `main`'s body doesn't either, the counting run is the reference interpreter's,
with no allocation counted. -/
theorem Program.runCounting_eq {p : Program} (hD : p.decls.MakesCover lim)
    (hmain : p.main.allocFreeIn p.decls lim = true) (fuel : Nat) (input : String) :
    p.runCounting fuel input = (p.runCopy fuel input).atCount 0 := by
  have hs : State.AllocFree p.decls lim ([], World.start input) :=
    ⟨fun _ h => (nomatch h), World.All.start input⟩
  unfold Program.runCounting Program.runCopy Program.run
  rw [((eval_counts hD fuel) p.main hmain 0 _ hs).1, Outcome.leaveBody_atCount]

/-- What `without alloc` promises (facts.without-alloc): the functions limited by it are among a
set of functions a call of any of which, on arguments that allocate nothing when called, from a
state whose values don't either, with any count of allocations, runs in the counting evaluator
as the reference interpreter runs it, with the count unchanged in every state it ends in: it
allocates nothing. A run whose `main` is limited counts no allocation. The count leaves out the
copies of shared lists that writes through an index and in-place parameters stand for, which no
step of the calculus makes: that a limited function copies nothing is not stated. -/
def Program.AllocsKept (p : Program) (fuel : Nat) (input : String) : Prop :=
  (∃ lim : Limited, (∀ name d, p.decls.fn? name = some d → d.limits.alloc = true →
      lim.fn name = true) ∧
    ∀ (n : Nat) (name : Name) (types : List Ty) (rows : List Row) (passed : List Passed) (c : Nat)
      (s : Copy.State), lim.fn name = true → (∀ q ∈ passed, q.AllocFree p.decls lim) →
      State.AllocFree p.decls lim s →
      Eval.call p.decls Count.memory (Count.eval p.decls n) (.function name types rows) passed
          (Count.lift c s) =
        (Eval.call p.decls Copy.memory (eval p.decls Copy.memory n) (.function name types rows)
          passed s).atCount c) ∧
  (p.limits.alloc = true → p.runCounting fuel input = (p.runCopy fuel input).atCount 0)

/-- The values that make no value needing storage under a cover of `without alloc`. -/
theorem Decls.AllocCover.makes {IP : Name → Nat → Bool} (h : D.AllocCover lim IP) :
    D.MakesCover lim :=
  ⟨fun d hd hl => (h.fns d hd hl).1, h.methods⟩

/-- The checks of `without alloc` keep its promise. -/
theorem Program.AllocLimited.kept {p : Program} (h : p.AllocLimited) (fuel : Nat) (input : String) :
    p.AllocsKept fuel input := by
  obtain ⟨lim, IP, _, hD, hfns, hmain⟩ := h
  refine ⟨⟨lim, fun name d hd hl => ?_, fun n name _ _ _ c s hf hp hs =>
    (hD.makes.call n hf hp c s hs).1⟩, fun hl => Program.runCounting_eq hD.makes (hmain hl).1 fuel input⟩
  obtain ⟨hmem, rfl⟩ := Decls.fn?_spec hd
  exact hfns d hmem hl

end Stilt
