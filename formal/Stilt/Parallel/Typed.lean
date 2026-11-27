import Stilt.Parallel
import Stilt.Soundness.Theorem

/-!
# Parallel calls of well-typed closures

A closure of `std.par` has an empty row (par.what-runs-in-parallel), and the
fundamental lemma gives a call of a function value of such a type, on
arguments of its parameter types, no raise and no performance to end with. So
the calls of `par.map` and `par.both`, and of each level of `par.fold`'s tree,
end alike run at the same time, each from the frame they start from, as run
one after another (par.sequential-meaning and par.panics): no program can tell
how many threads ran them. The same lemma keeps every continuation in its task
(tasks.continuations-stay-in-task): a task's function performs no user-defined effect, so a
call of it never ends as a performance.
-/

namespace Stilt

variable {D : Decls}

/-- An empty row reads as no label at run time. -/
theorem Row.pure_close (η : REnv) : Row.pure.close η = [] := rfl

/-- A call of a function value whose type's row reads as no label but `io` at run time, on arguments
of its parameter types, from a frame of the code around it, never ends as a performance. -/
theorem call_settled (hD : D.Typed) (n : Nat) {Γ : Ctx} {η : REnv} {f : Value}
    {passed : List Passed} {ps : List (Mode × Ty)} {result : Ty} {ρ : Row} {γ : Copy.State}
    (hρ : ∀ x ∈ ρ.close η, x = .io) (hf : Value.Typed D f ((Ty.fn ps result ρ).close η))
    (hp : Passed.Typed D Γ η passed ps) (hγ : State.Typed D γ Γ η) :
    (Eval.call D Copy.memory (eval D Copy.memory n) f passed γ).Settled := by
  have h := call_ok (hD.sound n) hD hf hp γ hγ
  generalize Eval.call D Copy.memory (eval D Copy.memory n) f passed γ = o at h ⊢
  cases o with
  | performed op v s k =>
    obtain ⟨⟨τ, ρ', hperf, -⟩, -⟩ := h
    simp only [performsOf] at hperf
    split at hperf
    · obtain ⟨_, _, hm, -⟩ := hperf
      exact nomatch hρ _ hm
    · exact nomatch hρ _ hperf.1
  | _ => trivial

/-- tasks.continuations-stay-in-task: a task's function raises nothing and performs no
user-defined effect (tasks.task-functions), and `async` performs nothing but its tasks' calls,
as the export writes it, so the row of its type holds `io` at most. A call of it never ends as
a performance: no continuation leaves the task, and every performance in it is handled, and
resumed, inside it. -/
theorem continuations_stay (hD : D.Typed) (n : Nat) {Γ : Ctx} {η : REnv} {f : Value}
    {result : Ty} {io : Bool} {γ : Copy.State}
    (hf : Value.Typed D f ((Ty.fn [] result ⟨io, none, [], [], none⟩).close η))
    (hγ : State.Typed D γ Γ η) :
    (Eval.call D Copy.memory (eval D Copy.memory n) f [] γ).Settled :=
  call_settled hD n (fun x hx => by cases io <;> simp_all [Row.close, Row.labelsOf, Row.ioLabel]) hf
    .nil hγ

/-- par.sequential-meaning and par.panics: calls of function values whose
types have empty rows, on arguments of their parameter types, run at the same
time, each from the frame they start from, end as they do run one after
another, from the first to the last: with their values in order, or as the
first that doesn't give one, in any typed world the calls share. -/
theorem parallel_eq_sequential (hD : D.Typed) (n : Nat) {Γ : Ctx} {η : REnv} {γ : Copy.Frame}
    (hγ : Frame.Typed D γ Γ η) {x : World} (hx : World.Typed D x) (calls : List (Value × List Value))
    (hc : ∀ c ∈ calls, ∃ ps result, Value.Typed D c.1 ((Ty.fn ps result Row.pure).close η) ∧
      Passed.Typed D Γ η (c.2.map .value) ps) :
    Eval.inParallel (calls.map fun c => Eval.call D Copy.memory (eval D Copy.memory n) c.1
        (c.2.map .value)) (γ, x) =
      Eval.sequentially (calls.map fun c => Eval.call D Copy.memory (eval D Copy.memory n) c.1
        (c.2.map .value)) (γ, x) := by
  refine Eval.inParallel_eq_sequentially γ (World.Typed D) _ ?_ x hx
  intro c hc' x' hx'
  obtain ⟨c, hmem, rfl⟩ := List.mem_map.1 hc'
  obtain ⟨ps, result, hf, hp⟩ := hc c hmem
  refine ⟨Eval.call_at (w := .leftToRight) (γ, x'), call_settled hD n (fun _ h => by simp [Row.pure_close] at h) hf hp (γ := (γ, x')) ⟨hγ, hx'⟩,
    fun v s' h => ?_⟩
  have hok := call_ok (hD.sound n) hD hf hp (γ, x') ⟨hγ, hx'⟩
  rw [h] at hok
  exact hok.2.2

end Stilt
