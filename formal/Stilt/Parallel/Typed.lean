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
    (hρ : ∀ x ∈ ρ.close η, x.IsLabel → x = .io) (hf : Value.Typed D f ((Ty.fn ps result ρ).close η))
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
      exact nomatch hρ _ hm trivial
    · exact nomatch hρ _ hperf.1 trivial
  | _ => trivial

/-- The labels of a task's row, read at run time, are `io` at most: its error type is no label
(tasks.task-functions). -/
theorem Row.OfTask.labels {ρ : Row} (hρ : ρ.OfTask) (η : REnv) :
    ∀ x ∈ ρ.close η, x.IsLabel → x = .io := by
  intro x hx hl
  obtain ⟨hv, he, hr⟩ := hρ
  rcases Row.mem_close.1 hx with ⟨E, _, rfl⟩ | ⟨v, hv', _⟩ | ⟨E, hE, _⟩ | ⟨p, hp, _⟩ | ⟨_, rfl⟩
  · exact absurd hl (Ty.close_not_label η E)
  · rw [hv] at hv'; exact nomatch hv'
  · rw [he] at hE; exact nomatch hE
  · rw [hr] at hp; exact nomatch hp
  · rfl

/-- tasks.same-output-under-every-handler and tasks.scope-failure: a task's function, of a type
whose row is a task's, called with no arguments from a typed state, run beside the code after
its `spawn` as `task.threads()` runs it, ends as the sequential run does, whatever that code is
(`Eval.aside_eq_bind`): copy-in, copy-out leaves the frames where the call starts as they were
however it ends (tasks.values-in-tasks), and the call never ends as a performance. So a program
writes, reads and ends under `task.threads()` as its sequential run does, a panic in a task
ending it where that run would, and a task of a scope that raises ending the scope there, every
task after it cancelled. The model gives `task.threads()` no interleaving: the order of the
world's output, reads and shared values is the one the paragraph gives, the sequential run's. -/
theorem task_aside (hD : D.Typed) (n : Nat) {Γ : Ctx} {η : REnv} {f : Value} {result : Ty}
    {ρ : Row} {γ : Copy.State} (hρ : ρ.OfTask) (hf : Value.Typed D f ((Ty.fn [] result ρ).close η))
    (hγ : State.Typed D γ Γ η) (rest : Value → Eval Copy.State Value) :
    Eval.aside (Eval.call D Copy.memory (eval D Copy.memory n) f []) rest γ =
      Eval.bind (Eval.call D Copy.memory (eval D Copy.memory n) f []) rest γ :=
  Eval.aside_eq_bind (Eval.call_at (w := .leftToRight) (vs := []) γ)
    (call_settled hD n (hρ.labels η) hf .nil hγ)

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
  call_settled hD n (Row.OfTask.labels ⟨rfl, rfl, rfl⟩ η) hf .nil hγ

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
