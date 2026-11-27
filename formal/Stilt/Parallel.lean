import Stilt.Semantics

/-!
# Parallel calls

par.sequential-meaning gives each function of `std.par` the meaning of its
sequential run: `map` calls its function on the elements from the first to the
last, and `both` calls `f`, then `g`. A parallel run calls them at the same
time, each on a thread that copies what the call captures, and par.panics makes
it report the first failure in the sequential order. This module states both
runs of a list of calls and proves them equal in copy-in, copy-out, whatever
its order of write-back, when the calls pass only values, as the closures of
`std.par` are called (par.what-runs-in-parallel): such a call leaves its
caller's frame as it was, however it ends, so no call sees what another did.
The threads share one world, the output each writes to, and each call runs in
it as the one before it left it.
`Stilt.Parallel.Typed` adds that a call of a function value whose type has an
empty row, on arguments of its parameter types, never ends as a raise or a
performance, so the two runs agree for every such call.

A task runs beside the code that started it in the same way (`Eval.aside`): from the frames
where it starts, the code after its `spawn` going on from its own, and the two agree with the
sequential run under the same conditions (`Eval.aside_eq_bind`). The order of the world's effects
in that run is the sequential run's, as tasks.same-output-under-every-handler gives it; the calculus
reaches no files, network, clock, environment or randomness, whose order among tasks
tasks.unordered-io leaves out of a program's meaning.
-/

namespace Stilt

variable {σ α : Type}

/-- An outcome that leaves the frames of the state `s`, when it leaves a state,
a performance's included, in any world. -/
def Outcome.At (s : σ × World) : Outcome (σ × World) α → Prop
  | .done _ s' | .raised _ s' | .jumped _ s' | .panicked _ s' => s'.1 = s.1
  | .performed _ _ s' _ => s'.1 = s.1
  | .outOfFuel | .stuck => True

/-- An outcome that isn't a performance. -/
def Outcome.Settled : Outcome σ α → Prop
  | .performed .. => False
  | _ => True

namespace Eval

/-- The sequential run of a list of calls (par.sequential-meaning): each from
the state the one before it left, their values in order, or the outcome of the
first that doesn't give one. -/
def sequentially : List (Eval σ Value) → Eval σ (List Value)
  | [] => pure []
  | c :: cs => do
    let v ← c
    let vs ← sequentially cs
    pure (v :: vs)

/-- The parallel run of a list of calls: each from the same frames, as threads
that copy what they capture run them, in the world the threads share, their
values in order with the state that the calls left, or the outcome of the first
in order that doesn't give one (par.panics). -/
def inParallel : List (Eval (σ × World) Value) → Eval (σ × World) (List Value)
  | [] => fun s => .done [] s
  | c :: cs => fun s =>
    match c s with
    | .done v s₁ => (inParallel cs (s.1, s₁.2)).bind fun vs s' => .done (v :: vs) s'
    | o => o.bind fun _ _ => .stuck

/-- Calls that each leave the frames as they were, in any world that `W` holds of, none of
which ends as a performance, and each of which gives its value in such a world, give the same
outcome run in parallel as in sequence. -/
theorem inParallel_eq_sequentially (fr : σ) (W : World → Prop) :
    ∀ (cs : List (Eval (σ × World) Value)),
      (∀ c ∈ cs, ∀ x, W x → (c (fr, x)).At (fr, x) ∧ (c (fr, x)).Settled ∧
        ∀ v s', c (fr, x) = .done v s' → W s'.2) →
      ∀ x, W x → inParallel cs (fr, x) = sequentially cs (fr, x)
  | [], _, _, _ => rfl
  | c :: cs, h, x, hx => by
    have ih := inParallel_eq_sequentially fr W cs fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    obtain ⟨hat, hset, hW⟩ := h c List.mem_cons_self x hx
    show _ = Eval.bind c (fun v => Eval.bind (sequentially cs) fun vs => Eval.pure (v :: vs)) _
    unfold inParallel Eval.bind
    cases hc : c (fr, x) with
    | done v s' =>
      rw [hc] at hat
      have hx' := hW v s' hc
      obtain ⟨fr', x'⟩ := s'
      cases (show fr' = fr from hat)
      simp only [Outcome.bind]
      rw [ih x' hx']
      rfl
    | raised e s' => rfl
    | jumped j s' => rfl
    | panicked k s' => rfl
    | performed op v s' k => rw [hc] at hset; exact hset.elim
    | outOfFuel => rfl
    | stuck => rfl

/-- A task run beside the code that started it, as `task.threads()` runs it
(tasks.same-output-under-every-handler): the task runs from the frames where it starts, on a
thread that copies what it captures, and the code after its `spawn`, `rest`, goes on from its own
frames, not the task's. The world they share holds what the task writes before what `rest`
writes, and the task's reads before `rest`'s: the order of output, of reads and of the blocks of
`when` that the paragraph and shared.when-order give, which is the sequential run's. A task that
ends without a value, by a panic or, in a scope, a raise, ends the run there, and `rest` never
runs: nothing after that point appears, and every task after it is cancelled
(tasks.scope-failure). -/
def aside (task : Eval (σ × World) Value) (rest : Value → Eval (σ × World) α) :
    Eval (σ × World) α :=
  fun s => (task s).bind fun v s₁ => rest v (s.1, s₁.2)

/-- A task that leaves the frames where it starts as they were, and doesn't end as a
performance, run beside the code after its `spawn`, ends as the sequential run does, where that
code runs once the task has ended. -/
theorem aside_eq_bind {task : Eval (σ × World) Value} {rest : Value → Eval (σ × World) α}
    {s : σ × World} (hat : (task s).At s) (hset : (task s).Settled) :
    aside task rest s = Eval.bind task rest s := by
  unfold aside Eval.bind
  cases h : task s with
  | done v s₁ =>
    rw [h] at hat
    obtain ⟨fr, w⟩ := s₁
    cases (show fr = s.1 from hat)
    rfl
  | performed op v s₁ k => rw [h] at hset; exact hset.elim
  | raised e s₁ => rfl
  | jumped j s₁ => rfl
  | panicked k s₁ => rfl
  | outOfFuel => rfl
  | stuck => rfl

end Eval

/-! ## Calls that pass values in copy-in, copy-out -/

/-- Arguments bound to parameters that pass values alone. -/
def AllValues (bound : List (Name × Passed)) : Prop := ∀ p ∈ bound, ∃ v, p.2 = .value v

theorem bindArgs_values :
    ∀ {ps : List Param} {vs : List Value} {bound : List (Name × Passed)},
      bindArgs ps (vs.map .value) = some bound → AllValues bound
  | [], [], _, h => by cases h; intro p hp; cases hp
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | p :: ps, v :: vs, bound, h => by
    simp only [List.map_cons, bindArgs] at h
    cases hm : p.mode <;> simp only [hm] at h
    · obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.1 h
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ⟨v, rfl⟩
      · exact bindArgs_values hrest q hq
    · cases h

/-- Copy-out of arguments that pass values writes nothing back: the caller's
frame is as it was (values.passing-values). -/
theorem Copy.leave_values {caller callee : Copy.Frame} :
    ∀ {bound : List (Name × Passed)}, AllValues bound → Copy.leave caller callee bound = .ok caller
  | [], _ => rfl
  | (y, a) :: bound, h => by
    obtain ⟨v, hv⟩ := h (y, a) List.mem_cons_self
    simp only at hv
    subst hv
    exact Copy.leave_values (bound := bound) fun p hp => h p (List.mem_cons_of_mem _ hp)

theorem Copy.leaveWith_values {w : WriteBack} {caller callee : Copy.State}
    {bound : List (Name × Passed)} (h : AllValues bound) :
    (Copy.memoryWith w).leave caller callee bound = .ok (caller.1, callee.2) := by
  show (·, callee.2) <$> Copy.leave caller.1 callee.1 (w.order bound) = _
  rw [Copy.leave_values fun p hp => h p ((w.perm bound).mem_iff.1 hp)]
  rfl

/-- A callee's outcome, once its call has ended, leaves the caller's frame, when
the call passed values alone. -/
theorem Outcome.leaveCall_at {w : WriteBack} {bound : List (Name × Passed)} (hb : AllValues bound)
    (s : Copy.State) : ∀ (o : Outcome Copy.State Value), (o.leaveCall (Copy.memoryWith w) bound s).At s
  | .done _ s' | .raised _ s' | .panicked _ s' | .jumped (.ret _) s' => by
    simp only [Outcome.leaveCall, Copy.leaveWith_values hb, Outcome.At]
  | .jumped .brk _ | .jumped .cont _ | .outOfFuel | .stuck => trivial
  | .performed _ _ s' _ => by
    simp only [Outcome.leaveCall, Copy.leaveWith_values hb, Outcome.At]

/-- A call's outcome is a performance only when its callee's is. -/
theorem Outcome.leaveCall_settled {M : Memory σ} {bound : List (Name × Passed)} {s : σ} :
    ∀ {o : Outcome σ Value}, o.Settled → (o.leaveCall M bound s).Settled
  | .done _ s', _ | .raised _ s', _ | .panicked _ s', _ | .jumped (.ret _) s', _ => by
    simp only [Outcome.leaveCall]
    split
    · trivial
    · rename_i f _; cases f <;> trivial
  | .jumped .brk _, _ | .jumped .cont _, _ | .outOfFuel, _ | .stuck, _ => trivial

/-- In copy-in, copy-out, a call that passes values alone leaves its caller's
frame as it was, however it ends (tasks.values-in-tasks). -/
theorem Eval.call_at {D : Decls} {w : WriteBack} {run : Expr → Eval Copy.State Value} {f : Value}
    {vs : List Value} (s : Copy.State) :
    (Eval.call D (Copy.memoryWith w) run f (vs.map .value) s).At s := by
  have inv : ∀ (captured : List (Name × Value)) (params : List Param) (body : Eval Copy.State Value),
      (Eval.invoke (Copy.memoryWith w) captured params (vs.map .value) body s).At s := by
    intro captured params body
    unfold Eval.invoke
    split
    · trivial
    · rename_i bound hb
      split
      · rename_i f _; cases f <;> simp [Outcome.fault, Outcome.At]
      · exact Outcome.leaveCall_at (bindArgs_values hb) s _
  unfold Eval.call
  split
  · exact inv _ _ _
  · rename_i name types rows
    cases hd : D.fn? name with
    | none => trivial
    | some d => exact inv _ _ _
  · trivial

end Stilt
