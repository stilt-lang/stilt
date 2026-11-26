import Stilt.InPlace.Agreement
import Stilt.Modes.Agreement
import Stilt.Cycles.Run
import Stilt.Held.Run
import Stilt.Windows.Sim
import Stilt.Windows.Checked
import Stilt.Parallel.Typed

/-!
# Accepted programs and their soundness

The checks a program passes before it runs, as one predicate on the core
calculus, and the one theorem that says what they promise of its runs.

A program is **accepted** when it is well typed, which takes in mutability
(modes.what-can-be-modified) and the no-escape check (effects.no-escape), obeys
the law of exclusivity (modes.law), modifies no source of a view while the view
lives (views.change-while-viewed) and keeps every view inside its sources' scopes
(views.escaping). `soundness` says what that gives every run, at every fuel and on
every input:

* the run of the reference interpreter's model gets stuck nowhere, and raises
  only an error of the type its row allows (`typeSoundness`);
* no access to a place is ever reached by another that the law forbids, which
  the model states by what such an access would change: copy-in, copy-out,
  where each body works on copies, and in-place mutation, where every `inout`
  argument is the caller's storage, show the same and write the same output
  (`inPlaceAgreement`);
* views held as the compiler holds them, windows into their sources' storage
  that hold no copy, show what copies show (`shows_windows`, views.what-view-is);
* the reuse of storage that the modes of bindings allow, at the last uses of
  `local`, `unique` bindings and the captures of `once` closures, shows nothing
  either (`modesAgreement`);
* no cell of a `Shared<U>` whose `U` can't reach itself is on a cycle in the
  world the run ends in (`on_cycle_can_reach_itself`, cycles.can-form-cycle);
* no code but the `when` holding a shared value's cell reads or writes it: a held cell
  stays held in every state an evaluation reaches, and the `when` puts back in it the value
  its name has when its block ends (`eval_keepsHeld`, `release_puts_back`, shared.when);
* a call of a task's function never ends as a performance, so no continuation leaves its
  task (`continuations_stay`, tasks.continuations-stay-in-task);
* calls of closures with empty rows run at the same time end as they do run one after
  another, with their values in order or as the first that gives none
  (`parallel_eq_sequential`, par.sequential-meaning and par.panics).
-/

namespace Stilt

/-- The checks of a program, each a rule of the Reference that the checker
applies before the program runs. -/
structure Program.Accepted (p : Program) : Prop where
  /-- Typing, with mutability and the no-escape check. -/
  wellTyped : p.WellTyped
  /-- The law of exclusivity (modes.law, E0402 and E0404). -/
  exclusive : p.Exclusive
  /-- No source of a view modified while the view lives (views.change-while-viewed, E0423). -/
  viewsRead : p.ViewsRead
  /-- No view outlives its sources' scopes (views.escaping, E0422). -/
  viewsContained : p.ViewsContained

/-- What an accepted program's run at a fuel, on an input, keeps of the Reference's promises. -/
structure Program.Promises (p : Program) (fuel : Nat) (input : String) : Prop where
  /-- Finishing with `()`, a raise of the type the row allows, a panic or out
  of fuel; never stuck (`TypeSoundness`). -/
  typed : (p.runCopy fuel input).Sound p.decls p.row
  /-- No access breaks exclusivity: in place shows and writes what copies do
  (`InPlaceAgreement`). -/
  exclusive : (p.runCopy fuel input).shows = (p.runInPlace fuel input).shows
  /-- No view reads a source that changed or is gone: with views as windows into their
  sources' storage, the run shows and writes what copies do (views.what-view-is). -/
  views : (p.runCopy fuel input).shows = (p.runWindows fuel input).shows
  /-- The reuse the modes allow shows nothing and writes nothing else, up to the
  marks in a raised error (`ModesAgreement`). -/
  modes : (p.runCopy fuel input).shows =
    (p.markModes.runMoving fuel input).shows.map Observation.eraseRaised id
  /-- A cell on a cycle, in the world the run ends in, is one of a `Shared<U>` whose `U`
  can reach itself (`on_cycle_can_reach_itself`, cycles.can-form-cycle). -/
  cycles : ∀ w ∈ (p.runCopy fuel input).world, ∀ (u : Ty) (k : Nat), w.Chain (u, k) (u, k) →
    CanReachItself p.decls u
  /-- The discipline of `when`, a property of the evaluator that holds of every evaluation,
  whether the program is accepted or not: no code but the `when` holding a cell reads or
  writes its value. From a state whose world holds a cell, every state an evaluation reaches
  holds it, in every rest of a performance resumed where it is held too, and every cell stays
  in its place (`eval_keepsHeld`); and however a `when`'s block ends, the `when` ends the same
  way with each name's value put back in its cell and the cell let go, every other cell and
  the frames as they were (`release_puts_back`, shared.when). The calculus runs one task at a
  time, so this says nothing of threads. -/
  whenDiscipline : (∀ (n : Nat) (e : Expr) (s : Copy.State) (k : Ty × Nat), s.2.Held k →
      (eval p.decls Copy.memory n e s).KeepsHeld k s.2) ∧
    ∀ (cells : List (Name × Ty × Nat)) (o : Outcome Copy.State Value) (s s' : Copy.State),
      (cells.map Prod.snd).Nodup → o.ending? = some s →
      (∀ x h, (x, h) ∈ cells → ∃ v, Copy.read s.1 x [] = .ok v) →
      (o.release Copy.memory cells).ending? = some s' → Memory.PutBack Copy.frames false cells s s'
  /-- tasks.continuations-stay-in-task: a call of a function value of a task function's type,
  which takes no parameters and whose row holds `io` at most (tasks.task-functions), from any
  typed state, never ends as a performance: no continuation leaves the task
  (`continuations_stay`). -/
  tasks : ∀ (n : Nat) {Γ : Ctx} {η : REnv} {f : Value} {result : Ty} {io : Bool}
      {γ : Copy.State}, Value.Typed p.decls f ((Ty.fn [] result ⟨io, none, [], [], none⟩).close η) →
      State.Typed p.decls γ Γ η →
      (Eval.call p.decls Copy.memory (eval p.decls Copy.memory n) f [] γ).Settled
  /-- par.sequential-meaning and par.panics: calls of function values whose types have empty
  rows, on arguments of their parameter types, run at the same time from one typed frame,
  end as they do run one after another, from the first to the last, in every typed world
  (`parallel_eq_sequential`). -/
  parallel : ∀ (n : Nat) {Γ : Ctx} {η : REnv} {γ : Copy.Frame}, Frame.Typed p.decls γ Γ η →
      ∀ {x : World}, World.Typed p.decls x → ∀ calls : List (Value × List Value),
      (∀ c ∈ calls, ∃ ps result, Value.Typed p.decls c.1 ((Ty.fn ps result Row.pure).close η) ∧
        Passed.Typed p.decls Γ η (c.2.map .value) ps) →
      Eval.inParallel (calls.map fun c => Eval.call p.decls Copy.memory
          (eval p.decls Copy.memory n) c.1 (c.2.map .value)) (γ, x) =
        Eval.sequentially (calls.map fun c => Eval.call p.decls Copy.memory
          (eval p.decls Copy.memory n) c.1 (c.2.map .value)) (γ, x)

/-- **Soundness**: every run of an accepted program, on every input, keeps the promises. -/
def Soundness : Prop :=
  ∀ (p : Program) (fuel : Nat) (input : String), p.Accepted → p.Promises fuel input

/-- **Soundness**, proved. -/
theorem soundness : Soundness := fun p fuel input h =>
  ⟨typeSoundness p fuel input h.wellTyped, inPlaceAgreement p fuel input h.wellTyped h.exclusive,
    (inPlaceAgreement p fuel input h.wellTyped h.exclusive).trans
      (Windows.shows_windows (Windows.cases_of (Windows.declsChecked_of h.wellTyped h.exclusive
        h.viewsRead h.viewsContained)) (Windows.main_distinctParams h.wellTyped) h.exclusive.2
        h.viewsRead h.viewsContained fuel input),
    modesAgreement p fuel input h.wellTyped h.exclusive, h.wellTyped.cycles fuel input,
    p.keepsHeld,
    fun n _ _ _ _ _ _ hf hγ => continuations_stay h.wellTyped.typedDecls n hf hγ,
    fun n _ _ _ hγ _ hx calls hc => parallel_eq_sequential h.wellTyped.typedDecls n hγ hx calls hc⟩

end Stilt
