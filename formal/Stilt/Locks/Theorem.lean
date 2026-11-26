import Stilt.Locks.Calls

/-!
# A `when`'s block takes no other cell

**No `when` inside a `when`** (shared.locks): code that holds no site of `locks`, run with
any fuel in copy-in, copy-out whatever its order of write-back, from a frame whose function
values are lock-free, holds no cell in any state it reaches that the world it started in
didn't hold, and the rests of its performances, resumed in any world, hold none that world
doesn't. E0430 asks it of every `when`'s block (`Program.Locks`), so a block that holds its
cells never waits on another while it runs: the premise of `Stilt.Shared.Deadlock.Step`, a
task inside a `when` releases before it acquires, under which `no_deadlock` shows that no
system of tasks deadlocks (shared.when-order).

A call through a function value adds nothing to the fact (facts.calls-through-function-values),
so such a call may still lock when the value was made by code that does: the frame's function
values are asked to be lock-free, and a value that a `when` takes out of a cell is one the
code may not know.

The proof goes by induction on the fuel, case by case on the expression: code without a site
runs no `when`, every value it makes is lock-free, and a call of a lock-free value runs a
body without a site.
-/

namespace Stilt

open Eval.TakesNone in
/-- Evaluating code without a site of `locks`, with any fuel, takes no cell. -/
theorem eval_takesNone {D : Decls} {L : List Name} (hD : D.LocksClosed L) (w : WriteBack) :
    ∀ n, LockFreeRun D L (eval D (Copy.memoryWith w) n)
  | 0, _, _ => outOfFuel
  | n + 1, e, he => by
    have ih := eval_takesNone hD w n
    cases e <;> (try simp only [Expr.lockFree, Bool.and_eq_true, decide_eq_true_eq] at he)
    case var x => exact read w x
    case move x => exact read w x
    case int k => exact pure .int
    case bool b => exact pure .bool
    case unit => exact pure .unit
    case record R _ fs => exact bind (fields ih fs he) (fun _ hw => declare D R hw)
    case variant T _ C es => exact bind (list ih es he) (fun _ hvs => pure (.variant hvs))
    case list τ es => exact bind (list ih es he) (fun _ hvs => pure (.list hvs))
    case op o es => exact bind (list ih es he) (fun _ hvs => run w hvs)
    case view es =>
      exact bind (list ih es he) (fun _ hvs => ofExcept fun _ h =>
        Op.apply_hereditary Value.LockFree.hereditary hvs h)
    case field e f => exact bind (ih e he) (fun _ hv => ofExcept fun _ h => hv.get h)
    case index e i =>
      exact bind (ih e he.1) (fun _ hv => bind (bind (ih i he.2) (fun _ _ => asInt))
        (fun _ _ => ofExcept fun _ h => hv.get h))
    case fnRef f types rows => exact pure (.function he)
    case method t m τ =>
      simp only [Bool.not_eq_true'] at he
      exact method τ he
    case closure ps result ρ body =>
      exact bind (capture w _) (fun _ hc => pure (.closure he hc))
    case call callee as _ =>
      exact bind (ih callee he.1) (fun _ hf => bind (args ih as he.2)
        (fun _ hp => callAs w hD ih false hf hp))
    case letIn x τ init body =>
      exact bind (ih init he.1) (fun _ hv => withInit w hv (ih body he.2))
    case varIn x τ init body =>
      exact bind (ih init he.1) (fun _ hv => withInit w hv (ih body he.2))
    case assign p value =>
      obtain ⟨x, ps⟩ := p
      simp only [Expr.lockFree, Bool.and_eq_true] at he
      exact assign ih w x he.1 he.2
    case seq a b => exact bind (ih a he.1) (fun _ _ => ih b he.2)
    case «if» c τ a b =>
      exact bind (bind (ih c he.1.1) (fun _ _ => asBool)) (fun g _ => ite g (ih a he.1.2) (ih b he.2))
    case «match» e τ arms => exact bind (ih e he.1) (fun _ hv => select ih w he.2 hv)
    case «for» x τ e body => exact loop ih w x he.1 he.2
    case raise e => exact bind (ih e he) (fun _ hv => throw hv)
    case «try» e => exact ih e he
    case form _ e => exact ih e he
    case tryCatch e E x h τ => exact handle (ih e he.1) fun _ hv => withVar w hv (ih h he.2)
    case «while» c body =>
      have hl := ih (.while c body) (by simp [Expr.lockFree, he.1, he.2])
      exact bind (bind (ih c he.1) (fun _ _ => asBool)) (fun g _ => ite g
        (bind (turn (ih body he.2)) (fun g' _ => ite g' hl (pure .unit))) (pure .unit))
    case «loop» body =>
      have hl := ih (.loop body) (by simp [Expr.lockFree, he])
      exact bind (turn (ih body he)) (fun g _ => ite g hl (pure .unit))
    case «break» => exact jump trivial
    case «continue» => exact jump trivial
    case «return» e => exact bind (ih e he) (fun _ hv => jump hv)
    case perform op e => exact bind (ih e he) (fun _ hv => perform w hv)
    case withH E c h b =>
      exact bind (ih h he.1) (fun _ hh s hs => Outcome.TakesNone.letGo w _ <|
        Outcome.TakesNone.handleWith w hh (fun _ v s' hc hv hs' =>
          callAs w hD ih c hc (passed := [.value v]) (fun q hq => by
            simp only [List.mem_singleton] at hq; subst hq; exact hv) s' hs')
          (ih b he.2 s hs))
    case held ns hs b => simp at he

/-- **No `when` inside a `when`** (shared.locks): in a program that passes E0430, the block of
every `when` it writes, as written or instantiated, run with any fuel from a frame whose
function values are lock-free, holds no cell in any state it reaches that its world didn't
hold when it started, and neither do its performances' rests, from the world each is resumed
in. Of shared.when-order, this states that no block waits on a value while it holds one; the
calculus runs one task, so the order among tasks and the output under every handler of
`async` are left out (shared.when-order). -/
theorem Program.Locks.block {p : Program} (hp : p.Locks) (w : WriteBack) (n : Nat) {b : Expr}
    (hb : b ∈ p.whenBlocks) (ts : TySubst) (rs : RowSubst) {s : Copy.State}
    (hs : Frame.LockFree p.decls p.decls.locks s.1) :
    (eval p.decls (Copy.memoryWith w) n ((b.substTys ts).substRows rs) s).TakesNone p.decls
      p.decls.locks (Value.LockFree p.decls p.decls.locks) s.2 :=
  eval_takesNone p.decls.locks_closed w n _
    (by rw [Expr.lockFree_substRows, Expr.lockFree_substTys]; exact hp b hb) s hs

end Stilt
