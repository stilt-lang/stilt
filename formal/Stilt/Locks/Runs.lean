import Stilt.Locks.Steps
import Stilt.Locks.Instances
import Stilt.InPlace.Enter

/-!
# Runs that take no cell

The evaluator's steps that run expressions keep `Eval.TakesNone`, given that running code
without a site of `locks` does (`LockFreeRun`): a list of expressions, a record's fields, the
indexes of a place, a call's arguments, a `match`, an assignment, a `for` loop, a method's
function, and a call of a lock-free function value, whose body holds no site: a closure's by
the value, a declared function's by `Decls.LocksClosed`, instantiated or not (shared.locks).
-/

namespace Stilt

variable {D : Decls} {L : List Name}

/-- Running code without a site of `locks` takes no cell. -/
def LockFreeRun (D : Decls) (L : List Name) (run : Expr → Eval Copy.State Value) : Prop :=
  ∀ e, e.lockFree D L = true → Eval.TakesNone D L (Value.LockFree D L) (run e)

theorem armsLockFree_mem : ∀ {arms : List Arm} {arm : Arm}, armsLockFree D L arms = true →
    arm ∈ arms → arm.body.lockFree D L = true
  | ⟨_, _, _⟩ :: _, _, h, hm => by
    simp only [armsLockFree, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h.1
    · exact armsLockFree_mem h.2 hm

namespace Eval.TakesNone

variable {run : Expr → Eval Copy.State Value} (h : LockFreeRun D L run)
include h

theorem list : ∀ (es : List Expr), exprsLockFree D L es = true →
    Eval.TakesNone D L (fun vs : List Value => ∀ v ∈ vs, v.LockFree D L) (Eval.list run es)
  | [], _ => pure (by simp)
  | e :: es, hes => by
    simp only [exprsLockFree, Bool.and_eq_true] at hes
    refine bind (h e hes.1) (fun v hv => bind (list es hes.2) (fun vs hvs => pure fun u hu => ?_))
    rcases List.mem_cons.1 hu with rfl | hu
    · exact hv
    · exact hvs u hu

theorem fields : ∀ (fs : List (Name × Expr)), fieldsLockFree D L fs = true →
    Eval.TakesNone D L (fun ws : List (Name × Value) => ∀ fv ∈ ws, fv.2.LockFree D L)
      (Eval.fields run fs)
  | [], _ => pure (by simp)
  | (f, e) :: fs, hfs => by
    simp only [fieldsLockFree, Bool.and_eq_true] at hfs
    refine bind (h e hfs.1) (fun v hv => bind (fields fs hfs.2) (fun ws hws => pure fun fv hfv => ?_))
    rcases List.mem_cons.1 hfv with rfl | hfv
    · exact hv
    · exact hws fv hfv

theorem path : ∀ (ps : List Projection), pathLockFree D L ps = true →
    Eval.TakesNone D L (fun _ => True) (Eval.path run ps)
  | [], _ => pure trivial
  | .field _ :: ps, hps => by
    simp only [pathLockFree] at hps
    exact bind (path ps hps) (fun _ _ => pure trivial)
  | .index i :: ps, hps => by
    simp only [pathLockFree, Bool.and_eq_true] at hps
    exact bind (bind (h i hps.1) (fun _ _ => asInt))
      (fun _ _ => bind (path ps hps.2) (fun _ _ => pure trivial))

theorem args : ∀ (as : List Arg), argsLockFree D L as = true →
    Eval.TakesNone D L (fun passed : List Passed => ∀ q ∈ passed, q.LockFree D L)
      (Eval.args run as)
  | [], _ => pure (by simp)
  | .value e :: as, has => by
    simp only [argsLockFree, Bool.and_eq_true] at has
    refine bind (h e has.1) (fun v hv => bind (args as has.2) (fun ps hps => pure fun q hq => ?_))
    rcases List.mem_cons.1 hq with rfl | hq
    · cases e <;> exact hv
    · exact hps q hq
  | .inout ⟨x, projections⟩ :: as, has => by
    simp only [argsLockFree, Bool.and_eq_true] at has
    refine bind (path h projections has.1) (fun _ _ =>
      bind (args as has.2) (fun ps hps => pure fun q hq => ?_))
    rcases List.mem_cons.1 hq with rfl | hq
    · trivial
    · exact hps q hq

theorem select (w : WriteBack) {arms : List Arm} (harms : armsLockFree D L arms = true)
    {v : Value} (hv : v.LockFree D L) :
    Eval.TakesNone D L (Value.LockFree D L) (Eval.select (Copy.memoryWith w) run arms v) := by
  unfold Eval.select
  cases hsel : selectArm arms v with
  | none => exact stuck
  | some au =>
    obtain ⟨arm, us⟩ := au
    obtain ⟨hmem, hm⟩ := selectArm_mem hsel
    dsimp only
    split
    · exact withVars w (h _ (armsLockFree_mem harms hmem)) _ fun xv hxv =>
        arm.pattern.matchOn_parts Value.LockFree.passesToParts hv hm xv.2 (List.of_mem_zip hxv).2
    · exact stuck

theorem assign (w : WriteBack) (x : Name) {ps : List Projection} (hps : pathLockFree D L ps = true)
    {value : Expr} (hv : value.lockFree D L = true) :
    Eval.TakesNone D L (Value.LockFree D L) (Eval.assign (Copy.memoryWith w) run x ps value) :=
  bind (path h ps hps) (fun _ _ => bind (h value hv) (fun _ hw =>
    bind (update fun _ _ hs h' => by
      obtain ⟨_, hfr, rfl⟩ := Frames.withWorld_write_ok _ h'
      exact ⟨Frame.LockFree.write hs hw hfr, rfl⟩)
      (fun _ _ => pure .unit)))

theorem loop (w : WriteBack) (x : Name) {e body : Expr} (he : e.lockFree D L = true)
    (hb : body.lockFree D L = true) :
    Eval.TakesNone D L (Value.LockFree D L) (Eval.loop (Copy.memoryWith w) run x e body) :=
  bind (bind (h e he) (fun _ hv => asList hv))
    (fun vs hvs => bind (forEach (fun _ hv => withVar w hv (turn (h body hb))) vs hvs)
      (fun _ _ => pure .unit))

end Eval.TakesNone

end Stilt
