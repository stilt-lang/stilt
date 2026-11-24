import Stilt.OneShot.Steps
import Stilt.OneShot.Instances
import Stilt.Matching

/-!
# Runs that resume at most so often

The evaluator's steps that run expressions keep `Eval.OneShot`, given that
running checked code does (`OneShotRun`): a list of expressions, a record's
fields, the indexes of a place, a call's arguments, a `match`, an assignment,
a `for` loop, whose body, when it never resumes, may run any number of times,
and a call, whose callee's body resumes at most once when a `with` that takes
control calls it, and never otherwise.
-/

namespace Stilt

/-- Running checked code that may resume at most once performs at most the
`resume`s its text counts. -/
def OneShotRun (run : Expr → Eval Copy.State Value) : Prop :=
  ∀ e, e.oneShot = true → e.resumes ≤ 1 → Eval.OneShot e.resumes Value.OneShot (run e)

theorem armsOneShot_mem : ∀ {arms : List Arm} {arm : Arm}, armsOneShot arms = true → arm ∈ arms →
    arm.body.oneShot = true ∧ arm.body.resumes ≤ armsResumes arms
  | ⟨_, _, _⟩ :: _, _, h, hm => by
    simp only [armsOneShot, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨h.1, by simp only [armsResumes]; omega⟩
    · obtain ⟨h₁, h₂⟩ := armsOneShot_mem h.2 hm
      exact ⟨h₁, by simp only [armsResumes]; omega⟩

/-- A loop that may run its body twice counts two. -/
theorem loopResumes_le {n : Nat} (h : loopResumes n ≤ 1) : n = 0 := by
  unfold loopResumes at h
  split at h <;> omega

namespace Eval.OneShot

variable {run : Expr → Eval Copy.State Value} (h : OneShotRun run)
include h

theorem list : ∀ (es : List Expr), exprsOneShot es = true → exprsResumes es ≤ 1 →
    Eval.OneShot (exprsResumes es) (fun vs : List Value => ∀ v ∈ vs, v.OneShot) (Eval.list run es)
  | [], _, _ => pure (by simp)
  | e :: es, hes, hn => by
    simp only [exprsOneShot, Bool.and_eq_true] at hes
    simp only [exprsResumes] at hn ⊢
    refine bindLe (h e hes.1 (by omega)) (fun v hv => bindLe (n := exprsResumes es) (b := 0) (list es hes.2 (by omega))
      (fun vs hvs => pure fun u hu => ?_) (by omega)) (by omega)
    rcases List.mem_cons.1 hu with rfl | hu
    · exact hv
    · exact hvs u hu

theorem fields : ∀ (fs : List (Name × Expr)), fieldsOneShot fs = true → fieldsResumes fs ≤ 1 →
    Eval.OneShot (fieldsResumes fs) (fun ws : List (Name × Value) => ∀ fv ∈ ws, fv.2.OneShot)
      (Eval.fields run fs)
  | [], _, _ => pure (by simp)
  | (f, e) :: fs, hfs, hn => by
    simp only [fieldsOneShot, Bool.and_eq_true] at hfs
    simp only [fieldsResumes] at hn ⊢
    refine bindLe (h e hfs.1 (by omega)) (fun v hv => bindLe (n := fieldsResumes fs) (b := 0) (fields fs hfs.2 (by omega))
      (fun ws hws => pure fun fv hfv => ?_) (by omega)) (by omega)
    rcases List.mem_cons.1 hfv with rfl | hfv
    · exact hv
    · exact hws fv hfv

theorem path : ∀ (ps : List Projection), pathOneShot ps = true → pathResumes ps ≤ 1 →
    Eval.OneShot (pathResumes ps) (fun _ => True) (Eval.path run ps)
  | [], _, _ => pure trivial
  | .field _ :: ps, hps, hn => by
    simp only [pathOneShot] at hps
    simp only [pathResumes] at hn ⊢
    exact bindLe (b := 0) (path ps hps hn) (fun _ _ => pure trivial) (by omega)
  | .index i :: ps, hps, hn => by
    simp only [pathOneShot, Bool.and_eq_true] at hps
    simp only [pathResumes] at hn ⊢
    exact bindLe (bindLe (b := 0) (h i hps.1 (by omega)) (fun _ _ => asInt) (Nat.le_refl _))
      (fun _ _ => bindLe (b := 0) (path ps hps.2 (by omega)) (fun _ _ => pure trivial) (Nat.le_refl _))
      (by omega)

theorem args : ∀ (as : List Arg), argsOneShot as = true → argsResumes as ≤ 1 →
    Eval.OneShot (argsResumes as) (fun passed : List Passed => ∀ q ∈ passed, q.OneShot)
      (Eval.args run as)
  | [], _, _ => pure (by simp)
  | .value e :: as, has, hn => by
    simp only [argsOneShot, Bool.and_eq_true] at has
    simp only [argsResumes] at hn ⊢
    refine bindLe (h e has.1 (by omega)) (fun v hv => bindLe (n := argsResumes as) (b := 0) (args as has.2 (by omega))
      (fun ps hps => pure fun q hq => ?_) (by omega)) (by omega)
    rcases List.mem_cons.1 hq with rfl | hq
    · cases e <;> exact hv
    · exact hps q hq
  | .inout ⟨x, projections⟩ :: as, has, hn => by
    simp only [argsOneShot, Bool.and_eq_true] at has
    simp only [argsResumes] at hn ⊢
    refine bindLe (path h projections has.1 (by omega)) (fun _ _ =>
      bindLe (n := argsResumes as) (b := 0) (args as has.2 (by omega))
        (fun ps hps => pure fun q hq => ?_) (by omega))
      (by omega)
    rcases List.mem_cons.1 hq with rfl | hq
    · trivial
    · exact hps q hq

theorem select (w : WriteBack) {arms : List Arm} (harms : armsOneShot arms = true)
    (hn : armsResumes arms ≤ 1) {v : Value} (hv : v.OneShot) :
    Eval.OneShot (armsResumes arms) Value.OneShot (Eval.select (Copy.memoryWith w) run arms v) := by
  unfold Eval.select
  cases hsel : selectArm arms v with
  | none => exact stuck
  | some au =>
    obtain ⟨arm, us⟩ := au
    obtain ⟨hmem, hm⟩ := selectArm_mem hsel
    obtain ⟨hb, hbn⟩ := armsOneShot_mem harms hmem
    dsimp only
    split
    · exact withVars w ((h _ hb (by omega)).mono hbn fun _ h => h) _ fun xv hxv =>
        arm.pattern.matchOn_parts Value.OneShot.passesToParts hv hm xv.2 (List.of_mem_zip hxv).2
    · exact stuck

theorem assign (w : WriteBack) (x : Name) {ps : List Projection} (hps : pathOneShot ps = true)
    {value : Expr} (hv : value.oneShot = true) (hn : pathResumes ps + value.resumes ≤ 1) :
    Eval.OneShot (pathResumes ps + value.resumes) Value.OneShot
      (Eval.assign (Copy.memoryWith w) run x ps value) :=
  bindLe (path h ps hps (by omega)) (fun _ _ => bindLe (h value hv (by omega)) (fun _ hw =>
    bindLe (n := 0) (a := 0) (b := 0) (update fun _ _ hs h' => by
      obtain ⟨_, hfr, rfl⟩ := Frames.withWorld_write_ok _ h'
      exact ⟨Frame.OneShot.write hs.1 hw hfr, hs.2⟩)
      (fun _ _ => pure .unit) (Nat.le_refl _)) (by omega)) (Nat.le_refl _)

/-- A `for` loop whose body never resumes. -/
theorem loop (w : WriteBack) (x : Name) {e body : Expr} (he : e.oneShot = true) (hb : body.oneShot = true)
    (hn : e.resumes ≤ 1) (hb0 : body.resumes = 0) :
    Eval.OneShot e.resumes Value.OneShot (Eval.loop (Copy.memoryWith w) run x e body) := by
  have hbody : Eval.OneShot 0 Value.OneShot (run body) := hb0 ▸ h body hb (by omega)
  exact bindLe (bindLe (b := 0) (h e he hn) (fun _ hv => asList hv) (Nat.le_refl _))
    (fun vs hvs => bindLe (b := 0) (forEach (fun v hv => withVar w hv (turn hbody)) vs hvs)
      (fun _ _ => pure .unit) (Nat.le_refl _)) (by omega)

end Eval.OneShot

end Stilt
