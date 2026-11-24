import Stilt.Windows.Steps

/-!
# A run of `main`

`main` starts from empty stores, in a context with no variable, no read around it and no caller.
When its evaluation ends alike in both models, the runs show the same: the value returned or the
error raised, read through its windows at the end of the run of windows, is the in-place one, and
both worlds are the same (program.main).
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls}

/-- The context `main` runs in. -/
def Ctx.main : Ctx := ⟨[], [], [], 0, [], fun _ => [], fun _ => none⟩

theorem Pre.main (input : String) :
    Pre D Ctx.main [] (⟨[], []⟩, World.start input) (⟨[], []⟩, World.start input) where
  agree := Agree.mk rfl rfl rfl (fun _ h => nomatch h) (World.All.start input) List.Pairwise.nil
    (fun _ h => nomatch h) fun ℓ x h => by
      change ([] : List (Option Value))[ℓ]? = _ at h
      simp at h
  fits := .base (fun _ h => nomatch h) (fun _ h => nomatch h)
  outer ℓ x h := by simp [Ctx.main] at h
  owned ℓ x _ h := by
    change ([] : List (Option Value))[ℓ]? = _ at h
    simp at h
  pend _ h := nomatch h
  start := Nat.zero_le _
  alive ℓ y h := by simp [Ctx.main] at h

theorem Guards.main : Guards D Ctx.main [] [] where
  fenced := .base (fun _ h => nomatch h) (fun _ h => nomatch h)
  brought _ h := nomatch h
  old ℓ h := by simp [Ctx.main] at h
  pend _ h := nomatch h
  start _ h := nomatch h

/-- A value read alike is what the run of windows shows of it. -/
theorem resolve_of_leaving {si : IState} {sw : WState} {v w : Value}
    (h : VRel si.1.store sw.1.store w v) : resolve sw.1.store w = .ok v := h.resolve

/-- Runs of `main` that end alike show the same. -/
theorem shows_of_sim {S : List Shape} {o : Outcome IState Value} {o' : Outcome WState Value}
    (h : o.Rel (CorrG D Ctx.main [] (ValG D Ctx.main S) []) o') :
    o.leaveBody.shows = (o'.leaveBody.resolveWindows).shows := by
  cases o <;> cases o' <;> simp only [Outcome.Rel] at h <;> try exact absurd h id
  case done.done v si w sw =>
    obtain ⟨hp, -, hv, -⟩ := h
    simp only [Outcome.leaveBody, Outcome.resolveWindows, hv.resolve, Outcome.shows,
      Outcome.observe, Outcome.output, hp.agree.world]
  case raised.raised e si e' sw =>
    obtain ⟨hp, -, hv, -⟩ := h
    simp only [Outcome.leaveBody, Outcome.resolveWindows, hv.resolve, Outcome.shows,
      Outcome.observe, Outcome.output, hp.agree.world]
  case jumped.jumped j si j' sw =>
    obtain ⟨hp, -, hj⟩ := h
    rcases j with _ | _ | v <;> rcases j' with _ | _ | w <;> simp only at hj
    · simp only [Outcome.leaveBody, Outcome.resolveWindows, Outcome.shows, Outcome.observe,
        Outcome.output, hp.agree.world]
    · simp only [Outcome.leaveBody, Outcome.resolveWindows, Outcome.shows, Outcome.observe,
        Outcome.output, hp.agree.world]
    · simp only [Outcome.leaveBody, Outcome.resolveWindows, hj.1.resolve, Outcome.shows,
        Outcome.observe, Outcome.output, hp.agree.world]
  case panicked.panicked k si k' sw =>
    obtain ⟨hp, -, rfl⟩ := h
    simp only [Outcome.leaveBody, Outcome.resolveWindows, Outcome.shows, Outcome.observe,
      Outcome.output, hp.agree.world]
  all_goals rfl

/-- When `main`'s evaluation keeps the simulation, its runs in place and with windows show the
same. -/
theorem shows_of_main {p : Program} {fuel : Nat} {S : List Shape}
    (h : Sim p.decls Ctx.main [] S (Stilt.eval p.decls InPlace.memory fuel p.main)
      (Windows.eval p.decls fuel p.main)) (input : String) :
    (p.runInPlace fuel input).shows = (p.runWindows fuel input).shows :=
  shows_of_sim (h _ _ (Pre.main input) Guards.main trivial)

end Windows

end Stilt
