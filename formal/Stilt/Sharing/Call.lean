import Stilt.Sharing.Leave
import Stilt.InPlace.Call

/-!
# Calls with sharing

A call keeps the simulation when every binding is shared: each root of an `inout` argument
stops sharing when the call starts (`unshareArgs`), the callee starts alike
(`Stilt.Sharing.Enter`), its body runs alike, and what copy-out writes back when it ends is
what sharing wrote in place (`Stilt.Sharing.Leave`). A performance leaves the call as a raise
does, and its rest leaves it again when it ends.
-/

namespace Stilt.Sharing

open InPlace (Passed.Compat)

variable {shared : Name → Bool}

/-- The end of a call, with the worlds: both models leave it alike, the caller going on in the
world the callee ended in. -/
theorem leave_in {fr : Copy.State} {s : State × World} (hs : AgreesIn fr s)
    {bound : List (Name × Passed)} {frc : Copy.Frame} {sc : State}
    (hent : Entered s.1 bound frc sc) (hcompat : (bound.map Prod.snd).Pairwise Passed.Compat)
    (halone : ∀ y x p, (y, Passed.place x p) ∈ bound → Alone s.1 x) {fr' : Copy.State}
    {s' : State × World} (hag : AgreesIn fr' s') (hF : Follows sc s'.1) :
    ∃ fr'', Copy.memory.leave fr fr' bound = .ok fr'' ∧
      (memory shared).leave s s' bound = .ok (⟨s.1.env, s'.1.store⟩, s'.2) ∧
      AgreesIn fr'' (⟨s.1.env, s'.1.store⟩, s'.2) ∧ Follows s.1 ⟨s.1.env, s'.1.store⟩ := by
  obtain ⟨fr'', hleave, hag'', hF''⟩ := leave_agrees hs.1 hs.2.1 hent hcompat halone hag.1 hF
  refine ⟨(fr'', fr'.2), ?_, rfl, ⟨hag'', hs.2.1.store _, hag.2.2.1, hag.2.2.2⟩, hF''⟩
  show (·, fr'.2) <$> Copy.frames.leave fr.1 fr'.1 bound = _
  rw [hleave]
  rfl

/-- The callee's outcome as its call's keeps the simulation: a value, a raise, a `return`, a
panic and a performance leave the call alike, and a performance's rest leaves it alike when it
ends. -/
theorem Corr.leaveCall {fr : Copy.State} {s : State × World} (hs : AgreesIn fr s)
    {bound : List (Name × Passed)} {frc : Copy.Frame} {sc : State}
    (hent : Entered s.1 bound frc sc) (hcompat : (bound.map Prod.snd).Pairwise Passed.Compat)
    (halone : ∀ y x p, (y, Passed.place x p) ∈ bound → Alone s.1 x)
    {o : Outcome Copy.State Value} {o' : Outcome (State × World) Value}
    (h : Corr Value.Safe sc o o') :
    Corr Value.Safe s.1 (o.leaveCall Copy.memory bound fr)
      (o'.leaveCall (memory shared) bound s) := by
  induction o generalizing o' with
  | performed op v frk k ih =>
    cases o' with
    | performed op' v' sk k' =>
      obtain ⟨⟨rfl, rfl, hv, hag, hev⟩, hk⟩ := h
      obtain ⟨_, h₁, h₂, hag'', hev''⟩ := leave_in (shared := shared) hs hent hcompat halone hag hev
      simp only [Outcome.leaveCall, h₁, h₂]
      exact ⟨⟨rfl, rfl, hv, hag'', hev''⟩, fun w x w' x' hw => ih w x (hk w x w' x' hw)⟩
    | _ => exact absurd h id
  | done v fr' =>
    cases o' with
    | done v' s' =>
      obtain ⟨rfl, hv, hag, hev⟩ := h
      obtain ⟨_, h₁, h₂, hag'', hev''⟩ := leave_in (shared := shared) hs hent hcompat halone hag hev
      simp only [Outcome.leaveCall, h₁, h₂]
      exact ⟨rfl, hv, hag'', hev''⟩
    | _ => exact absurd h id
  | raised e fr' =>
    cases o' with
    | raised e' s' =>
      obtain ⟨rfl, he, hag, hev⟩ := h
      obtain ⟨_, h₁, h₂, hag'', hev''⟩ := leave_in (shared := shared) hs hent hcompat halone hag hev
      simp only [Outcome.leaveCall, h₁, h₂]
      exact ⟨rfl, he, hag'', hev''⟩
    | _ => exact absurd h id
  | jumped j fr' =>
    cases o' with
    | jumped j' s' =>
      obtain ⟨rfl, hj, hag, hev⟩ := h
      cases j with
      | ret v =>
        obtain ⟨_, h₁, h₂, hag'', hev''⟩ :=
          leave_in (shared := shared) hs hent hcompat halone hag hev
        simp only [Outcome.leaveCall, h₁, h₂]
        exact ⟨rfl, hj, hag'', hev''⟩
      | brk | cont => exact (trivial : Corr Value.Safe s.1 .stuck .stuck)
    | _ => exact absurd h id
  | panicked k fr' =>
    cases o' with
    | panicked k' s' =>
      obtain ⟨rfl, hag, hev⟩ := h
      obtain ⟨_, h₁, h₂, hag'', hev''⟩ := leave_in (shared := shared) hs hent hcompat halone hag hev
      simp only [Outcome.leaveCall, h₁, h₂]
      exact ⟨rfl, hag'', hev''⟩
    | _ => exact absurd h id
  | outOfFuel =>
    cases o' <;> first | exact absurd h id | exact (trivial : Corr Value.Safe s.1 .outOfFuel .outOfFuel)
  | stuck => cases o' <;> first | exact absurd h id | exact (trivial : Corr Value.Safe s.1 .stuck .stuck)

/-- The roots of a call's `inout` arguments that name bindings are alone. -/
def RootsAlone (s : State) (passed : List Passed) : Prop :=
  ∀ x p, Passed.place x p ∈ passed → (s.env.lookup x).isSome → Alone s x

/-- A call of a safe function value, from a state whose roots are alone, keeps the
simulation. -/
theorem Corr.invoke (hsh : ∀ y, shared y = true) {captured : List (Name × Value)}
    (hc : ∀ xv ∈ captured, xv.2.Safe) {params : List Param}
    (hnd : (params.map Param.name).Nodup) {passed : List Passed}
    (hpassed : InPlace.Sim.PassedSafe passed) (hcompat : passed.Pairwise Passed.Compat)
    {body : Eval Copy.State Value} {body' : Eval (State × World) Value}
    (hb : Sim Value.Safe body body') {fr : Copy.State} {s : State × World} (hs : AgreesIn fr s)
    (hr : RootsAlone s.1 passed) :
    Corr Value.Safe s.1 (Eval.invoke Copy.memory captured params passed body fr)
      (Eval.invoke (memory shared) captured params passed body' s) := by
  unfold Eval.invoke
  cases hbind : bindArgs params passed with
  | none => trivial
  | some bound =>
    obtain ⟨hnames, hsnd⟩ := InPlace.bindArgs_spec hbind
    dsimp only
    have hmem : ∀ y x p, (y, Passed.place x p) ∈ bound → Passed.place x p ∈ passed :=
      fun y x p h => hsnd ▸ List.mem_map_of_mem (f := Prod.snd) h
    have hroots : ∀ y x p e, (y, Passed.place x p) ∈ bound → s.1.env.lookup x = some e →
        e.alias = none := fun y x p e h hl => by
      obtain ⟨e', hl', ha', -⟩ := hr x p (hmem y x p h) (by simp [hl])
      rw [hl] at hl'
      cases hl'
      exact ha'
    rw [← hsnd] at hcompat hpassed
    rcases hs.1.enter hsh hc (by rw [hnames]; exact hnd) hcompat hpassed hroots with
      ⟨f, h₁, h₂⟩ | ⟨frc, sc, h₁, h₂, hent⟩
    · rw [Copy.memory, memory, Frames.withWorld_enter, Frames.withWorld_enter, h₁, h₂,
        Frames.map_error, Frames.map_error]
      exact Corr.fault hs f
    · rw [Copy.memory, memory, Frames.withWorld_enter, Frames.withWorld_enter, h₁, h₂,
        Frames.map_ok, Frames.map_ok]
      have halone : ∀ y x p, (y, Passed.place x p) ∈ bound → Alone s.1 x := fun y x p h => by
        obtain ⟨e, hl, -⟩ := hent.places y x p h
        exact hr x p (hmem y x p h) (by simp [hl])
      exact Corr.leaveCall hs hent hcompat halone
        (hb (frc, fr.2) (sc, s.2) ⟨hent.agrees, hent.shared, hs.2.2⟩)

/-- Calling a safe value, from a state whose roots are alone, keeps the simulation. -/
theorem Corr.call {D : Decls} (hD : InPlace.Sim.DeclsSafe D) (hsh : ∀ y, shared y = true)
    {run : Expr → Eval Copy.State Value} {run' : Expr → Eval (State × World) Value}
    (h : SimRun run run') {f : Value} (hf : f.Safe) {passed : List Passed}
    (hpassed : InPlace.Sim.PassedSafe passed) (hcompat : passed.Pairwise Passed.Compat)
    {fr : Copy.State} {s : State × World} (hs : AgreesIn fr s) (hr : RootsAlone s.1 passed) :
    Corr Value.Safe s.1 (Eval.call D Copy.memory run f passed fr)
      (Eval.call D (memory shared) run' f passed s) := by
  cases f with
  | closure captured params result ρ body =>
    cases hf with
    | closure hnd hex hdp hc =>
      exact Corr.invoke hsh hc hnd hpassed hcompat (h body ⟨⟨[], hex⟩, hdp⟩) hs hr
  | function name types rows =>
    unfold Eval.call
    dsimp only
    cases hd : D.fn? name with
    | none => exact Sim.fail _ fr s hs
    | some d =>
      obtain ⟨hnd, hex, hdp⟩ := hD d (List.mem_of_find?_eq_some hd)
      refine Corr.invoke (captured := []) hsh (by simp) hnd hpassed hcompat
        (h _ ⟨⟨[], ?_⟩, ?_⟩) hs hr
      · rw [Expr.exclusive_substRows, Expr.exclusive_substTys]
        exact hex
      · rw [Expr.distinctParams_substRows, Expr.distinctParams_substTys]
        exact hdp
  | _ => exact Sim.fail _ fr s hs

/-- A call as code or a `with` makes it, from a state whose roots are alone. -/
theorem Corr.callAs {D : Decls} (hD : InPlace.Sim.DeclsSafe D) (hsh : ∀ y, shared y = true)
    {run : Expr → Eval Copy.State Value} {run' : Expr → Eval (State × World) Value}
    (h : SimRun run run') (control : Bool) {f : Value} (hf : f.Safe) {passed : List Passed}
    (hpassed : InPlace.Sim.PassedSafe passed) (hcompat : passed.Pairwise Passed.Compat)
    {fr : Copy.State} {s : State × World} (hs : AgreesIn fr s) (hr : RootsAlone s.1 passed) :
    Corr Value.Safe s.1 (Eval.callAs D Copy.memory run control f passed fr)
      (Eval.callAs D (memory shared) run' control f passed s) := by
  unfold Eval.callAs
  split
  · exact Sim.fail _ fr s hs
  · exact Corr.call hD hsh h hf hpassed hcompat hs hr

/-- A call keeps the simulation when every binding is shared: each root of an `inout` argument
stops sharing when the call starts (`unshareArgs`), the body runs alike, and what copy-out
writes back when the call ends is what sharing wrote in place (modes.shared-writes). -/
theorem Sim.callAs {D : Decls} (hD : InPlace.Sim.DeclsSafe D) (hsh : ∀ y, shared y = true)
    {run : Expr → Eval Copy.State Value} {run' : Expr → Eval (State × World) Value}
    (h : SimRun run run') (control : Bool) {f : Value} (hf : f.Safe) {passed : List Passed}
    (hpassed : InPlace.Sim.PassedSafe passed) (hcompat : passed.Pairwise Passed.Compat) :
    Sim Value.Safe (Eval.callAs D Copy.memory run control f passed)
      (unshareArgs passed >>= fun _ => Eval.callAs D (memory shared) run' control f passed) := by
  intro fr s hs
  obtain ⟨s₁, h₁, hs₁, hF, -, hr⟩ := unshareArgs_agrees passed hs
  show Corr Value.Safe s.1 _ ((unshareArgs passed s).bind fun _ s' => _)
  rw [h₁]
  exact (Corr.callAs hD hsh h control hf hpassed hcompat hs₁ hr).follow hF

end Stilt.Sharing
