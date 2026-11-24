import Stilt.InPlace.Leave
import Stilt.InPlace.Instances

/-!
# Calls

A call keeps the simulation: it starts alike in both models
(`Stilt.InPlace.Enter`), its body runs alike, and it ends alike
(`Stilt.InPlace.Leave`), with the caller's state evolved only by writes to
the places of its `inout` arguments. A performance leaves the call as a raise
does, and its rest leaves it again when it ends.
-/

namespace Stilt.InPlace

/-- The end of a call: copy-in, copy-out's write-back gives a frame that agrees
with the store the callee left, and the caller's state evolved only by writes
to the places of its `inout` arguments. -/
theorem leave_agrees {fr : Copy.Frame} {s : State} (hs : Agrees fr s)
    {bound : List (Name × Passed)} {frc : Copy.Frame} {sc : State} (hent : Entered s bound frc sc)
    (hcompat : (bound.map Prod.snd).Pairwise Passed.Compat) {fr' : Copy.Frame} {s' : State}
    (hag : Agrees fr' s') (hev : Evolves sc s') :
    ∃ fr'', Copy.frames.leave fr fr' bound = .ok fr'' ∧ Agrees fr'' ⟨s.env, s'.store⟩ ∧
      Evolves s ⟨s.env, s'.store⟩ := by
  obtain ⟨henv, W, st, extra, hs', hW, hseq⟩ := hev
  obtain ⟨F, hF⟩ := hent.store
  rw [hF] at hseq
  obtain ⟨A', B', hR, hlen, -, hlow, -⟩ := setSeq_append_store
    (fun pw hpw => atLoc_of_under (hW pw hpw)) hseq
  simp only [Value.list.injEq] at hR
  subst hR
  have hvalid : ∀ P ∈ bound.filterMap (placePath s), ∃ u, (Value.list s.store).get P = .ok u := by
    intro P hP
    obtain ⟨y, x, p, r, hmem, hl, rfl⟩ := mem_placePaths hP
    obtain ⟨r', hl', -, u, hu⟩ := hent.places y x p hmem
    rw [hl] at hl'
    cases hl'
    refine ⟨u, ?_⟩
    show (Value.list s.store).get (r.toPath ++ p) = _
    rw [← deref_eq_get (lt_of_deref hu) s.env]
    exact hu
  have hunder : ∀ pw ∈ W.filter (below s.store.length),
      pw.1.Under (bound.filterMap (placePath s)) := by
    intro pw hpw
    obtain ⟨hpw, hb⟩ := List.mem_filter.1 hpw
    obtain ⟨P, hP, q, hq⟩ := hW pw hpw
    obtain ⟨xr, hxr, rfl⟩ := List.mem_map.1 hP
    rcases hent.refs xr hxr with hfresh | ⟨y, x, p, r, hmem, hl, heq⟩
    · simp [below, hq, Ref.toPath] at hb
      omega
    · refine ⟨(placeRef r p).toPath, List.mem_filterMap.2 ⟨_, hmem, ?_⟩, q, by rw [hq, heq]⟩
      simp [placePath, hl]
  obtain ⟨L, hL, hget, hseqL⟩ :=
    Value.setSeq_canon (placePaths_disjoint hs.disjoint hcompat) hvalid hunder hlow
  have hread : ∀ y x p, (y, Passed.place x p) ∈ bound → ∃ r, s.env.lookup x = some r ∧
      Copy.read fr' y [] = (Value.list A').get (placeRef r p).toPath := by
    intro y x p hmem
    obtain ⟨r, hl, hly, u, hu⟩ := hent.places y x p hmem
    have hlt := lt_of_deref hu
    refine ⟨r, hl, ?_⟩
    rw [hag.read]
    simp only [InPlace.read, henv, hly]
    rw [deref_store, hs', List.append_assoc, deref_eq_get (by simp [placeRef]; omega),
      get_append_low (by simpa [placeRef, hlen] using hlt), List.append_nil]
  obtain ⟨fr'', hfold, hag''⟩ := leave_fold hread (fun _ _ _ _ _ hv => hag.read_safe hv) bound
    (fun _ h => h) fr s.store L hs (by rw [hL]) hget hseqL
  refine ⟨fr'', by rw [copy_leave_eq]; exact hfold, ?_, ?_⟩
  · rw [hs', List.append_assoc]
    exact hag''.store_append _
  · refine ⟨rfl, L, A', B' ++ extra, by rw [hs', List.append_assoc], fun pw hpw => ?_, hseqL⟩
    have hP : pw.1 ∈ bound.filterMap (placePath s) := hL ▸ List.mem_map_of_mem hpw
    obtain ⟨y, x, p, r, hmem, hl, hP⟩ := mem_placePaths hP
    exact ⟨r.toPath, List.mem_map.2 ⟨(x, r), mem_of_lookup hl, rfl⟩, p, hP⟩

/-- The end of a call, with the worlds: both models leave it alike, the caller
going on in the world the callee ended in. -/
theorem leave_in {fr : Copy.State} {s : State × World} (hs : AgreesIn fr s)
    {bound : List (Name × Passed)} {frc : Copy.Frame} {sc : State} (hent : Entered s.1 bound frc sc)
    (hcompat : (bound.map Prod.snd).Pairwise Passed.Compat) {fr' : Copy.State}
    {s' : State × World} (hag : AgreesIn fr' s') (hev : Evolves sc s'.1) :
    ∃ fr'', Copy.memory.leave fr fr' bound = .ok fr'' ∧
      InPlace.memory.leave s s' bound = .ok (⟨s.1.env, s'.1.store⟩, s'.2) ∧
      AgreesIn fr'' (⟨s.1.env, s'.1.store⟩, s'.2) ∧ Evolves s.1 ⟨s.1.env, s'.1.store⟩ := by
  obtain ⟨fr'', hleave, hag'', hev''⟩ := leave_agrees hs.1 hent hcompat hag.1 hev
  refine ⟨(fr'', fr'.2), ?_, rfl, ⟨hag'', hag.2⟩, hev''⟩
  show (·, fr'.2) <$> Copy.frames.leave fr.1 fr'.1 bound = _
  rw [hleave]
  rfl

/-- The callee's outcome as its call's keeps the simulation: a value, a
raise, a `return`, a panic and a performance leave the call alike, and a
performance's rest leaves it alike when it ends. -/
theorem Corr.leaveCall {fr : Copy.State} {s : State × World} (hs : AgreesIn fr s)
    {bound : List (Name × Passed)} {frc : Copy.Frame} {sc : State} (hent : Entered s.1 bound frc sc)
    (hcompat : (bound.map Prod.snd).Pairwise Passed.Compat) {o : Outcome Copy.State Value}
    {o' : Outcome (State × World) Value} (h : Corr Value.Safe sc o o') :
    Corr Value.Safe s.1 (o.leaveCall Copy.memory bound fr) (o'.leaveCall InPlace.memory bound s) := by
  induction o generalizing o' with
  | performed op v frk k ih =>
    cases o' with
    | performed op' v' sk k' =>
      obtain ⟨⟨rfl, rfl, hv, hag, hev⟩, hk⟩ := h
      obtain ⟨_, h₁, h₂, hag'', hev''⟩ := leave_in hs hent hcompat hag hev
      simp only [Outcome.leaveCall, h₁, h₂]
      exact ⟨⟨rfl, rfl, hv, hag'', hev''⟩, fun w x w' x' hw => ih w x (hk w x w' x' hw)⟩
    | _ => exact absurd h id
  | done v fr' =>
    cases o' with
    | done v' s' =>
      obtain ⟨rfl, hv, hag, hev⟩ := h
      obtain ⟨_, h₁, h₂, hag'', hev''⟩ := leave_in hs hent hcompat hag hev
      simp only [Outcome.leaveCall, h₁, h₂]
      exact ⟨rfl, hv, hag'', hev''⟩
    | _ => exact absurd h id
  | raised e fr' =>
    cases o' with
    | raised e' s' =>
      obtain ⟨rfl, he, hag, hev⟩ := h
      obtain ⟨_, h₁, h₂, hag'', hev''⟩ := leave_in hs hent hcompat hag hev
      simp only [Outcome.leaveCall, h₁, h₂]
      exact ⟨rfl, he, hag'', hev''⟩
    | _ => exact absurd h id
  | jumped j fr' =>
    cases o' with
    | jumped j' s' =>
      obtain ⟨rfl, hj, hag, hev⟩ := h
      cases j with
      | ret v =>
        obtain ⟨_, h₁, h₂, hag'', hev''⟩ := leave_in hs hent hcompat hag hev
        simp only [Outcome.leaveCall, h₁, h₂]
        exact ⟨rfl, hj, hag'', hev''⟩
      | brk | cont => exact (trivial : Corr Value.Safe s.1 .stuck .stuck)
    | _ => exact absurd h id
  | panicked k fr' =>
    cases o' with
    | panicked k' s' =>
      obtain ⟨rfl, hag, hev⟩ := h
      obtain ⟨_, h₁, h₂, hag'', hev''⟩ := leave_in hs hent hcompat hag hev
      simp only [Outcome.leaveCall, h₁, h₂]
      exact ⟨rfl, hag'', hev''⟩
    | _ => exact absurd h id
  | outOfFuel =>
    cases o' <;> first | exact absurd h id | exact (trivial : Corr Value.Safe s.1 .outOfFuel .outOfFuel)
  | stuck => cases o' <;> first | exact absurd h id | exact (trivial : Corr Value.Safe s.1 .stuck .stuck)

namespace Sim

/-- A call of a safe function value keeps the simulation. -/
theorem invoke {captured : List (Name × Value)} (hc : ∀ xv ∈ captured, xv.2.Safe)
    {params : List Param} (hnd : (params.map Param.name).Nodup) {passed : List Passed}
    (hpassed : PassedSafe passed) (hcompat : passed.Pairwise Passed.Compat)
    {body : Eval Copy.State Value} {body' : Eval (State × World) Value}
    (hb : Sim Value.Safe body body') :
    Sim Value.Safe (Eval.invoke Copy.memory captured params passed body)
      (Eval.invoke InPlace.memory captured params passed body') := by
  intro fr s hs
  unfold Eval.invoke
  cases hbind : bindArgs params passed with
  | none => trivial
  | some bound =>
    obtain ⟨hnames, hsnd⟩ := bindArgs_spec hbind
    dsimp only
    rw [← hsnd] at hcompat hpassed
    rcases hs.1.enter hc (by rw [hnames]; exact hnd) hcompat hpassed with
      ⟨f, h₁, h₂⟩ | ⟨frc, sc, h₁, h₂, hent⟩
    · rw [Copy.memory, InPlace.memory, Frames.withWorld_enter, Frames.withWorld_enter, h₁, h₂,
        Frames.map_error, Frames.map_error]
      exact Corr.fault hs f
    · rw [Copy.memory, InPlace.memory, Frames.withWorld_enter, Frames.withWorld_enter, h₁, h₂,
        Frames.map_ok, Frames.map_ok]
      exact Corr.leaveCall hs hent hcompat (hb (frc, fr.2) (sc, s.2) ⟨hent.agrees, hs.2⟩)

/-- The functions of the declarations take distinct parameters and have safe
bodies. -/
def DeclsSafe (D : Decls) : Prop :=
  ∀ d ∈ D.fns, (d.params.map Param.name).Nodup ∧ d.body.exclusive [] = true ∧
    d.body.distinctParams = true

/-- Calling a safe value with the values of safe arguments, whose places don't
overlap, keeps the simulation. -/
theorem call {D : Decls} (hD : DeclsSafe D) {run : Expr → Eval Copy.State Value}
    {run' : Expr → Eval (State × World) Value} (h : SimRun run run') {f : Value} (hf : f.Safe)
    {passed : List Passed} (hpassed : PassedSafe passed)
    (hcompat : passed.Pairwise Passed.Compat) :
    Sim Value.Safe (Eval.call D Copy.memory run f passed)
      (Eval.call D InPlace.memory run' f passed) := by
  cases f with
  | closure captured params result ρ body =>
    cases hf with
    | closure hnd hex hdp hc =>
      exact invoke hc hnd hpassed hcompat (h body ⟨⟨[], hex⟩, hdp⟩)
  | function name types rows =>
    unfold Eval.call
    dsimp only
    cases hd : D.fn? name with
    | none => exact fail _
    | some d =>
      obtain ⟨hnd, hex, hdp⟩ := hD d (List.mem_of_find?_eq_some hd)
      refine invoke (captured := []) (by simp) hnd hpassed hcompat (h _ ⟨⟨[], ?_⟩, ?_⟩)
      · rw [Expr.exclusive_substRows, Expr.exclusive_substTys]
        exact hex
      · rw [Expr.distinctParams_substRows, Expr.distinctParams_substTys]
        exact hdp
  | _ => exact fail _

/-- A call as code or a `with` makes it keeps the simulation. -/
theorem callAs {D : Decls} (hD : DeclsSafe D) {run : Expr → Eval Copy.State Value}
    {run' : Expr → Eval (State × World) Value} (h : SimRun run run') (control : Bool) {f : Value} (hf : f.Safe)
    {passed : List Passed} (hpassed : PassedSafe passed)
    (hcompat : passed.Pairwise Passed.Compat) :
    Sim Value.Safe (Eval.callAs D Copy.memory run control f passed)
      (Eval.callAs D InPlace.memory run' control f passed) := by
  unfold Eval.callAs
  split
  · exact fail _
  · exact call hD h hf hpassed hcompat

end Sim

end Stilt.InPlace
