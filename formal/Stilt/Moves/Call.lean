import Stilt.Moves.Invoke
import Stilt.Moves.Instantiation
import Stilt.InPlace.Instances

/-!
# Calls keep the simulation

`invoke_step` runs a call of a body whose marks are last uses, from a caller
`Ready` for it; `call_step` calls a function value, a closure or a declared
function with its row variables instantiated (effects.inference).
-/

namespace Stilt.Moving

open InPlace

/-- The functions of the declarations take distinct parameters and have safe
bodies whose marks are last uses. -/
def DeclsOk (D : Decls) : Prop :=
  ∀ d ∈ D.fns, (d.params.map Param.name).Nodup ∧ d.body.exclusive [] = true ∧
    d.body.distinctParams = true ∧ d.body.movesOk (inoutLive d.params) = true

/-- What a call needs of its caller, on the arguments it passes. -/
structure ReadyP (L X : Live) (m : List Bool) (fr : Copy.State) (s : State × World)
    (passed : List Passed) : Prop where
  agrees : MAgreesIn m fr s
  places : ∀ x p, Passed.place x p ∈ passed → LiveAt x m (names fr.1) ∧ X.mem x = true
  moved : ∀ x v, Passed.moved x v ∈ passed →
    LiveAt x m (names fr.1) ∧ fr.1.lookup x = some v ∧ X.mem x = true ∧ L.mem x = false
  compat : (passed.map Passed.handOver).Pairwise Passed.Compat
  nodup : (movedOf passed).Nodup
  passed : PassedOk passed

variable {L X : Live} {m : List Bool} {fr : Copy.State} {s : State × World}

theorem ReadyP.ready {passed : List Passed} (h : ReadyP L X m fr s passed)
    {bound : List (Name × Passed)} (hb : bound.map Prod.snd = passed) :
    Ready L X m fr.1 s.1 bound := by
  have hmap : (bound.map Moving.handOver).map Prod.snd = passed.map Passed.handOver := by
    rw [← hb, List.map_map, List.map_map]
    exact List.map_congr_left fun ya _ => by
      obtain ⟨y, q⟩ := ya
      simp only [Function.comp_apply, handOver_eq]
  refine ⟨h.agrees.1, fun y x p hm => h.places x p ?_, fun y x v hm => h.moved x v ?_,
    hmap ▸ h.compat,
    hb ▸ h.nodup, hb ▸ h.passed⟩ <;> exact hb ▸ List.mem_map_of_mem hm

theorem fst_handOver (ya : Name × Passed) : (Moving.handOver ya).1 = ya.1 := by
  obtain ⟨y, q⟩ := ya
  rw [handOver_eq]

/-- The callee ends, and the caller gets the write-back and its store, in the
world the callee ended in. -/
theorem Ready.finish {fr : Copy.Frame} {s : State} {params : List Param}
    {bound : List (Name × Passed)} (hr : Ready L X m fr s bound) {frc : Copy.Frame} {sc : State}
    (hent : Entered ⟨keep m s.env, s.store⟩ (bound.map Moving.handOver) frc sc)
    (hinout : ∀ y x p, (y, Passed.place x p) ∈ bound → (inoutLive params).mem y = true) {Xb : Live}
    {fr' : Copy.State} {s' : State × World}
    (hp : Post (inoutLive params) Xb (List.replicate frc.length true) sc fr' s') :
    ∃ fr₂, Copy.frames.leave fr fr'.1 bound = .ok fr₂ ∧
      Post L X m s (fr₂, fr'.2) (⟨s.env, s'.1.store⟩, s'.2) := by
  obtain ⟨mc, ⟨hagc, hw, hx⟩, hkc, henvc, hevc⟩ := hp
  have hev : Evolves sc s'.1 := by
    have h₁ := Evolves.of_sub (e' := sc.env)
      (fun e he => (sublist_keep _ _).subset (sel_mem he).1) hevc
    have hs' : s'.1 = ⟨sc.env, s'.1.store⟩ := by rw [← henvc]
    rw [hs']
    exact h₁
  obtain ⟨fr₂, hfr, hpost⟩ := hr.post hent hev fun y x p hm => by
    have hl : LiveAt y mc (names fr'.1) := by
      rw [hagc.keys_eq, keys, henvc]
      exact (LiveAt.of_all (fun b hb => List.eq_of_mem_replicate hb)).of_kills
        (.inl (hinout y x p hm)) hkc
    exact ⟨hagc.read hl [], fun v hv => hagc.read_ok hl hv⟩
  refine ⟨fr₂, hfr, ?_⟩
  rw [hw]
  exact hpost s'.2 (hw ▸ hx)

theorem copy_leave_in {fr fr' : Copy.State} {bound : List (Name × Passed)} {fr₂ : Copy.Frame}
    (h : Copy.frames.leave fr.1 fr'.1 bound = .ok fr₂) :
    Copy.memory.leave fr fr' bound = .ok (fr₂, fr'.2) := by
  show (·, fr'.2) <$> Copy.frames.leave fr.1 fr'.1 bound = _
  rw [h]
  rfl

theorem moving_leave (s s' : State × World) (bound : List (Name × Passed)) :
    Moving.memory.leave s s' bound = .ok (⟨s.1.env, s'.1.store⟩, s'.2) := rfl

/-- The callee's outcome as its call's keeps the simulation: a value, a raise,
a `return`, a panic and a performance leave the call alike, and a performance's
rest leaves it alike when it ends. -/
theorem MCorr.leaveCall {params : List Param} {bound : List (Name × Passed)}
    (hr : Ready L X m fr.1 s.1 bound) {frc : Copy.Frame} {sc : State}
    (hent : Entered ⟨keep m s.1.env, s.1.store⟩ (bound.map Moving.handOver) frc sc)
    (hinout : ∀ y x p, (y, Passed.place x p) ∈ bound → (inoutLive params).mem y = true) {Xb : Live}
    {o : Outcome Copy.State Value} {o' : Outcome (State × World) Value}
    (h : MCorr VOk (inoutLive params) Xb (List.replicate frc.length true) sc o o') :
    MCorr VOk L X m s.1 (o.leaveCall Copy.memory bound fr)
      (o'.leaveCall Moving.memory bound s) := by
  induction o generalizing o' with
  | performed op v frk k ih =>
    cases o' with
    | performed op' v' sk k' =>
      obtain ⟨⟨rfl, rfl, hv, hp⟩, hk⟩ := h
      obtain ⟨fr₂, hl, hpost⟩ := hr.finish hent hinout hp
      simp only [Outcome.leaveCall, copy_leave_in hl, moving_leave]
      exact ⟨⟨rfl, rfl, hv, hpost⟩, fun w x w' x' hw => ih w x (hk w x w' x' hw)⟩
    | _ => exact absurd h id
  | done v fr' =>
    cases o' with
    | done v' s' =>
      obtain ⟨rfl, hv, hp⟩ := h
      obtain ⟨fr₂, hl, hpost⟩ := hr.finish hent hinout hp
      simp only [Outcome.leaveCall, copy_leave_in hl, moving_leave]
      exact ⟨rfl, hv, hpost⟩
    | _ => exact absurd h id
  | raised e fr' =>
    cases o' with
    | raised e' s' =>
      obtain ⟨rfl, he, hp⟩ := h
      obtain ⟨fr₂, hl, hpost⟩ := hr.finish hent hinout hp
      simp only [Outcome.leaveCall, copy_leave_in hl, moving_leave]
      exact ⟨rfl, he, hpost⟩
    | _ => exact absurd h id
  | jumped j fr' =>
    cases o' with
    | jumped j' s' =>
      obtain ⟨rfl, hj, hp⟩ := h
      cases j with
      | ret v =>
        obtain ⟨fr₂, hl, hpost⟩ := hr.finish hent hinout hp
        simp only [Outcome.leaveCall, copy_leave_in hl, moving_leave]
        exact ⟨rfl, hj, hpost⟩
      | brk | cont => exact (trivial : MCorr VOk L X m s.1 .stuck .stuck)
    | _ => exact absurd h id
  | panicked k fr' =>
    cases o' with
    | panicked k' s' =>
      obtain ⟨rfl, hp⟩ := h
      obtain ⟨fr₂, hl, hpost⟩ := hr.finish hent hinout hp
      simp only [Outcome.leaveCall, copy_leave_in hl, moving_leave]
      exact ⟨rfl, hpost⟩
    | _ => exact absurd h id
  | outOfFuel =>
    cases o' <;> first
      | exact absurd h id
      | exact (trivial : MCorr VOk L X m s.1 .outOfFuel .outOfFuel)
  | stuck =>
    cases o' <;> first | exact absurd h id | exact (trivial : MCorr VOk L X m s.1 .stuck .stuck)

/-- A call of a body whose marks are last uses keeps the simulation. -/
theorem invoke_step {captured : List (Name × Value)} (hc : ∀ xv ∈ captured, VOk xv.2)
    {params : List Param} (hnd : (params.map Param.name).Nodup) {passed : List Passed}
    {body : Eval Copy.State Value} {body' : Eval (State × World) Value} {Lb' X' : Live}
    (hb : MSim VOk Lb' (inoutLive params) X' body body') (hr : ReadyP L X m fr s passed) :
    MCorr VOk L X m s.1 (Eval.invoke Copy.memory captured params passed body fr)
      (Eval.invoke Moving.memory captured params passed body' s) := by
  unfold Eval.invoke
  cases hbind : bindArgs params passed with
  | none => trivial
  | some bound =>
    obtain ⟨hnames, hsnd⟩ := bindArgs_spec hbind
    have hr' := hr.ready hsnd
    have hag := hr'.agrees
    dsimp only
    have hpv : ∀ q ∈ (bound.map Moving.handOver).map Prod.snd, ∀ v, q.value? = some v → VOk v := by
      intro q hq v hv
      obtain ⟨ya, hya, rfl⟩ := List.mem_map.1 hq
      obtain ⟨ya', hya', rfl⟩ := List.mem_map.1 hya
      obtain ⟨y, q'⟩ := ya'
      rw [handOver_eq] at hv
      exact hr'.passed q' (List.mem_map_of_mem hya') v (value?_handOver hv)
    rw [Copy.memory, Moving.memory, Frames.withWorld_enter, Frames.withWorld_enter,
      copy_enter_view hag captured (fun y x p hm => (hr'.places y x p hm).1)
        (fun y x v hm => ⟨(hr'.moved y x v hm).1, (hr'.moved y x v hm).2.1⟩),
      show Moving.frames.enter s.1 captured bound =
        InPlace.frames.enter s.1 captured (bound.map Moving.handOver) from rfl,
      inPlace_enter_view hag captured (fun y x p hm => (hr'.places' y x p hm).1)]
    rcases hag.agrees.enter (fun xv h => (hc xv h).1)
        (by rw [List.map_map, show Prod.fst ∘ Moving.handOver = Prod.fst from funext fst_handOver,
          hnames]; exact hnd) hr'.compat (fun q hq v hv => (hpv q hq v hv).1) with
      ⟨f, h₁, h₂⟩ | ⟨frc, sc, h₁, h₂, hent⟩
    · rw [h₁, h₂, Frames.map_error, Frames.map_error]
      exact MCorr.fault hr.agrees f
    · rw [h₁, h₂, Frames.map_ok, Frames.map_ok]
      dsimp only
      have hagc := MAgrees.callee hent.agrees
        (enter_just (fun xv h => (hc xv h).2) hag.just (fun q hq v hv => (hpv q hq v hv).2) h₁)
      have hinout := bindArgs_inout hbind
      exact MCorr.leaveCall hr' hent hinout
        (hb (frc, fr.2) (sc, s.2) _ ⟨hagc, hr.agrees.2⟩
          (Inv.of_all fun b hb => List.eq_of_mem_replicate hb))

end Stilt.Moving
