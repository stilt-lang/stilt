import Stilt.Moves.Call
import Stilt.Moves.Pass

/-!
# Calls and bindings in the simulation

The two cases of the simulation where a last use hands storage over: a call,
whose arguments may be last uses, and `let` or `var`, whose initializer may be
one (values.passing-values).
-/

namespace Stilt.Moving

open InPlace

variable {L X : Live} {run : Expr → Eval Copy.State Value}
  {run' : Expr → Eval (State × World) Value}

/-- Calling a function value that a run may hold keeps the simulation. -/
theorem call_step {D : Decls} (hD : DeclsOk D) (h : MRun run run') {f : Value} (hf : VOk f)
    {passed : List Passed} {m : List Bool} {fr : Copy.State} {s : State × World}
    (hr : ReadyP L X m fr s passed) :
    MCorr VOk L X m s.1 (Eval.call D Copy.memory run f passed fr)
      (Eval.call D Moving.memory run' f passed s) := by
  obtain ⟨hs, hj⟩ := hf
  cases f with
  | closure captured params result ρ body =>
    cases hs with
    | closure hnd hex hdp hc =>
      cases hj with
      | closure hmv hcj =>
        exact invoke_step (fun xv hxv => ⟨hc xv hxv, hcj xv hxv⟩) hnd
          (h body _ ⟨⟨[], hex⟩, hdp⟩ hmv) hr
  | function name types rows =>
    unfold Eval.call
    dsimp only
    cases hd : D.fn? name with
    | none => exact (trivial : MCorr VOk L X m s.1 .stuck .stuck)
    | some d =>
      obtain ⟨hnd, hex, hdp, hmv⟩ := hD d (List.mem_of_find?_eq_some hd)
      refine invoke_step (captured := []) (by simp) hnd (h _ _ ⟨⟨[], ?_⟩, ?_⟩ ?_) hr
      · rw [Expr.exclusive_substRows, Expr.exclusive_substTys]; exact hex
      · rw [Expr.distinctParams_substRows, Expr.distinctParams_substTys]; exact hdp
      · rw [Expr.movesOk_substRows, Expr.movesOk_substTys]; exact hmv
  | _ => exact (trivial : MCorr VOk L X m s.1 .stuck .stuck)

/-- A call as code or a `with` makes it keeps the simulation. -/
theorem callAs_step {D : Decls} (hD : DeclsOk D) (h : MRun run run') (control : Bool) {f : Value}
    (hf : VOk f) {passed : List Passed} {m : List Bool} {fr : Copy.State} {s : State × World}
    (hr : ReadyP L X m fr s passed) :
    MCorr VOk L X m s.1 (Eval.callAs D Copy.memory run control f passed fr)
      (Eval.callAs D Moving.memory run' control f passed s) := by
  unfold Eval.callAs
  split
  · exact (trivial : MCorr VOk L X m s.1 .stuck .stuck)
  · exact call_step hD h hf hr

/-- Arguments evaluated, then the call made from where they leave. -/
theorem MSim.bind_args {G : List Passed → Prop} {H : Value → Prop} {Lb L₁ : Live}
    {m₀ : Eval Copy.State (List Passed)} {m₀' : Eval (State × World) (List Passed)}
    {f : List Passed → Eval Copy.State Value} {f' : List Passed → Eval (State × World) Value}
    (hm : ASim G Lb L₁ X m₀ m₀')
    (hf : ∀ ps fr s mk, G ps → MovedHeld ps fr.1 → MAgreesIn mk fr s → Inv L₁ mk (keys s.1) →
      MCorr H L X mk s.1 (f ps fr) (f' ps s)) (hLb : L₁.Sub Lb) (hL : L.Sub L₁) :
    MSim H Lb L X (m₀ >>= f) (m₀' >>= f') := by
  intro fr s mk hag hinv
  show MCorr H L X mk s.1 ((m₀ fr).bind fun a fr' => f a fr') ((m₀' s).bind fun a s' => f' a s')
  refine Outcome.Rel.bind (hm fr s mk hag hinv)
    (MCorr.escapes fun _ _ hp => hp.mono hL (Live.Sub.refl X)) ?_
  rintro a fr₁ a' s₁ ⟨rfl, ⟨hG, hheld⟩, m₁, hag₁, hk, henv, hev⟩
  have hinv₁ : Inv L₁ m₁ (keys s₁.1) := by
    rw [keys, henv]
    exact hinv.of_kills hLb hk
  exact (hf a fr₁ s₁ m₁ hG hheld hag₁ hinv₁).prefix hag.1 hk henv hev hL

theorem inoutRoots_sub : ∀ (as : List Arg) (x : Name), x ∈ inoutRoots as → (argsMentions as).mem x = true
  | [], _, h => by simp [inoutRoots] at h
  | .value e :: as, x, h => by
    have := inoutRoots_sub as x h
    simp [argsMentions, this]
  | .inout ⟨y, ps⟩ :: as, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [argsMentions]
    · have := inoutRoots_sub as x h
      simp [argsMentions, this]

/-- A caller is ready for a call once its arguments are evaluated. -/
theorem readyP {as : List Arg} {ps : List Passed} {fr : Copy.State} {s : State × World}
    {mk : List Bool} (hok : ArgsOk as ps) (hheld : MovedHeld ps fr.1) (hag : MAgreesIn mk fr s)
    (hinv : Inv ((L.union (Live.ofList (inoutRoots as))).union (Live.ofList (movedRoots as))) mk
      (keys s.1))
    (hmv : argsMovesOk (L.union (Live.ofList (inoutRoots as))) as = true)
    (hcompat : ps.Pairwise Passed.Compat) (hX : (argsMentions as).Sub X) :
    ReadyP L X mk fr s ps := by
  obtain ⟨hnd, hB⟩ := moved_distinct hmv
  have hmo : ∀ x v, Passed.moved x v ∈ ps → x ∈ movedRoots as := fun x v hm => by
    rw [← hok.2.2]
    exact List.mem_filterMap.2 ⟨_, hm, rfl⟩
  have hpl : ∀ z p, Passed.place z p ∈ ps → z ∈ inoutRoots as := fun z p hm => place_roots hok.2.1 hm
  refine ⟨hag, fun x p hm => ⟨hag.1.keys_eq ▸ hinv.live x ?_,
      hX x (inoutRoots_sub as x (hpl x p hm))⟩,
    fun x v hm => ⟨hag.1.keys_eq ▸ hinv.live x ?_, hheld x v hm, hX x (movedRoots_sub as x (hmo x v hm)),
      ?_⟩, compat_handOver hcompat (hok.2.2 ▸ hnd) fun x hx z p hz => ?_, hok.2.2 ▸ hnd, hok.1⟩
  · simp [hpl x p hm]
  · simp [hmo x v hm]
  · have := hB x (hmo x v hm)
    simp only [Live.mem_union, Bool.or_eq_false_iff] at this
    exact this.1
  · rintro rfl
    have h₁ := hB x (hok.2.2 ▸ hx)
    have h₂ := hpl x p hz
    simp only [Live.mem_union, Bool.or_eq_false_iff] at h₁
    rw [show (Live.ofList (inoutRoots as)).mem x = true from (Live.mem_ofList _ _).2 h₂] at h₁
    exact absurd h₁.2 (by simp)

end Stilt.Moving
