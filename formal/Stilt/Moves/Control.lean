import Stilt.Moves.Scopes

/-!
# Control

The steps of the evaluator that hold no last use of their own keep the
simulation: a `catch`, the arms of a `match`, a loop, an assignment, a
closure's capture, and the conversions of values.
-/

namespace Stilt.Moving

open InPlace

variable {α : Type} {G : α → Prop} {Lb L X : Live}

namespace MSim

/-- A `catch` runs its arm when its operand raises (effects.catch). -/
theorem handle {L₁ : Live} {m : Eval Copy.State α} {m' : Eval (State × World) α}
    {h : Value → Eval Copy.State α} {h' : Value → Eval (State × World) α} (hm : MSim G Lb L₁ X m m')
    (hh : ∀ e, VOk e → MSim G L₁ L X (h e) (h' e)) (hLb : L₁.Sub Lb) (hL : L.Sub L₁) :
    MSim G Lb L X (Eval.handle m h) (Eval.handle m' h') := by
  intro fr s mk hag hinv
  show MCorr G L X mk s.1 ((m fr).handle fun e fr' => h e fr') ((m' s).handle fun e s' => h' e s')
  have hp : ∀ fr₁ s₁, Post L₁ X mk s.1 fr₁ s₁ → Post L X mk s.1 fr₁ s₁ :=
    fun _ _ hp => hp.mono hL (Live.Sub.refl X)
  obtain ⟨-, hj, hpk, hP⟩ := MCorr.escapes (G := fun a _ => G a) (H := fun a _ => G a) hp
  refine Outcome.Rel.handle (hm fr s mk hag hinv) (fun _ _ _ _ hc => ⟨hc.1, hc.2.1, hp _ _ hc.2.2⟩)
    hj hpk hP ?_
  rintro e fr₁ e' s₁ ⟨rfl, he, m₁, hag₁, hk, henv, hev⟩
  have hinv₁ : Inv L₁ m₁ (keys s₁.1) := by
    rw [keys, henv]
    exact hinv.of_kills hLb hk
  exact (hh e he fr₁ s₁ m₁ hag₁ hinv₁).prefix hag.1 hk henv hev hL

/-- Binds the parts an arm's pattern matched, live for the arm's body (expressions.match). -/
theorem withVars {m : Eval Copy.State α} {m' : Eval (State × World) α} {Lb' L' X' : Live}
    (hm : MSim G Lb' L' X' m m') :
    ∀ (bindings : List (Name × Value)) (Lb L X : Live), (∀ xv ∈ bindings, VOk xv.2) →
      Lb'.Sub (Lb.union (Live.ofList (bindings.map Prod.fst))) →
      (L.eraseAll (bindings.map Prod.fst)).Sub L' → (X'.eraseAll (bindings.map Prod.fst)).Sub X →
      MSim G Lb L X (Eval.withVars Copy.memory bindings m) (Eval.withVars Moving.memory bindings m')
  | [], Lb, _, _, _, hLb, hL, hX => hm.mono (hLb.trans (by live_sub)) hL hX
  | (x, v) :: bindings, Lb, L, X, hv, hLb, hL, hX =>
    withVar x (hv (x, v) List.mem_cons_self)
      (withVars hm bindings (Lb.union (Live.one x)) (L.erase x)
        (X'.eraseAll (bindings.map Prod.fst)) (fun xv h => hv xv (List.mem_cons_of_mem _ h))
        (hLb.trans (by live_sub)) hL (Live.Sub.refl _))
      (fun z hz hzx => by simp_all) (fun z hz hzx => Live.mem_erase_of_ne hz hzx)
      (fun z hz => hX z (by
        simp only [Live.mem_erase_eq, Live.mem_eraseAll_eq, List.map_cons, List.contains_cons,
          Bool.and_eq_true, Bool.not_or, Bool.not_eq_true', bne_iff_ne, ne_eq,
          beq_eq_false_iff_ne] at hz ⊢
        grind))

theorem forEach {body : Value → Eval Copy.State Bool} {body' : Value → Eval (State × World) Bool}
    (h : ∀ v, VOk v → MSim (fun _ => True) Lb Lb X (body v) (body' v)) :
    ∀ vs : List Value, (∀ v ∈ vs, VOk v) →
      MSim (fun _ => True) Lb Lb X (Eval.forEach body vs) (Eval.forEach body' vs)
  | [], _ => pure trivial
  | v :: vs, hvs =>
    bind (h v (hvs v List.mem_cons_self))
      (fun g _ => ite g (forEach h vs fun u hu => hvs u (List.mem_cons_of_mem _ hu)) (pure trivial))
      (Live.Sub.refl _) (Live.Sub.refl _)

theorem asInt {v : Value} : MSim (fun _ => True) Lb L X (Eval.asInt v) (Eval.asInt v) := by
  cases v <;> first | exact pure trivial | exact fail _

theorem asBool {v : Value} : MSim (fun _ => True) Lb L X (Eval.asBool v) (Eval.asBool v) := by
  cases v <;> first | exact pure trivial | exact fail _

theorem asList {v : Value} (hv : VOk v) :
    MSim (fun vs : List Value => ∀ u ∈ vs, VOk u) Lb L X (Eval.asList v) (Eval.asList v) := by
  cases v <;> first | exact fail _ | skip
  obtain ⟨hs, hj⟩ := hv
  cases hs with
  | list h =>
    cases hj with
    | list h' => exact pure fun u hu => ⟨h u hu, h' u hu⟩

/-- A part of a value that a run may hold, as `e.f` and `e[i]` read it. -/
theorem get {v : Value} (hv : VOk v) (p : Path) :
    MSim VOk Lb L X (Eval.ofExcept (v.get p)) (Eval.ofExcept (v.get p)) :=
  ofExcept _ fun _ h => ⟨hv.1.get h, hv.2.get h⟩

/-- A loop runs its body with each element bound, from the value its iterable
had when it started (expressions.for-iterables; modes.change-while-iterating). -/
theorem loop {run : Expr → Eval Copy.State Value} {run' : Expr → Eval (State × World) Value}
    (x : Name)
    {e body : Expr} {Lc Lb' Lt X' : Live} (he : MSim VOk Lb Lc X (run e) (run' e))
    (hb : MSim VOk Lb' Lt X' (run body) (run' body))
    (hLb : ∀ z, Lb'.mem z = true → z ≠ x → Lc.mem z = true)
    (hLt : ∀ z, Lc.mem z = true → z ≠ x → Lt.mem z = true)
    (hX : (X'.erase x).Sub X) (hLc : Lc.Sub Lb) (hL : L.Sub Lc) :
    MSim VOk Lb L X (Eval.loop Copy.memory run x e body) (Eval.loop Moving.memory run' x e body) :=
  bind (bind he (fun _ hv => asList hv) hLc (Live.Sub.refl _)) (fun vs hvs =>
    bind (forEach (fun _ hv => withVar x hv (turn hb) hLb hLt hX) vs hvs)
      (fun _ _ => pure ⟨.unit, .unit⟩) (Live.Sub.refl _) hL) hLc hL

/-- Writing a live variable that the expression mentions (values.let-and-var and values.assignment-order). -/
theorem update (x : Name) (p : Path) {w : Value} (hw : VOk w) (hx : Lb.mem x = true)
    (hX : X.mem x = true) :
    MSim (fun _ => True) Lb L X (Eval.update fun fr => Copy.memory.write fr x p w)
      (Eval.update fun s => Moving.memory.write s x p w) := by
  intro fr s mk hag hinv
  have hlx : LiveAt x mk (names fr.1) := hag.1.keys_eq ▸ hinv.live x hx
  unfold Eval.update
  rcases hag.1.write hlx hw.1 hw.2 p with ⟨f, h₁, h₂⟩ | ⟨fr', s', h₁, h₂, hag', henv, r, hr, hev⟩
  · simp only [Copy.memory, Moving.memory, Frames.withWorld, Copy.frames, Moving.frames, h₁, h₂]
    exact MCorr.fault hag f
  · simp only [Copy.memory, Moving.memory, Frames.withWorld, Copy.frames, Moving.frames, h₁, h₂]
    refine ⟨rfl, trivial, mk, ⟨hag', hag.2⟩, Kills.refl L X mk _ (by simp [hag.1.len_env]), henv,
      ?_⟩
    refine Evolves.of_sub (fun e he => ?_) hev
    rw [List.mem_singleton.1 he]
    exact mem_sel_of_lookup hag.1.len_env (hag.1.liveAt_env hlx) hr hX

/-- A closure literal captures the newest binding of each variable that `keep`
holds, each live when the expression mentions it (expressions.capture). -/
theorem capture {keep : Name → Bool} (hk : ∀ x, keep x = true → Lb.mem x = true) :
    MSim (fun captured : List (Name × Value) => ∀ xv ∈ captured, VOk xv.2) Lb L X
      (Eval.inspect (Copy.memory.capture · keep)) (Eval.inspect (Moving.memory.capture · keep)) :=
  inspect fun _ _ _ hag hinv => by
    obtain ⟨h₁, h₂⟩ := hag.1.capture fun x hx => hag.1.keys_eq ▸ hinv.live x (hk x hx)
    exact ⟨h₁.symm, fun _ ha => by cases ha; exact h₂⟩

end MSim

end Stilt.Moving
