import Stilt.Quiet.Cases

/-!
# Matches, loops, `when` and `with` keep the world's output and input

A `match` runs its arms, a loop its body's turns, a `when` its block between taking its cells
and putting their values back, and a `with` its block and its handler's clauses, whose rows
fit within the row around the `with` (handlers.handler-literals): each keeps the world when
what it runs does.
-/

namespace Stilt

section

variable {D : Decls} {η : REnv} {X : Exits} {α : Type}

/-- The names of a `when`, bound to values of their types, the first one outermost, keep the
world when the block does. -/
theorem Eval.KeepsIo.withHeld {m : Eval Copy.State α} :
    ∀ {Γ : Ctx} {ns : List (Name × Ty)} {vs : List Value}, ValuesAt D η vs (ns.map Prod.snd) →
      Eval.KeepsIo D (Γ.holding ns) η X m →
        Eval.KeepsIo D Γ η X (Eval.withVars Copy.memory ((ns.map Prod.fst).zip vs) m)
  | _, [], _, h, hm => by cases h; exact hm
  | Γ, p :: _, _ :: _, .cons hv hvs, hm =>
    Eval.KeepsIo.withVar (b := ⟨p.2, true⟩) hv
      (Eval.KeepsIo.withHeld (Γ := Γ.bind p.1 ⟨p.2, true⟩) hvs hm)
  | _, _ :: _, [], h, _ => nomatch h

end

section

variable {D : Decls} {n : Nat} (hq : Quiet D n) (hs : Sound D n) {scope : RowScope} {η : REnv}
  (hη : η.Respects scope) (θ : RowSubst) {Γ : Ctx} {fx : Effects}
  (hio : STy.io ∉ fx.row.close η)
include hq hs hη hio

theorem match_keeps (hD : D.WellFormed) {e : Expr} {σ τ : Ty} {arms : List Arm}
    (he : HasType D scope Γ fx e σ) (ha' : ArmsFit D scope Γ fx arms σ τ) :
    Eval.KeepsIo D Γ η (fx.exits D η)
      (eval D Copy.memory (n + 1) ((Expr.match e τ arms).substRows θ)) := by
  refine Eval.KeepsIo.bind (hs he hη θ) (hq he hη hio θ) fun v hv => ?_
  show Eval.KeepsIo D Γ η _ (Eval.select Copy.memory (eval D Copy.memory n) (substArmRows θ arms) v)
  rw [substArmRows_eq_map]
  refine Eval.select_of (Eval.KeepsIo D Γ η (fx.exits D η)) (.inl Eval.KeepsIo.fail)
    (.inl Eval.KeepsIo.fail) ?_ ?_
  · intro a ha _ us hm _
    obtain ⟨arm, hmem, rfl⟩ := List.mem_map.1 ha
    obtain ⟨σs, ρ, hp, hbs, -, hb, -⟩ := ha'.mem hmem
    exact Eval.KeepsIo.withVars (by rw [hbs, hp.length]) (hp.bound hD hv hm) (hq hb hη hio θ)
  · intro a ha g hga us hus _ m hm
    obtain ⟨arm, hmem, rfl⟩ := List.mem_map.1 ha
    obtain ⟨σs, ρ, hp, hbs, hgt, hb, -⟩ := ha'.mem hmem
    obtain ⟨q, hq', hqm⟩ := Pattern.mem_ways hus
    obtain ⟨hqp, -⟩ := hp.alternative q hq'
    have hlen : arm.binders.length = σs.length := by rw [hbs, hp.length]
    have hut := hqp.bound hD hv hqm
    cases harm : arm.guard with
    | none => simp [harm, substGuardRows] at hga
    | some g₀ =>
      rw [harm] at hgt hga
      cases hgt with
      | some hgt hfg =>
        simp only [substGuardRows, Option.some.injEq] at hga
        subst hga
        refine Eval.KeepsIo.bind (P := fun _ => True)
          (Eval.Ok.withVars hlen hut (Eval.Ok.bind (hs hgt hη θ) fun w hw => ?_))
          (Eval.KeepsIo.withVars hlen hut
            (Eval.KeepsIo.bindAny (hq hgt hη hio θ) fun _ _ => Outcome.KeepsIo.asBool)) fun k _ => ?_
        · obtain ⟨k, rfl⟩ := (hw.fits (hfg.close η)).bool_inv
          exact Eval.Ok.pure trivial
        · cases k
          · exact hm
          · exact Eval.KeepsIo.withVars hlen hut (hq hb hη hio θ)

theorem for_keeps {x : Name} {τ : Ty} {e body : Expr} {σ : Ty}
    (he : HasType D scope Γ fx e (.list τ)) (hb : HasType D scope (Γ.bind x ⟨τ, false⟩) fx.inLoop body σ) :
    Eval.KeepsIo D Γ η (fx.exits D η)
      (eval D Copy.memory (n + 1) ((Expr.for x τ e body).substRows θ)) := by
  refine Eval.KeepsIo.bind (P := fun vs => ∀ u ∈ vs, Value.Typed D u (τ.close η))
    (Eval.Ok.bind (hs he hη θ) fun v hv => ?_)
    (Eval.KeepsIo.bindAny (hq he hη hio θ) fun _ _ => Outcome.KeepsIo.asList) fun vs hvs => ?_
  · obtain ⟨vs, rfl, hvs⟩ := hv.list_inv
    exact Eval.Ok.pure hvs
  · refine Eval.KeepsIo.bindAny (Eval.KeepsIo.forEach (fun u hu => ?_) (fun u hu => ?_) hvs)
      fun _ _ => rfl
    · exact (Eval.Ok.withVar (b := ⟨τ, false⟩) hu
        ((hs hb hη θ).turn (X' := fx.exits D η) (fun _ F hF he => ⟨F, hF, he⟩) fun _ h => h)).mono
          (fun _ _ => trivial) (fun _ F hF he => ⟨F, hF, he⟩) fun _ h => h
    · exact Eval.KeepsIo.withVar (b := ⟨τ, false⟩) hu ((hq hb hη hio θ).turn.mono)

theorem while_keeps {c body : Expr} {σc σ : Ty} (hc : HasType D scope Γ fx c σc)
    (hfc : Fits σc .bool) (hb : HasType D scope Γ fx.inLoop body σ) (hfb : Fits σ .unit) :
    Eval.KeepsIo D Γ η (fx.exits D η)
      (eval D Copy.memory (n + 1) ((Expr.while c body).substRows θ)) := by
  have hl := hq (.while hc hfc hb hfb) hη hio θ
  refine Eval.KeepsIo.bind (P := fun _ => True) (Eval.Ok.bind (hs hc hη θ) fun v hv => ?_)
    (Eval.KeepsIo.bindAny (hq hc hη hio θ) fun _ _ => Outcome.KeepsIo.asBool) fun k _ => ?_
  · obtain ⟨k, rfl⟩ := (hv.fits (hfc.close η)).bool_inv
    exact Eval.Ok.pure trivial
  · cases k
    · exact Eval.KeepsIo.pure
    · refine Eval.KeepsIo.bind ((hs hb hη θ).turn (X' := fx.exits D η)
        (fun _ F hF he => ⟨F, hF, he⟩) fun _ h => h) (hq hb hη hio θ).turn.mono fun g _ => ?_
      cases g
      · exact Eval.KeepsIo.pure
      · exact hl

omit hs in
theorem loop_keeps {body : Expr} {σ σ' : Ty} {fx' : Effects} {P : Bool → Prop}
    (hrow : fx'.row = fx.row)
    (hperf : (fx'.exits D η).Performs (fx.exits D η)) (hl : HasType D scope Γ fx (.loop body) σ)
    (hb : HasType D scope Γ fx' body σ') (hok : Eval.Ok D Γ η (fx.exits D η) P
      (Eval.turn (eval D Copy.memory n (body.substRows θ)))) :
    Eval.KeepsIo D Γ η (fx.exits D η) (eval D Copy.memory (n + 1) ((Expr.loop body).substRows θ)) :=
  Eval.KeepsIo.bind hok ((hq hb hη (hrow ▸ hio) θ).turn.mono hperf) fun g _ => by
    cases g
    · exact Eval.KeepsIo.pure
    · exact hq hl hη hio θ

theorem held_keeps {ns : List (Name × Ty)} {es : List Expr} {body : Expr} {σ : Ty}
    (hes : ExprsFit D scope Γ fx es (ns.map fun p => .shared p.2))
    (hb : HasType D scope (Γ.holding ns) fx body σ) :
    Eval.KeepsIo D Γ η (fx.exits D η)
      (eval D Copy.memory (n + 1) ((Expr.held ns es body).substRows θ)) := by
  have hnames : (ns.map fun p => (p.1, p.2.substRows θ)).map Prod.fst = ns.map Prod.fst := by
    simp [Function.comp_def]
  show Eval.KeepsIo D Γ η _ (Eval.bind (Eval.list (eval D Copy.memory n) (substExprRows θ es)) fun vs =>
    Eval.held Copy.memory (eval D Copy.memory n (body.substRows θ))
      ((ns.map fun p => (p.1, p.2.substRows θ)).map Prod.fst) vs)
  rw [hnames]
  refine Eval.KeepsIo.bind (ExprsFit.ok hs hη θ hes) (ExprsFit.keeps hq hs hη θ hes hio) fun vs hvs => ?_
  obtain ⟨cells, hcells, hr⟩ := hvs.cells
  unfold Eval.held
  rw [hcells]
  refine Eval.KeepsIo.bind (Eval.Ok.ofExcept (P := (· = cells)) (.inl ⟨cells, rfl, rfl⟩))
    Eval.KeepsIo.ofExcept fun c hc => ?_
  subst hc
  refine Eval.KeepsIo.bind (P := fun vs => ValuesAt D η vs (ns.map Prod.snd))
    (Eval.Ok.bind (Q := fun vs => ValuesAt D η vs (ns.map Prod.snd)) (Eval.Ok.worldWith
    (P := fun v => ∃ vs', v = .list vs' ∧ ValuesAt D η vs' (ns.map Prod.snd)) fun x hx => ?_)
      fun v hv => ?_)
    (Eval.KeepsIo.bindAny (fun γ _ => Outcome.KeepsIo.world (fun x v x' h => ?_) γ)
      fun _ _ => Outcome.KeepsIo.asList) fun vs' hvs' => ?_
  · rcases hx.take hr with ⟨vs', w', h, hvs', hw'⟩ | h
    · exact .inl ⟨_, _, by rw [h]; rfl, ⟨vs', rfl, hvs'⟩, hw'⟩
    · exact .inr ⟨.deadlock, by rw [h]; rfl⟩
  · obtain ⟨vs', rfl, hvs'⟩ := hv
    exact Eval.Ok.pure (P := fun vs => ValuesAt D η vs (ns.map Prod.snd)) hvs'
  · cases ht : World.take c x with
    | error => rw [ht] at h; cases h
    | ok p =>
      rw [ht] at h
      cases h
      exact World.take_io ht
  · have hlen : (ns.map Prod.fst).length = vs'.length := by
      rw [hvs'.length, List.length_map, List.length_map]
    simp only [hlen, ↓reduceIte]
    exact Eval.KeepsIo.withHeld hvs' fun s hs' => ((hq hb hη hio θ) s hs').release

end

end Stilt
