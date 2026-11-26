import Stilt.WellTyped

/-!
# Checks that decide the side conditions of typing

Lemmas that turn the side conditions of typing into Boolean checks, which
`decide` evaluates on the closed programs of the counterexamples, and what
typing knows of a function named as a value.
-/

namespace Stilt.Counterexamples

theorem viewsViewable_of_check {τ : Ty} (h : τ.views.all Ty.viewable = true) :
    τ.ViewsViewable := by
  intro υ hυ
  have := List.all_eq_true.1 h υ hυ
  cases υ <;> simp_all [Ty.viewable]

theorem wellFormed_of_check {τ : Ty} {s : RowScope}
    (h : ((τ.rows.all fun ρ => ρ.vars.all (· ∈ s.vars)) && τ.concreteCheck &&
      τ.views.all Ty.viewable) = true) :
    τ.WellFormed s := by
  simp only [Bool.and_eq_true] at h
  have hc := Ty.concrete_of_check h.1.2
  refine ⟨fun ρ hρ v hv => ?_, fun T hT => ?_, hc.2, viewsViewable_of_check h.2⟩
  · simpa using List.all_eq_true.1 (List.all_eq_true.1 h.1.1 ρ hρ) v hv
  · rw [hc.1] at hT
    exact nomatch hT

theorem instantiable_of_check {τ : Ty} {s : RowSubst}
    (h : (τ.rows.all fun ρ => decide ((ρ.labels s).length ≤ 1) &&
      ρ.vars.all fun v => (s.lookup v).all (·.resume.isNone)) = true) :
    τ.InstantiableBy s := by
  intro ρ hρ
  have := List.all_eq_true.1 h ρ hρ
  rw [Bool.and_eq_true] at this
  have hres := this.2
  replace this := this.1
  refine ⟨fun E hE F hF => ?_, fun v hv σ hσ => ?_⟩
  rotate_left
  · have := List.all_eq_true.1 hres v hv
    rw [hσ] at this
    simpa using this
  match hl : ρ.labels s with
  | [] => simp [hl] at hE
  | [_] =>
    simp only [hl, List.mem_singleton] at hE hF
    rw [hE, hF]
  | _ :: _ :: _ => simp [hl] at this

/-- A function with no type parameters whose signature is concrete, and
whose rows name only its row variables. -/
def signatureCheck (d : FnDecl) : Bool :=
  d.typeParams.isEmpty && (d.type.rows.all fun ρ => ρ.vars.all (· ∈ d.rowParams)) &&
    d.type.concreteCheck && d.type.views.all Ty.viewable && d.type.rows.all (·.effects.isEmpty)

private theorem signatures_of_check {D : Decls} (h : D.fns.all signatureCheck = true) :
    ∀ d ∈ D.fns, d.typeParams = [] ∧ d.type.WellFormed d.scope := by
  intro d hd
  have h := List.all_eq_true.1 h d hd
  simp only [signatureCheck, Bool.and_eq_true, List.isEmpty_iff] at h
  exact ⟨h.1.1.1.1, wellFormed_of_check (by simp only [Bool.and_eq_true]; exact ⟨⟨h.1.1.1.2, h.1.1.2⟩, h.1.2⟩)⟩

private theorem effectsIn_of_check {D : Decls} {τ : Ty} (h : τ.rows.all (·.effects.isEmpty) = true) :
    τ.EffectsIn D := by
  intro ρ hρ E hE
  have := List.all_eq_true.1 h ρ hρ
  simp only [List.isEmpty_iff] at this
  rw [this] at hE
  exact nomatch hE

private theorem signatureEffects_of_check {D : Decls} (h : D.fns.all signatureCheck = true) :
    ∀ d ∈ D.fns, d.type.EffectsIn D := by
  intro d hd
  have h := List.all_eq_true.1 h d hd
  simp only [signatureCheck, Bool.and_eq_true] at h
  exact effectsIn_of_check h.2

private theorem vars_nil_of_lookup {ks : List Name} {rows : List Row} {v : Name} {ρ : Row}
    (h : (rows.all fun ρ => ρ.vars.isEmpty) = true) (hl : (ks.zip rows).lookup v = some ρ) :
    ρ.vars = [] := by
  induction ks generalizing rows with
  | nil => exact nomatch hl
  | cons k ks ih =>
    cases rows with
    | nil => exact nomatch hl
    | cons σ rows =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      simp only [List.zip_cons_cons, List.lookup] at hl
      split at hl
      · cases hl
        simpa using h.1
      · exact ih h.2 hl

/-- A use that gives no row variable a row holding another passes nothing on
(effects.passing-to-paired-variables). -/
theorem passesOn_of_check {s : RowScope} {d : FnDecl} {rows : List Row}
    (h : (rows.all fun ρ => ρ.vars.isEmpty) = true) : PassesOnPairs s d (d.rowParams.zip rows) :=
  fun _ _ _ _ _ hl hr => by simp [vars_nil_of_lookup h hl] at hr

/-- A signature none of whose rows raises pairs no row variable with any
error type (effects.paired-row-variables). -/
theorem pairs_nothing {d : FnDecl}
    (h : ((paramRows (d.params.map Param.sig) ++ [d.row]).all (·.raise.isNone)) = true)
    (v : Name) (E : Ty) : ¬d.pairs v E := by
  rintro ⟨ρ, hρ, _, hraise⟩
  have := List.all_eq_true.1 h ρ hρ
  simp [hraise] at this

/-- What typing knows of a function with no type arguments named as a value. -/
theorem fnRef_inv {D : Decls} {s : RowScope} {Γ : Ctx} {fx : Effects} {f : Name}
    {rows : List Row} {τ : Ty} (h : HasType D s Γ fx (.fnRef f [] rows) τ) :
    ∃ d, D.fn? f = some d ∧ τ = d.type.substRows (d.rowParams.zip rows) ∧
      PassesOnPairs s d (d.rowParams.zip rows) := by
  cases h with
  | fnRef hd _ _ _ _ hpass _ =>
    exact ⟨_, hd, by simp [FnDecl.typeArgs, List.zip_nil_right, Ty.substTys_nil], hpass⟩

/-- The conditions of `FnDecl.ImplicitRows`, as one Boolean check. -/
def implicitRowsCheck (d : FnDecl) : Bool :=
  d.implicits.all (· ∈ d.rowParams) && decide d.implicits.Nodup &&
    d.params.all (fun p => match p.implicit, p.type with
      | none, _ => true
      | some v, .fn ps r ρ => decide (p.mode = .let) && decide (ρ.vars = [v]) &&
        (Ty.fn ps r ρ).innerRows.all (·.vars.isEmpty)
      | some _, _ => false) &&
    d.implicits.all (· ∈ d.row.vars) &&
    d.implicits.all (fun v =>
      d.params.all (fun p => decide (p.implicit = some v) || p.type.rows.all (v ∉ ·.vars)) &&
        d.result.rows.all (v ∉ ·.vars) && d.row.rows.tail.all (v ∉ ·.vars)) &&
    d.type.rows.all (fun σ => decide ((σ.vars.filter (· ∉ d.implicits)).length ≤ 1))

theorem implicitRows_of_check {d : FnDecl} (h : implicitRowsCheck d = true) : d.ImplicitRows := by
  simp only [implicitRowsCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hlisted, hfresh⟩, hparam⟩, hown⟩, helse⟩, hwritten⟩ := h
  refine ⟨hlisted, hfresh, fun p hp v hv => ?_, hown, fun v hv => ?_, hwritten⟩
  · have := hparam p hp
    cases hτ : p.type with
    | fn ps r ρ =>
      simp only [hv, hτ, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        List.isEmpty_iff] at this
      exact ⟨this.1.1, ps, r, ρ, rfl, this.1.2, this.2⟩
    | _ => simp [hv, hτ] at this
  · obtain ⟨⟨hps, hres⟩, hrow⟩ := helse v hv
    refine ⟨fun p hp hne σ hσ => ?_, fun σ hσ => by simpa using hres σ hσ,
      fun σ hσ => by simpa using hrow σ hσ⟩
    have := hps p hp
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at this
    simpa using (this.resolve_left hne) σ hσ

/-- The decision of the no-escape check for the programs of the
counterexamples. -/
theorem noEscape_of_check {p : Program}
    (h : (p.decls.fns.all fun d => d.body.noEscape p.decls d.nonEscaping false) = true) :
    p.NoEscape :=
  fun d hd => List.all_eq_true.1 h d hd

/-- The decisions of `Decls.WellFormed` for the programs of the
counterexamples. -/
theorem declsWellFormed {D : Decls}
    (hrecords : (D.records.map (·.name)).Nodup)
    (hfields : (D.records.all fun r =>
      decide (r.fields.map Prod.fst).Nodup &&
        r.fields.all fun f => f.2.concreteCheck && f.2.rows.all (·.effects.isEmpty)) = true)
    (hfieldsClosed : ∀ r ∈ D.records, ∀ f ∈ r.fields, f.2.Closed)
    (hvariants : D.variants = [] ∧ D.traits = [] ∧ D.traitImpls = [] ∧ D.effects = [])
    (hfns : (D.fns.map (·.name)).Nodup)
    (hparams : ∀ d ∈ D.fns, (d.params.map Param.name).Nodup)
    (hrowParams : ∀ d ∈ D.fns, d.rowParams.Nodup)
    (hsigs : D.fns.all signatureCheck = true)
    (himplicit : D.fns.all implicitRowsCheck = true) (hreceivers : D.Receivers) :
    D.WellFormed := by
  obtain ⟨hv, ht, hti, he⟩ := hvariants
  have hf := fun r hr => List.all_eq_true.1 hfields r hr
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hf
  exact ⟨hrecords, fun r hr => (hf r hr).1, hfieldsClosed,
    fun r hr f hfm => (Ty.concrete_of_check ((hf r hr).2 f hfm).1).2, by simp [hv], by simp [hv],
    by simp [hv], by simp [hv],
    ⟨fun r hr f hfm T hT => (by
      rw [(Ty.concrete_of_check ((hf r hr).2 f hfm).1).1] at hT
      exact nomatch hT), by simp [hv]⟩, hfns, hparams, hrowParams,
    fun d hd => by simp [(signatures_of_check hsigs d hd).1], fun d hd => (signatures_of_check hsigs d hd).2,
    fun d hd => implicitRows_of_check (List.all_eq_true.1 himplicit d hd), hreceivers,
    by simp [ht], by simp [hti], by simpa [Decls.typeNames, hv, ht, he] using hrecords,
    by simp [he], by simp [hti], by simp [hti],
    ⟨fun r hr f hfm => effectsIn_of_check (by simpa using ((hf r hr).2 f hfm).2), by simp [hv],
      signatureEffects_of_check hsigs, by simp [he], by simp [ht]⟩⟩

end Stilt.Counterexamples
