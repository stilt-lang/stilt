import Stilt.Soundness.Uses

/-!
# Trait methods

`Trait.m` at a type with an impl of the trait, an impl of `Eq`, `Ord` or `Show` that the
program writes among them, is the function of that impl, whose signature is the method's with
`Self` the type (traits.impl-signatures). In an instance, every type is ground, so a bound
that typing allowed is met by an impl (traits.unsatisfied-bounds), and the evaluator finds the
function by the type's head (traits.qualified-calls).
-/

namespace Stilt

section

variable {D : Decls}

/-- Names are unique, so a function is found by its own name. -/
theorem find?_name_of_mem :
    ∀ {l : List FnDecl} {d : FnDecl}, (l.map (·.name)).Nodup → d ∈ l →
      l.find? (·.name == d.name) = some d
  | d₀ :: l, d, hnd, hd => by
    rw [List.find?_cons]
    rcases List.mem_cons.1 hd with rfl | hd
    · simp
    · have hne : (d₀.name == d.name) = false := by
        simp only [beq_eq_false_iff_ne]
        intro heq
        exact (List.nodup_cons.1 hnd).1 (by simp only [heq]; exact List.mem_map_of_mem hd)
      rw [hne]
      exact find?_name_of_mem (List.nodup_cons.1 hnd).2 hd

theorem Decls.WellFormed.fn?_of_mem (hD : D.WellFormed) {d : FnDecl} (hd : d ∈ D.fns) : D.fn? d.name = some d :=
  find?_name_of_mem hD.fnNames hd

/-- The function that `Trait.m` at a head finds: the impl's member, with the impl's
parameters and no row variables, and the method's signature at the impl's type and
arguments. -/
theorem Decls.WellFormed.implFn (hD : D.WellFormed) {Tr m : Name} {t : TraitDecl} {σ : Ty}
    (ht : D.trait? Tr = some t) (hm : t.methods.lookup m = some σ) {h : Head} {i : TraitImpl}
    (hi : D.traitImpl? Tr h = some i) :
    ∃ d ∈ D.fns, D.fn? (implName Tr h m) = some d ∧ d.typeParams = i.typeParams ∧
      d.rowParams = [] ∧ d.type = σ.substTys ((selfParam, i.selfType) :: t.params.zip i.args) := by
  have him := List.mem_of_find?_eq_some hi
  have hp := List.find?_some hi
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  obtain ⟨t', ht', -, -, -, -, hfns⟩ := hD.traitImpls i him
  rw [ht] at ht'
  obtain rfl := Option.some.inj ht'
  obtain ⟨d, hd, rfl, htp, hrp, hty⟩ := hfns _ σ hm
  have hmem : d.within i.typeParams (implQualifier i.trait i.type) ∈ D.fns :=
    List.mem_append_right _ (List.mem_flatMap.2 ⟨i, him, List.mem_map_of_mem hd⟩)
  exact ⟨_, hmem, hD.fn?_of_mem hmem, by simp [FnDecl.within, htp], hrp, hty⟩

/-- A ground type's arguments are ground. -/
theorem Ty.Ground.args {τ : Ty} (h : τ.Ground) : ∀ a ∈ τ.args, a.Ground := by
  have key : ∀ (as : List Ty), (∀ ρ ∈ tysRows as, ρ.vars = []) → tysParams as = [] →
      (∀ ρ ∈ tysRows as, ρ.ParamFree) → ∀ a ∈ as, a.Ground := by
    intro as
    induction as with
    | nil => exact fun _ _ _ _ h => nomatch h
    | cons a as ih =>
      intro hc hp hf b hb
      simp only [tysRows, tysParams, List.append_eq_nil_iff, List.mem_append] at hc hp hf
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨fun ρ hρ => hc ρ (.inl hρ), hp.1, fun ρ hρ => hf ρ (.inl hρ)⟩
      · exact ih (fun ρ hρ => hc ρ (.inr hρ)) hp.2 (fun ρ hρ => hf ρ (.inr hρ)) b hb
  cases τ with
  | record _ as | variant _ as => exact key as h.1 h.2.1 h.2.2
  | _ => exact fun _ h => nomatch h

/-- Distinct names, each paired with a type, find the type paired with each of them. -/
theorem lookup_zip_mem :
    ∀ {ps : List TypeParam} {τs : List Ty}, (ps.map TypeParam.name).Nodup →
      ps.length = τs.length → ∀ {p : TypeParam}, p ∈ ps →
        ∃ σ, ((ps.map TypeParam.name).zip τs).lookup p.name = some σ ∧ (p, σ) ∈ ps.zip τs
  | [], _, _, _, _, h => nomatch h
  | _ :: _, [], _, hl, _, _ => nomatch hl
  | q :: ps, τ :: τs, hnd, hl, p, hp => by
    simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons, List.mem_cons]
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨τ, by simp, .inl rfl⟩
    · have hne : (p.name == q.name) = false := by
        have := (List.nodup_cons.1 hnd).1
        simp only [beq_eq_false_iff_ne]
        rintro heq
        exact this (heq ▸ List.mem_map_of_mem hp)
      rw [hne]
      obtain ⟨σ, h₁, h₂⟩ := lookup_zip_mem (List.nodup_cons.1 hnd).2 (by simpa using hl) hp
      exact ⟨σ, h₁, .inr h₂⟩

/-- Type parameters with distinct names, instantiated by types, one for each, are those
types. -/
theorem params_substTys_zip :
    ∀ {ps : List TypeParam} {τs : List Ty}, (ps.map TypeParam.name).Nodup →
      ps.length = τs.length →
        (ps.map fun p => Ty.param p.name).map (Ty.substTys ((ps.map TypeParam.name).zip τs)) = τs
  | [], [], _, _ => rfl
  | [], _ :: _, _, hl => nomatch hl
  | _ :: _, [], _, hl => nomatch hl
  | q :: ps, τ :: τs, hnd, hl => by
    rw [List.map_cons, List.map_cons, List.map_cons, List.zip_cons_cons]
    congr 1
    · simp [Ty.substTys]
    refine Eq.trans (List.map_congr_left fun σ hσ => ?_)
      (params_substTys_zip (List.nodup_cons.1 hnd).2 (by simpa using hl))
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hσ
    have hne : (p.name == q.name) = false := by
      have := (List.nodup_cons.1 hnd).1
      simp only [beq_eq_false_iff_ne]
      rintro heq
      exact this (heq ▸ List.mem_map_of_mem hp)
    simp [Ty.substTys, List.lookup_cons, hne]

/-- A head at arguments, instantiated, is the head at the instantiated arguments. -/
theorem Head.at_substTys (h : Head) (args : List Ty) (s : TySubst) :
    (h.at args).substTys s = h.at (args.map (Ty.substTys s)) := by
  cases h <;> simp [Head.at, Head.type, Ty.substTys, substTyList_eq_map]

/-- The impl's function, at a type's arguments, has the method's type at the type and at
the arguments that the impl gives the trait there. -/
theorem Decls.WellFormed.implFn_type (hD : D.WellFormed) {Tr m : Name} {t : TraitDecl}
    {σ τ : Ty} (ht : D.trait? Tr = some t) (hm : t.methods.lookup m = some σ) {h : Head}
    {i : TraitImpl} (hi : D.traitImpl? Tr h = some i) (hh : τ.head? = some h)
    (hlen : i.typeParams.length = τ.args.length) {d : FnDecl} (hmem : d ∈ D.fns)
    (htp : d.typeParams = i.typeParams)
    (hty : d.type = σ.substTys ((selfParam, i.selfType) :: t.params.zip i.args)) :
    d.type.substTys (d.typeArgs τ.args) = σ.substTys
      ((selfParam, τ) :: t.params.zip (i.args.map (Ty.substTys (i.typeArgs τ.args)))) := by
  obtain ⟨t', ht', hl, -, -⟩ := hD.implOf hi
  rw [ht] at ht'
  cases ht'
  have hih : i.type = h := by
    have hp := List.find?_some hi
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact hp.2
  have hnd : (i.typeParams.map TypeParam.name).Nodup := htp ▸ hD.typeParams d hmem
  have hsig := (hD.traits t (List.mem_of_find?_eq_some ht)).signatures _ (mem_of_lookup hm)
  have hz := TySubst.then_zip (selfParam :: t.params) (i.selfType :: i.args)
    (i.typeArgs τ.args)
  simp only [List.zip_cons_cons, List.map_cons] at hz
  have hself : i.selfType.substTys (i.typeArgs τ.args) = τ := by
    rw [TraitImpl.selfType, Head.at_substTys, List.map_map, hih]
    have := params_substTys_zip hnd hlen
    simp only [List.map_map] at this
    rw [show (Ty.substTys (i.typeArgs τ.args) ∘ fun p : TypeParam => Ty.param p.name) =
      ((Ty.substTys ((i.typeParams.map TypeParam.name).zip τ.args)) ∘
        fun p : TypeParam => Ty.param p.name) from rfl, this]
    exact (Ty.eq_of_head? hh).symm
  rw [hty, show d.typeArgs τ.args = i.typeArgs τ.args by simp [FnDecl.typeArgs, htp,
    TraitImpl.typeArgs], Ty.substTys_substTys _ _ _ fun T hT => ?_, hz, hself]
  have := hsig.2.1 T hT
  simp only [TraitDecl.scope, List.map_cons, List.map_map] at this
  have hT' : T ∈ selfParam :: t.params := by simpa [Function.comp_def] using this
  have := List.lookup_zip_isSome hT' (bs := i.selfType :: i.args) (by simp [hl])
  simpa only [List.zip_cons_cons] using this

end

section

variable {D : Decls} {n : Nat} {scope : RowScope} {η : REnv} (hη : η.Respects scope)
  (θ : RowSubst) {Γ : Ctx} {fx : Effects}
include hη

/-- `Trait.m` at a type of an instance is a function value of the method's
type at that type. -/
theorem method_ok (hD : D.WellFormed) {Tr m : Name} {t : TraitDecl} {σ τ : Ty}
    {args : List Ty} (ht : D.trait? Tr = some t) (hm : t.methods.lookup m = some σ)
    (hc : τ.Closed) (hwf : τ.WellFormed scope)
    (hf : MethodAt D scope τ Tr args) :
    Eval.Ok D Γ η (fx.exits D η)
      (fun v => Value.Typed D v ((σ.substTys ((selfParam, τ) :: t.params.zip args)).close η))
      (eval D Copy.memory (n + 1) ((Expr.method Tr m τ).substRows θ)) := by
  obtain ⟨h, i, hh, hi, happ, rfl⟩ : ∃ h i, τ.head? = some h ∧ D.traitImpl? Tr h = some i ∧
      ImplApplies D scope i τ ∧ i.args.map (Ty.substTys (i.typeArgs τ.args)) = args := by
    rcases hf with ⟨-, p, hp', _⟩ | hi
    · rw [hη.types] at hp'
      exact nomatch hp'
    · exact hi
  obtain ⟨d, hmem, hd, htp, hrp, hty⟩ := hD.implFn ht hm hi
  obtain ⟨-, -, -, -, hpargs⟩ := hD.implOf hi
  have hg : τ.Ground := Ty.ground_of_wellFormed hc hwf hη.types
  have hnd : (i.typeParams.map TypeParam.name).Nodup := htp ▸ hD.typeParams d hmem
  have hδ : (d.typeArgs τ.args).Fits D d.scope d.scope.instantiated := by
    refine ⟨fun p hp => hg.args _ (List.of_mem_zip hp).2,
      fun p hp => happ.2.1 _ (List.of_mem_zip hp).2, fun p hp => ?_,
      fun _ h => h, fun _ _ h => h, fun _ _ h => h, fun p hp _ _ fT hfT => by
        have hp' : p ∈ i.typeParams := by simpa [FnDecl.scope, htp] using hp
        rw [hD.implFields i (List.mem_of_find?_eq_some hi) p hp'] at hfT
        exact nomatch hfT⟩
    have hp' : p ∈ i.typeParams := by simpa [FnDecl.scope, htp] using hp
    obtain ⟨σ', hl', hm'⟩ := lookup_zip_mem hnd happ.1 hp'
    refine ⟨σ', by simpa [FnDecl.typeArgs, htp] using hl', fun B hB => ⟨?_, fun as has => ?_⟩⟩
    · exact (happ.2.2 _ hm' B hB).of_types fun q hq => by
        rw [hη.types] at hq
        exact nomatch hq
    · simp [TypeParam.argsOf, hpargs p hp'] at has
  have hclosed : d.type.Closed := fun ρ hρ => by
    have := (hD.signatures d hmem).1 ρ hρ
    simp only [FnDecl.scope, hrp, List.not_mem_nil] at this
    exact List.eq_nil_iff_forall_not_mem.2 this
  have htype := hD.implFn_type ht hm hi hh happ.1 hmem htp hty
  have hnone : ∀ v E, d.pairs v E → False := fun v E ⟨ρ, hρ, hv, _⟩ => by
    rw [hclosed ρ (FnDecl.mem_rows_of_pairs hρ)] at hv
    exact nomatch hv
  have hη' : η.Respects d.scope.instantiated :=
    ⟨fun v E hp => (hnone v E hp).elim, fun v E hp => (hnone v E hp).elim, rfl, hη.noResume⟩
  have hv : Value.Typed D (Value.function (implName Tr h m) τ.args [])
      ((σ.substTys ((selfParam, τ) ::
        t.params.zip (i.args.map (Ty.substTys (i.typeArgs τ.args))))).close η) :=
    .function hd hδ hη' (by
      rw [show (d.type.substTys (d.typeArgs τ.args)) = _ from htype]
      exact .refl _)
  rw [show (Expr.method Tr m τ).substRows θ = .method Tr m τ by
    simp [Expr.substRows, Ty.substRows_of_closed θ _ hc]]
  show Eval.Ok D Γ η _ _ (Eval.method D Tr m τ)
  unfold Eval.method
  rw [hh]
  dsimp only
  rw [hi]
  exact Eval.Ok.pure hv

end

end Stilt
