import Stilt.WellTyped
import Stilt.Generics.Commute

/-!
# What an instantiation of type parameters needs

The instantiation of a typing context, the conditions that an instantiation
of a body's type parameters meets (`TySubst.Fits`), and what typing's side
conditions become under it: well-formed types, bounds, type arguments, the
rows of calls, the signatures of operations and the places of assignments.
`Stilt.Instances` puts them together.
-/

namespace Stilt

/-! ## Contexts -/

/-- A binding with its type's parameters instantiated. -/
def Binding.substTys (s : TySubst) (b : Binding) : Binding := { b with type := b.type.substTys s }

/-- A context with its types' parameters instantiated. -/
def Ctx.substTys (s : TySubst) (Γ : Ctx) : Ctx := Γ.map (Prod.map id (Binding.substTys s))

/-- The names of a `when` bound in an instance are the instance's. -/
theorem Ctx.holding_substTys (s : TySubst) : ∀ (ns : List (Name × Ty)) (Γ : Ctx),
    (Γ.substTys s).holding (ns.map fun p => (p.1, p.2.substTys s)) = (Γ.holding ns).substTys s
  | [], _ => rfl
  | p :: ns, Γ => Ctx.holding_substTys s ns ((p.1, ⟨p.2, true⟩) :: Γ)

namespace Ctx

theorem lookup_substTys {Γ : Ctx} {x : Name} {τ : Ty} {m : Bool} (s : TySubst)
    (h : Γ.lookup x = some ⟨τ, m⟩) : (Γ.substTys s).lookup x = some ⟨τ.substTys s, m⟩ := by
  simp only [Ctx.substTys, lookup, lookup_map_snd]
  rw [show List.lookup x Γ = some ⟨τ, m⟩ from h]
  rfl

theorem freeze_substTys (s : TySubst) (Γ : Ctx) : Γ.freeze.substTys s = (Γ.substTys s).freeze := by
  simp [Ctx.substTys, freeze, Binding.substTys]

theorem params_substTys (s : TySubst) (ps : List Param) :
    ∀ Γ : Ctx, (Γ.params ps).substTys s = (Γ.substTys s).params (ps.map (Param.substTys s)) := by
  induction ps with
  | nil => intro Γ; rfl
  | cons p ps ih => intro Γ; exact ih (Γ.bind p.name _)

theorem bindAll_substTys (s : TySubst) (xs : List Name) (τs : List Ty)
    (hτs : ∀ τ ∈ τs, τ.params = []) (Γ : Ctx) :
    (Γ.bindAll xs τs).substTys s = (Γ.substTys s).bindAll xs τs := by
  unfold bindAll
  induction xs generalizing τs Γ with
  | nil => rfl
  | cons x xs ih =>
    cases τs with
    | nil => rfl
    | cons τ τs =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      rw [ih τs (fun σ hσ => hτs σ (List.mem_cons_of_mem _ hσ))]
      simp [Ctx.substTys, bind, Binding.substTys, Ty.substTys_of_params (hτs τ List.mem_cons_self)]

/-- Binding names, instantiated, binds them at the instantiated types. -/
theorem bindAll_substTys_map (s : TySubst) (xs : List Name) (τs : List Ty) (Γ : Ctx) :
    (Γ.bindAll xs τs).substTys s = (Γ.substTys s).bindAll xs (τs.map (Ty.substTys s)) := by
  unfold bindAll
  induction xs generalizing τs Γ with
  | nil => rfl
  | cons x xs ih =>
    cases τs with
    | nil => rfl
    | cons τ τs =>
      simp only [List.zip_cons_cons, List.foldl_cons, List.map_cons]
      rw [ih τs]
      rfl

end Ctx

/-! ## What an instantiation needs -/

/-- An instantiation of the type parameters of a body checked in `scope`, for
an instance checked in `scope'`: ground types for all of them, each meeting its
parameter's bounds there, in a scope that allows what the body's allows. -/
structure TySubst.Fits (D : Decls) (scope scope' : RowScope) (s : TySubst) : Prop where
  ground : s.Ground
  viewable : ∀ p ∈ s, p.2.ViewsViewable
  covers : ∀ p ∈ scope.types, ∃ σ, s.lookup p.name = some σ ∧ ∀ B ∈ p.bounds,
    Satisfies D scope' σ B ∧
      ∀ args, p.argsOf B = some args → TraitArgs D scope' σ B (args.map (Ty.substTys s))
  vars : ∀ v ∈ scope.vars, v ∈ scope'.vars
  pairs : ∀ v E, scope.pairs v E → scope'.pairs v E
  passOn : ∀ v E, scope.passOn v E → scope'.passOn v E
  /-- Each parameter's instance has the fields its record bound names, at their instances
  (records.record-bounds). -/
  records : ∀ p ∈ scope.types, ∀ σ, s.lookup p.name = some σ → ∀ fT ∈ p.fields,
    FieldOf D scope' σ fT.1 (fT.2.substTys s)

section

variable {D : Decls} {scope scope' : RowScope} {s : TySubst}

theorem TySubst.Fits.isSome (hs : s.Fits D scope scope') {p : TypeParam} (hp : p ∈ scope.types) :
    (s.lookup p.name).isSome := by
  obtain ⟨σ, hl, _⟩ := hs.covers p hp
  simp [hl]

theorem TySubst.Fits.wellFormed (hs : s.Fits D scope scope') {τ : Ty} (h : τ.WellFormed scope) :
    (τ.substTys s).WellFormed scope' :=
  h.substTys hs.ground hs.viewable (fun _ hp => hs.isSome hp) hs.vars

/-- What implementing a prelude trait asks of a type at its outermost type holds of its
instance, with its components' instances in `S'`, and the types that implement the trait
where the instance is: a type parameter implements it through a bound, which the type
the instantiation gives it meets. -/
theorem Decls.ImplStep.substTys (hD : D.WellFormed) (hs : s.Fits D scope scope')
    {t : PreludeTrait} {S S' : Ty → Prop} (hS : ∀ σ, S σ → S' (σ.substTys s))
    (hI : ∀ σ, D.Implements scope' t σ → S' σ) :
    ∀ {σ : Ty}, D.ImplStep scope t S σ → D.ImplStep scope' t S' (σ.substTys s)
  | .int _, _ | .bool, _ | .str, _ | .unit, _ | .never, _ => trivial
  | .float _, h => h
  | .tuple τs, h => by
    show ∀ τ ∈ substTyList s τs, S' τ
    rw [substTyList_eq_map]
    intro τ' hτ'
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hτ'
    exact hS τ (h τ hτ)
  | .list τ, h => hS τ h
  | .record R args, ⟨hn, r, hr, hl, hf⟩ => by
    show D.ImplStep scope' t S' (.record R (substTyList s args))
    rw [substTyList_eq_map]
    refine ⟨hn, r, hr, by rw [List.length_map]; exact hl, fun f hf' => ?_⟩
    rw [← RecordDecl.fieldsAt_substTys
      (hD.paramsDeclared.fields r (List.mem_of_find?_eq_some hr)) hl s] at hf'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf'
    exact hS _ (hf g hg)
  | .variant T args, ⟨hn, v, hv, hl, hc⟩ => by
    show D.ImplStep scope' t S' (.variant T (substTyList s args))
    rw [substTyList_eq_map]
    refine ⟨hn, v, hv, by rw [List.length_map]; exact hl, fun c hc' τ' hτ' => ?_⟩
    rw [← VariantDecl.ctorsAt_substTys
      (hD.paramsDeclared.payloads v (List.mem_of_find?_eq_some hv)) hl s] at hc'
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc'
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hτ'
    exact hS _ (hc c₀ hc₀ τ hτ)
  | .map κ υ, h => by
    show D.ImplStep scope' t S' (.map (κ.substTys s) (υ.substTys s))
    cases t with
    | eq => rw [h.1.substTys s]; exact ⟨h.1, h.2.1, hS υ h.2.2⟩
    | ord => exact h.elim
    | «show» => exact ⟨hS κ h.1, hS υ h.2⟩
    | hash => exact h.elim
  | .set κ, h => by
    show D.ImplStep scope' t S' (.set (κ.substTys s))
    cases t with
    | eq => rw [h.1.substTys s]; exact h
    | ord => exact h.elim
    | «show» => exact hS κ h
    | hash => exact h.elim
  | .param _, ⟨q, hq, hp, hB⟩ => by
    subst hp
    obtain ⟨σ, hl, hσ⟩ := hs.covers q hq
    show D.ImplStep scope' t S' ((s.lookup q.name).getD (.param q.name))
    rw [hl, Option.getD_some]
    cases (hσ t.name hB).1 with
    | param hr hrB => exact ⟨_, hr, rfl, hrB⟩
    | impl hn => rw [PreludeTrait.ofName?_name] at hn; cases hn
    | prelude ht' hi =>
      rw [PreludeTrait.ofName?_name] at ht'
      cases ht'
      exact hi.step.mono hI
  | .fn .., h | .view _, h | .shared _, h => h.elim

/-- An instance of a type that implements a prelude trait implements it where the
instance is (traits.unsatisfied-bounds). -/
theorem Decls.Implements.substTys (hD : D.WellFormed) (hs : s.Fits D scope scope')
    {t : PreludeTrait} {τ : Ty} (h : D.Implements scope t τ) :
    D.Implements scope' t (τ.substTys s) := by
  obtain ⟨S, hτ, hS⟩ := h
  refine ⟨fun σ' => (∃ σ, S σ ∧ σ' = σ.substTys s) ∨ D.Implements scope' t σ',
    .inl ⟨τ, hτ, rfl⟩, ?_⟩
  rintro σ' (⟨σ, hσ, rfl⟩ | hi)
  · exact (hS σ hσ).substTys hD hs (fun σ hσ => .inl ⟨σ, hσ, rfl⟩) fun _ h => .inr h
  · exact hi.step.mono fun _ h => .inr h

theorem TySubst.Fits.satisfies (hD : D.WellFormed) (hs : s.Fits D scope scope') {τ : Ty}
    {B : Name} (h : Satisfies D scope τ B) : Satisfies D scope' (τ.substTys s) B := by
  induction h with
  | @param p B hp hB =>
    obtain ⟨σ, hl, hσ⟩ := hs.covers p hp
    simpa [Ty.substTys, hl] using (hσ B hB).1
  | @impl τ B h i hn hh hi hl hv _ ih =>
    refine .impl hn (Ty.head?_substTys hh s) hi
      (by rw [Ty.args_substTys hh, List.length_map]; exact hl) (fun a ha => ?_)
      fun pa hpa B' hB' => ?_
    · rw [Ty.args_substTys hh] at ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      exact Ty.ViewsViewable.substTys s hs.viewable b (hv b hb)
    rw [Ty.args_substTys hh, List.zip_map_right] at hpa
    obtain ⟨⟨p, a⟩, hmem, rfl⟩ := List.mem_map.1 hpa
    exact ih _ hmem B' hB'
  | prelude ht hi => exact .prelude ht (hi.substTys hD hs)

/-- What the program's impl of a trait is: an impl of a trait it declares, with one argument
for each of the trait's parameters, which name only the impl's parameters, and bounds that
write no trait arguments. -/
theorem Decls.WellFormed.implOf (hD : D.WellFormed) {B : Name} {h : Head} {i : TraitImpl}
    (hi : D.traitImpl? B h = some i) :
    ∃ t, D.trait? B = some t ∧ i.args.length = t.params.length ∧
      (∀ a ∈ i.args, a.Closed ∧ ∀ T ∈ a.params, T ∈ i.typeParams.map TypeParam.name) ∧
      ∀ p ∈ i.typeParams, p.args = [] := by
  have hp := List.find?_some hi
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨t, ht, hl, hg, -, hargs, -⟩ := hD.traitImpls i (List.mem_of_find?_eq_some hi)
  exact ⟨t, hp.1 ▸ ht, hl, hg, hargs⟩

/-- An impl's arguments at a type's arguments, in an instance, are its arguments at the
instance's arguments. -/
theorem TraitImpl.args_substTys (hD : D.WellFormed) {B : Name} {h : Head} {i : TraitImpl}
    (hi : D.traitImpl? B h = some i) {τs : List Ty} (hl : i.typeParams.length = τs.length)
    (s : TySubst) :
    (i.args.map (Ty.substTys (i.typeArgs τs))).map (Ty.substTys s) =
      i.args.map (Ty.substTys (i.typeArgs (τs.map (Ty.substTys s)))) := by
  obtain ⟨-, -, -, ha, -⟩ := hD.implOf hi
  rw [List.map_map]
  refine List.map_congr_left fun a hm => ?_
  simp only [Function.comp_apply, TraitImpl.typeArgs]
  rw [Ty.substTys_substTys _ _ _ fun T hT =>
    List.lookup_zip_isSome ((ha a hm).2 T hT) (by simpa using hl.symm), TySubst.then_zip]

/-- The impl that applies to a type applies to its instance. -/
theorem ImplApplies.substTys (hD : D.WellFormed) (hs : s.Fits D scope scope') {τ : Ty}
    {h : Head} (hh : τ.head? = some h) {i : TraitImpl} (happ : ImplApplies D scope i τ) :
    ImplApplies D scope' i (τ.substTys s) := by
  refine ⟨by rw [Ty.args_substTys hh, List.length_map]; exact happ.1, fun a ha => ?_,
    fun pa hpa B hB => ?_⟩
  · rw [Ty.args_substTys hh] at ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    exact Ty.ViewsViewable.substTys s hs.viewable b (happ.2.1 b hb)
  rw [Ty.args_substTys hh, List.zip_map_right] at hpa
  obtain ⟨⟨p, a⟩, hmem, rfl⟩ := List.mem_map.1 hpa
  exact hs.satisfies hD (happ.2.2 _ hmem B hB)

/-- A type with a head that meets a bound of a trait other than the prelude's meets it
through the impl for its head, which applies to it. -/
theorem Satisfies.applies {sc : RowScope} {σ : Ty} {Tr : Name} (h : Satisfies D sc σ Tr)
    (hn : PreludeTrait.ofName? Tr = none) {h' : Head} (hh : σ.head? = some h') {i : TraitImpl}
    (hi : D.traitImpl? Tr h' = some i) : ImplApplies D sc i σ := by
  cases h with
  | param => exact nomatch hh
  | impl _ hh' hi' hl hv hb =>
    rw [hh] at hh'
    cases hh'
    rw [hi] at hi'
    cases hi'
    exact ⟨hl, hv, hb⟩
  | prelude ht => rw [hn] at ht; exact nomatch ht

/-- The arguments a type gives a trait, in an instance: a type parameter's through the type
that the instantiation gives it, which meets the parameter's bound, and a type with a head
its impl's, at the instance's arguments. -/
theorem TraitArgs.substTys (hD : D.WellFormed) (hs : s.Fits D scope scope') {τ : Ty}
    {B : Name} {args : List Ty} (h : TraitArgs D scope τ B args) :
    TraitArgs D scope' (τ.substTys s) B (args.map (Ty.substTys s)) := by
  rcases h with ⟨q, hq, rfl, hB, ha⟩ | ⟨h, i, hh, hi, hl, rfl⟩
  · obtain ⟨σ, hl, hσ⟩ := hs.covers q hq
    simpa [Ty.substTys, hl] using (hσ B hB).2 _ ha
  · refine .inr ⟨h, i, Ty.head?_substTys hh s, hi,
      by rw [Ty.args_substTys hh, List.length_map]; exact hl, ?_⟩
    rw [Ty.args_substTys hh]
    exact (TraitImpl.args_substTys hD hi hl s).symm

/-- `Trait.m` at a type, in an instance: at a type parameter, the impl or the bound that the
type the instantiation gives it has. -/
theorem MethodAt.substTys (hD : D.WellFormed) (hs : s.Fits D scope scope') {τ : Ty} {Tr : Name}
    {args : List Ty} (h : MethodAt D scope τ Tr args) :
    MethodAt D scope' (τ.substTys s) Tr (args.map (Ty.substTys s)) := by
  rcases h with ⟨hn, q, hq, rfl, hB, ha | ⟨rfl, t, ht, htp⟩⟩ | ⟨h, i, hh, hi, happ, rfl⟩
  · obtain ⟨σ, hl, hσ⟩ := hs.covers q hq
    have hsub : (Ty.param q.name).substTys s = σ := by simp [Ty.substTys, hl]
    rw [hsub]
    rcases (hσ Tr hB).2 _ ha with ⟨r, hr, rfl, hrB, hra⟩ | ⟨h, i, hh, hi, -, he⟩
    · exact .inl ⟨hn, r, hr, rfl, hrB, .inl hra⟩
    · exact .inr ⟨h, i, hh, hi, (hσ Tr hB).1.applies hn hh hi, he⟩
  · obtain ⟨σ, hl, hσ⟩ := hs.covers q hq
    have hsub : (Ty.param q.name).substTys s = σ := by simp [Ty.substTys, hl]
    rw [hsub, List.map_nil]
    cases (hσ Tr hB).1 with
    | param hr hrB => exact .inl ⟨hn, _, hr, rfl, hrB, .inr ⟨rfl, t, ht, htp⟩⟩
    | impl _ hh hi hl' hv hb =>
      obtain ⟨t', ht', hl'', -⟩ := hD.implOf hi
      rw [ht] at ht'
      cases ht'
      rw [htp] at hl''
      exact .inr ⟨_, _, hh, hi, ⟨hl', hv, hb⟩, by rw [List.eq_nil_of_length_eq_zero hl'']; rfl⟩
    | prelude ht' => rw [hn] at ht'; exact nomatch ht'
  · refine .inr ⟨h, i, Ty.head?_substTys hh s, hi, happ.substTys hD hs hh, ?_⟩
    rw [Ty.args_substTys hh]
    exact (TraitImpl.args_substTys hD hi happ.1 s).symm

theorem TySubst.Fits.callAllowed (hs : s.Fits D scope scope') {fx : Effects} {σ : Row}
    (h : CallAllowed scope fx σ) : CallAllowed scope' fx σ :=
  ⟨h.within, h.marked, fun hc v hv =>
    let ⟨E, hE, hp⟩ := h.paired hc v hv
    ⟨E, hE, hs.pairs v E hp⟩, h.resume⟩

theorem TySubst.Fits.passesOn (hs : s.Fits D scope scope') {d : FnDecl} {θ : RowSubst}
    (h : PassesOnPairs scope d θ) : PassesOnPairs scope' d θ :=
  fun v E ρ r hp hl hr => hs.passOn r _ (h v E ρ r hp hl hr)

/-- A type well formed with no type parameters in scope names none. -/
theorem Ty.WellFormed.params_nil {τ : Ty} {scope : RowScope} (h : τ.WellFormed { scope with types := [] }) :
    τ.params = [] := by
  cases hp : τ.params with
  | nil => rfl
  | cons T _ =>
    have := h.2.1 T (by simp [hp])
    simp at this

theorem TySubst.Fits.withoutTypes (hs : s.Fits D scope scope') {τ : Ty}
    (h : τ.WellFormed { scope with types := [] }) : τ.WellFormed { scope' with types := [] } :=
  ⟨fun ρ hρ v hv => hs.vars v (h.1 ρ hρ v hv), fun T hT => h.2.1 T hT, h.2.2⟩

end

/-! ## The types an instance reads -/

theorem fst_substFieldTys (s : TySubst) :
    ∀ fields : List (Name × Expr), (substFieldTys s fields).map Prod.fst = fields.map Prod.fst
  | [] => rfl
  | _ :: fields => by simp [substFieldTys, fst_substFieldTys s fields]

theorem MapOp.Sig.substTys {o : MapOp} {τs : List Ty} {τ : Ty} (h : MapOp.Sig o τs τ)
    (s : TySubst) : MapOp.Sig o (τs.map (Ty.substTys s)) (τ.substTys s) := by
  cases h with
  | new hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .new hk
  | withDefault hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .withDefault hk
  | len hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .len hk
  | isEmpty hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .isEmpty hk
  | contains hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .contains hk
  | index hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .index hk
  | getOr hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .getOr hk
  | insert hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .insert hk
  | remove hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .remove hk
  | keys hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .keys hk
  | values hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .values hk
  | entries hk => simp only [List.map, Ty.substTys, substTyList, hk.substTys]; exact .entries hk
  | equal hk hv =>
    simp only [List.map, Ty.substTys, hk.substTys, hv.substTys]; exact .equal hk hv

theorem SetOp.Sig.substTys {o : SetOp} {τs : List Ty} {τ : Ty} (h : SetOp.Sig o τs τ)
    (s : TySubst) : SetOp.Sig o (τs.map (Ty.substTys s)) (τ.substTys s) := by
  cases h with
  | new hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .new hk
  | fromList hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .fromList hk
  | len hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .len hk
  | isEmpty hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .isEmpty hk
  | contains hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .contains hk
  | insert hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .insert hk
  | remove hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .remove hk
  | toList hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .toList hk
  | combine hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .combine hk
  | relate hk => simp only [List.map, Ty.substTys, hk.substTys]; exact .relate hk

theorem ListOp.Sig.substTys {o : ListOp} {τs : List Ty} {τ : Ty} (h : ListOp.Sig o τs τ)
    (s : TySubst) : ListOp.Sig o (τs.map (Ty.substTys s)) (τ.substTys s) := by
  cases h <;> simp only [List.map, Ty.substTys] <;> constructor

theorem Op.Sig.substTys {o : Op} {τs : List Ty} {τ : Ty} (h : Op.Sig o τs τ) {s : TySubst}
    (hs : s.Ground) : Op.Sig (o.substTys s) (τs.map (Ty.substTys s)) (τ.substTys s) := by
  cases h with
  | tuple h =>
    rw [show (Ty.tuple τs).substTys s = .tuple (τs.map (Ty.substTys s)) by
      simp [Ty.substTys, substTyList_eq_map]]
    exact .tuple (by simpa using h)
  | concat => rw [List.map_replicate]; exact .concat
  | neg h => exact .neg h
  | float h => exact .float h
  | convert h₁ h₂ => exact .convert h₁ h₂
  | farith h => exact .farith h
  | funary h₁ h₂ => exact .funary h₁ h₂
  | fbinary h => exact .fbinary h
  | list h => exact .list (h.substTys s)
  | map h => exact .map (h.substTys s)
  | set h => exact .set (h.substTys s)
  | viewAll h =>
    refine .viewAll ?_
    rename_i τ
    cases τ <;> first | exact h | simp [Ty.viewable] at h
  | viewOf h =>
    refine .viewOf ?_
    rename_i τ
    cases τ <;> first | exact h | simp [Ty.viewable] at h
  | viewPart h =>
    refine .viewPart ?_
    rename_i τ
    cases τ <;> first | exact h | simp [Ty.viewable] at h
  | @intMethod m k =>
    cases hs : m.second k <;> simp only [Option.map, Option.toList, List.map, Ty.substTys] <;>
      first | exact (hs ▸ Op.Sig.intMethod : Op.Sig _ _ _) | (rw [← hs]; exact .intMethod)
  | world h =>
    cases h with
    | sharedNew hu => exact .world (.sharedNew (hu.substTys hs))
    | _ => exact .world (by constructor)
  | _ => constructor

/-- An instance of an operation finds keys of the same key types: a key type names no
type parameter. -/
theorem Op.KeysIn.substTys {D : Decls} {o : Op} {τs : List Ty} {τ : Ty} (hk : o.KeysIn D τs τ)
    (h : Op.Sig o τs τ) (s : TySubst) :
    (o.substTys s).KeysIn D (τs.map (Ty.substTys s)) (τ.substTys s) := by
  cases h with
  | map h =>
    cases h with
    | equal hκ hυ =>
      simpa [Op.KeysIn, Op.keyTypes, Op.substTys, Ty.substTys, hκ.substTys, hυ.substTys] using hk
    | _ hk' => simpa [Op.KeysIn, Op.keyTypes, Op.substTys, Ty.substTys, hk'.substTys] using hk
  | set h =>
    cases h <;> rename_i hk' <;>
      simpa [Op.KeysIn, Op.keyTypes, Op.substTys, Ty.substTys, hk'.substTys] using hk
  | _ => intro κ hκ; simp [Op.keyTypes, Op.substTys] at hκ

/-- An instance of an operation needs its traits of the instances of its operands' types,
which implement them where the instance is. -/
theorem Op.BoundsIn.substTys {D : Decls} {scope scope' : RowScope} {s : TySubst} {o : Op}
    {τs : List Ty} {τ : Ty} (hD : D.WellFormed)
    (hs : s.Fits D scope scope') (h : Op.Sig o τs τ) (hb : o.BoundsIn D scope τs) :
    (o.substTys s).BoundsIn D scope' (τs.map (Ty.substTys s)) := by
  cases h with
  | structural =>
    intro p hp
    simp only [Op.substTys, List.map, Op.traitsNeeded, List.mem_singleton] at hp
    subst hp
    exact (hb _ List.mem_cons_self).substTys hD hs
  | showValue =>
    intro p hp
    simp only [Op.substTys, List.map, Op.traitsNeeded, List.mem_singleton] at hp
    subst hp
    exact (hb _ List.mem_cons_self).substTys hD hs
  | sortedByKey =>
    intro p hp
    simp only [Op.substTys, List.map, Ty.substTys, Op.traitsNeeded, List.mem_singleton] at hp
    subst hp
    exact (hb _ List.mem_cons_self).substTys hD hs
  | world h => exact Op.boundsIn_of_nil (by cases h <;> rfl)
  | _ => exact Op.boundsIn_of_nil rfl

/-- A place with its indexes' types instantiated. -/
def Place.substTys (s : TySubst) (p : Place) : Place := ⟨p.root, substPathTys s p.path⟩

theorem Expr.substTys_assign (s : TySubst) (p : Place) (e : Expr) :
    (Expr.assign p e).substTys s = .assign (p.substTys s) (e.substTys s) := by
  cases p; rfl

theorem substArgTys_inout (s : TySubst) (p : Place) (args : List Arg) :
    substArgTys s (.inout p :: args) = .inout (p.substTys s) :: substArgTys s args := by
  cases p; rfl

theorem substArmTys_cons (s : TySubst) (arm : Arm) (arms : List Arm) :
    substArmTys s (arm :: arms) =
      ⟨arm.pattern, arm.binders, substGuardTys s arm.guard, arm.body.substTys s⟩ ::
        substArmTys s arms := by
  cases arm; rfl

/-- Instantiating a `match`'s arms leaves their patterns as they are. -/
theorem armRows_substTys (s : TySubst) : ∀ arms : List Arm,
    armRows (substArmTys s arms) = armRows arms
  | [] => rfl
  | ⟨p, _, g, _⟩ :: arms => by
    have ih := armRows_substTys s arms
    simp only [armRows] at ih ⊢
    cases g <;> cases hp : p.hasConst <;>
      simp [substArmTys, substGuardTys, Arm.counts, hp, ih]

end Stilt
