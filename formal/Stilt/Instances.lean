import Stilt.Instances.Patterns

/-!
# Instances of generic bodies

A generic function's body is checked once, with its type parameters rigid and
their bounds all it knows of them (traits.unsatisfied-bounds and polymorphism.rigid-types),
and each call runs the body instantiated with the call's type arguments
(types.no-type-arguments). `HasType.substTys` is the fact that this rests on: an
instantiation by ground types that meet the parameters' bounds where the
instance is checked keeps every derivation, at the instantiated types.

The types a body reads from declarations, those of record fields and variant
payloads, name no type parameter, and neither does the row the body runs in, so
those stay as they are.
-/

namespace Stilt

/-! ## Derivations of instances -/

section

variable {D : Decls} {scope scope' : RowScope} {s : TySubst}

theorem Decls.WellFormed.fieldParams (hD : D.WellFormed) {R : Name} {r : RecordDecl}
    (hR : D.record? R = some r) : ∀ p ∈ r.fields, p.2.params = [] :=
  fun p hp => (hD.fieldsConcrete r (List.mem_of_find?_eq_some hR) p hp).1

theorem Decls.WellFormed.payloadParams (hD : D.WellFormed) {T : Name} {t : VariantDecl}
    (hT : D.variant? T = some t) : ∀ c ∈ t.ctors, ∀ τ ∈ c.2, τ.params = [] :=
  fun c hc τ hτ => (hD.payloadsConcrete t (List.mem_of_find?_eq_some hT) c hc τ hτ).1

/-- The type of a use of a function, instantiated, is the type of the use
with its type arguments instantiated. -/
theorem fnRefType_substTys (hD : D.WellFormed) (hs : s.Ground) {f : Name} {d : FnDecl}
    (hd : D.fn? f = some d) {types : List Ty} (hlen : types.length = d.typeParams.length)
    (rows : List Row) :
    ((d.type.substTys (d.typeArgs types)).substRows (d.rowParams.zip rows)).substTys s =
      (d.type.substTys (d.typeArgs (types.map (Ty.substTys s)))).substRows (d.rowParams.zip rows) := by
  have hcov : ∀ T ∈ d.type.params, ((d.typeArgs types).lookup T).isSome := fun T hT =>
    List.lookup_zip_isSome ((hD.signatures d (List.mem_of_find?_eq_some hd)).2.1 T hT)
      (by simpa using hlen)
  rw [← Ty.substTys_substRows hs, Ty.substTys_substTys _ _ _ hcov, FnDecl.typeArgs,
    TySubst.then_zip, FnDecl.typeArgs]

/-- The type of `Trait.m` at an instance is the method's type at the instance. -/
theorem methodType_substTys (hD : D.WellFormed) {Tr m : Name} {t : TraitDecl} {σ τ : Ty}
    (ht : D.trait? Tr = some t) (hm : t.methods.lookup m = some σ) (s : TySubst) :
    (σ.substTys [(selfParam, τ)]).substTys s = σ.substTys [(selfParam, τ.substTys s)] := by
  have hsig := (hD.traits t (List.mem_of_find?_eq_some ht)).signatures _ (mem_of_lookup hm)
  rw [Ty.substTys_substTys _ _ _ fun T hT => ?_]
  · rfl
  have := hsig.2.1 T hT
  simp only [TraitDecl.scope, List.map_cons, List.map_nil, List.mem_singleton] at this
  subst this
  rfl

/-- Where an expression sits, in an instance: a `return`'s result type
instantiated, the rest as it is. -/
def Effects.substTys (s : TySubst) (fx : Effects) : Effects :=
  { fx with result := fx.result.substTys s }

/-- Whether a call is allowed doesn't depend on a `return`'s result type. -/
theorem CallAllowed.substTys_effects {sc : RowScope} {fx : Effects} {σ : Row}
    (h : CallAllowed sc fx σ) (s : TySubst) : CallAllowed sc (fx.substTys s) σ :=
  ⟨h.within, h.marked, h.paired, h.resume⟩

/-- What a handler's fields implement doesn't depend on a `return`'s result
type, and survives a larger scope. -/
theorem HandlerFits.substTys (hs : s.Fits D scope scope') {fx : Effects} {eff : EffectDecl}
    {fields : List (Name × Ty)} {c : Option Ty} (h : HandlerFits scope fx eff fields c) :
    HandlerFits scope' (fx.substTys s) eff fields c := fun o A B ho =>
  let ⟨ρ, h₁, h₂, h₃⟩ := h o A B ho
  ⟨ρ, h₁, h₂, (hs.callAllowed h₃).substTys_effects s⟩

/-- A use of a function, instantiated. -/
theorem HasType.fnRef_substTys (hD : D.WellFormed) (hs : s.Fits D scope scope') {Γ : Ctx}
    {fx : Effects} {f : Name} {d : FnDecl} {types : List Ty} {rows : List Row}
    (hd : D.fn? f = some d) (hlen : rows.length = d.rowParams.length)
    (hinst : d.type.InstantiableBy (d.rowParams.zip rows)) (hres : ∀ ρ ∈ rows, ρ.resume = none)
    (hwf : ((d.type.substTys (d.typeArgs types)).substRows (d.rowParams.zip rows)).WellFormed scope)
    (hpass : PassesOnPairs scope d (d.rowParams.zip rows))
    (htys : TypeArgsFit D scope d.typeParams types) :
    HasType D scope' (Γ.substTys s) fx ((Expr.fnRef f types rows).substTys s)
      (((d.type.substTys (d.typeArgs types)).substRows (d.rowParams.zip rows)).substTys s) := by
  have heq := fnRefType_substTys hD hs.ground hd htys.length_eq.symm rows
  rw [heq]
  show HasType D scope' _ _ (.fnRef _ (substTyList s types) rows) _
  rw [substTyList_eq_map]
  exact .fnRef hd hlen hinst hres (heq ▸ hs.wellFormed hwf) (hs.passesOn hpass) (hs.typeArgs htys)

/-- `Trait.m` at a type, instantiated. -/
theorem HasType.method_substTys (hD : D.WellFormed) (hs : s.Fits D scope scope') {Γ : Ctx}
    {fx : Effects} {Tr m : Name} {t : TraitDecl} {σ τ : Ty} (ht : D.trait? Tr = some t)
    (hm : t.methods.lookup m = some σ) (hc : τ.Closed) (hwf : τ.WellFormed scope)
    (hsat : Satisfies D scope τ Tr) :
    HasType D scope' (Γ.substTys s) fx ((Expr.method Tr m τ).substTys s)
      ((σ.substTys [(selfParam, τ)]).substTys s) := by
  rw [methodType_substTys hD ht hm s]
  exact .method ht hm (hc.substTys hs.ground) (hs.wellFormed hwf) (hs.satisfies hsat)

/-- A closure literal, instantiated, from its instantiated body. -/
theorem HasType.closure_substTys (hs : s.Fits D scope scope') {Γ : Ctx} {fx : Effects}
    {ps : List Param} {r : Ty} {ρ : Row} {body : Expr} {σ : Ty} (hnd : (ps.map Param.name).Nodup)
    (hpt : ps.all (·.implicit.isNone) = true) (hwf : (Ty.fn (ps.map Param.sig) r ρ).WellFormed scope)
    (h : HasType D scope' ((Γ.substTys s).freeze.params (ps.map (Param.substTys s)))
      ⟨ρ, fx.marked, false, r.substTys s, false, false⟩ (body.substTys s) (σ.substTys s))
    (hfit : Fits σ r) :
    HasType D scope' (Γ.substTys s) fx ((Expr.closure ps r ρ body).substTys s)
      ((Ty.fn (ps.map Param.sig) r ρ).substTys s) := by
  have hwf' : (Ty.fn (substParamTys s (ps.map Param.sig)) (r.substTys s) ρ).WellFormed scope' :=
    hs.wellFormed hwf
  show HasType D scope' _ _ (.closure (ps.map (Param.substTys s)) _ ρ _)
    (.fn (substParamTys s (ps.map Param.sig)) _ ρ)
  rw [← map_sig_substTys] at hwf' ⊢
  exact .closure (by simpa [Param.substTys, Function.comp_def] using hnd)
    (by simpa [Param.substTys, Function.comp_def] using hpt) hwf' h (hfit.substTys s)

/-- A `try … catch`, instantiated, from its instantiated operand and handler;
the caught type names no type parameter. -/
theorem HasType.tryCatch_substTys (hs : s.Fits D scope scope') {Γ : Ctx} {fx : Effects}
    {e h : Expr} {E τ σ σ' : Ty} {x : Name} (hwfE : E.WellFormed { scope with types := [] })
    (hwf : τ.WellFormed scope)
    (he : HasType D scope' (Γ.substTys s) ⟨fx.row.withRaise E, true, true, fx.result, fx.breaks, fx.continues⟩ (e.substTys s) (σ.substTys s))
    (hfe : Fits σ τ)
    (hh : HasType D scope' ((Γ.substTys s).bind x ⟨E.substTys s, false⟩) fx (h.substTys s)
      (σ'.substTys s)) (hfh : Fits σ' τ) :
    HasType D scope' (Γ.substTys s) fx ((Expr.tryCatch e E x h τ).substTys s) (τ.substTys s) := by
  have hE : E.substTys s = E := Ty.substTys_of_params hwfE.params_nil s
  rw [hE] at hh
  show HasType D scope' _ _ (.tryCatch _ (E.substTys s) x _ _) _
  rw [hE]
  exact .tryCatch (hs.withoutTypes hwfE) (hs.wellFormed hwf) he (hfe.substTys s) hh (hfh.substTys s)

/-- A tuple's element, instantiated. -/
theorem HasType.elem_substTys {Γ : Ctx} {fx : Effects} {e : Expr} {τs : List Ty} {f : Name}
    {τ : Ty} (h : HasType D scope' Γ fx e ((Ty.tuple τs).substTys s))
    (hf : (positions τs).lookup f = some τ) : HasType D scope' Γ fx (.field e f) (τ.substTys s) := by
  simp only [Ty.substTys, substTyList_eq_map] at h
  exact .elem h (by unfold positions at hf ⊢; rw [lookup_positionsFrom_map, hf]; rfl)

/-- A variant literal, instantiated, from its instantiated payload; payload
types name no type parameter. -/
theorem HasType.variant_substTys (hD : D.WellFormed) {Γ : Ctx} {fx : Effects} {T C : Name}
    {t : VariantDecl} {τs : List Ty} {es : List Expr} (hT : D.variant? T = some t)
    (hC : t.ctors.lookup C = some τs)
    (h : ExprsFit D scope' Γ fx (substExprTys s es) (τs.map (Ty.substTys s))) :
    HasType D scope' Γ fx ((Expr.variant T C es).substTys s) ((Ty.variant T).substTys s) := by
  rw [List.map_congr_left fun τ hτ => Ty.substTys_of_params
    (hD.payloadParams hT _ (mem_of_lookup hC) τ hτ) s, List.map_id'] at h
  exact .variant hT hC h

/-- A list literal, instantiated, from its instantiated elements. -/
theorem HasType.list_substTys (hs : s.Fits D scope scope') {Γ : Ctx} {fx : Effects} {τ : Ty}
    {es : List Expr} (hwf : τ.WellFormed scope)
    (h : ExprsFit D scope' Γ fx (substExprTys s es) ((List.replicate es.length τ).map (Ty.substTys s))) :
    HasType D scope' Γ fx ((Expr.list τ es).substTys s) ((Ty.list τ).substTys s) := by
  rw [List.map_replicate, ← length_substExprTys s] at h
  exact .list (hs.wellFormed hwf) h

/-- A field read, instantiated; field types name no type parameter. -/
theorem HasType.field_substTys (hD : D.WellFormed) {Γ : Ctx} {fx : Effects} {e : Expr} {R f : Name}
    {r : RecordDecl} {τ : Ty} (h : HasType D scope' Γ fx e (.record R)) (hR : D.record? R = some r)
    (hf : r.fields.lookup f = some τ) : HasType D scope' Γ fx (.field e f) (τ.substTys s) := by
  rw [Ty.substTys_of_params (hD.fieldParams hR _ (mem_of_lookup hf))]
  exact .field h hR hf

/-- A `raise`, instantiated; the row's error type names no type parameter. -/
theorem HasType.raise_substTys {Γ : Ctx} {fx : Effects} {e : Expr} {E σ : Ty}
    (hE : fx.row.raise = some E) (hfx : fx.row.ParamFree)
    (h : HasType D scope' Γ fx e (σ.substTys s)) (hfit : Fits σ E) :
    HasType D scope' Γ fx (.raise e) .never := by
  have hfit' := hfit.substTys s
  rw [Ty.substTys_of_params (hfx E hE)] at hfit'
  exact .raise hE h hfit'

/-- An assignment, instantiated, from its instantiated place and value. -/
theorem HasType.assign_substTys {Γ : Ctx} {fx : Effects} {p : Place} {e : Expr} {τ σ : Ty}
    (hp : PlaceFits D scope' Γ fx (p.substTys s) (τ.substTys s))
    (he : HasType D scope' Γ fx (e.substTys s) (σ.substTys s)) (hfit : Fits σ τ) :
    HasType D scope' Γ fx ((Expr.assign p e).substTys s) .unit := by
  rw [Expr.substTys_assign]
  exact .assign hp he (hfit.substTys s)

mutual

/-- **Instantiation**: a derivation of a body, with ground types for its type
parameters that meet their bounds, is a derivation of the instance, at the
instantiated types. -/
theorem HasType.substTys (hD : D.WellFormed) (hs : s.Fits D scope scope') :
    ∀ {Γ fx e τ}, HasType D scope Γ fx e τ → fx.row.ParamFree →
      HasType D scope' (Γ.substTys s) (fx.substTys s) (e.substTys s) (τ.substTys s)
  | _, _, _, _, .var h, _ => .var (Ctx.lookup_substTys s h)
  | _, _, _, _, .int h, _ => .int h
  | _, _, _, _, .bool, _ => .bool
  | _, _, _, _, .unit, _ => .unit
  | _, _, _, _, .record hR hperm hf, hfx =>
    .record hR (by rw [fst_substFieldTys]; exact hperm)
      (FieldsFit.substTys hD hs hf hfx (hD.fieldParams hR))
  | _, _, _, _, .variant hT hC hp, hfx =>
    HasType.variant_substTys hD hT hC (ExprsFit.substTys hD hs hp hfx)
  | _, _, _, _, .list hwf hes, hfx => HasType.list_substTys hs hwf (ExprsFit.substTys hD hs hes hfx)
  | _, _, _, _, .op ho hes, hfx => .op (ho.substTys hs.ground) (ExprsFit.substTys hD hs hes hfx)
  | _, _, _, _, .view ho hes, hfx => .view (ho.substTys hs.ground) (ExprsFit.substTys hD hs hes hfx)
  | _, _, _, _, .field he hR hf, hfx => HasType.field_substTys hD (HasType.substTys hD hs he hfx) hR hf
  | _, _, _, _, .elem he hf, hfx => HasType.elem_substTys (HasType.substTys hD hs he hfx) hf
  | _, _, _, _, .index he hi hfit, hfx =>
    .index (HasType.substTys hD hs he hfx) (HasType.substTys hD hs hi hfx) (hfit.substTys s)
  | _, _, _, _, .fnRef hd hlen hinst hres hwf hpass htys, _ =>
    HasType.fnRef_substTys hD hs hd hlen hinst hres hwf hpass htys
  | _, _, _, _, .method ht hm hc hwf hsat, _ => HasType.method_substTys hD hs ht hm hc hwf hsat
  | _, _, _, _, .closure (ρ := ρ) hnd hpt hwf hb hfit, _ => by
    have h := HasType.substTys hD hs hb (hwf.2.2 ρ (by simp [Ty.rows, Row.mem_rows_self]))
    rw [Ctx.params_substTys, Ctx.freeze_substTys] at h
    exact HasType.closure_substTys hs hnd hpt hwf h hfit
  | _, _, _, _, .call hc ha hallow, hfx =>
    .call (HasType.substTys hD hs hc hfx) (ArgsFit.substTys hD hs ha hfx) ((hs.callAllowed hallow).substTys_effects s)
  | _, _, _, _, .letIn hwf hi hfit hb, hfx =>
    .letIn (hs.wellFormed hwf) (HasType.substTys hD hs hi hfx) (hfit.substTys s)
      (HasType.substTys hD hs hb hfx)
  | _, _, _, _, .varIn hwf hi hfit hb, hfx =>
    .varIn (hs.wellFormed hwf) (HasType.substTys hD hs hi hfx) (hfit.substTys s)
      (HasType.substTys hD hs hb hfx)
  | _, _, _, _, .held (ns := ns) hnd hwf hes hb, hfx => by
    have hes' := ExprsFit.substTys hD hs hes hfx
    simp only [List.map_map, Function.comp_def, Ty.substTys] at hes'
    refine .held (by simpa [Function.comp_def] using hnd) (fun p hp => ?_) (by simpa [Function.comp_def] using hes')
      (Ctx.holding_substTys s ns _ ▸ HasType.substTys hD hs hb hfx)
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact hs.wellFormed (hwf q hq)
  | _, _, _, _, .assign hp he hfit, hfx =>
    HasType.assign_substTys (PlaceFits.substTys hD hs hp hfx) (HasType.substTys hD hs he hfx) hfit
  | _, _, _, _, .seq ha hfit hb, hfx =>
    .seq (HasType.substTys hD hs ha hfx) (hfit.substTys s) (HasType.substTys hD hs hb hfx)
  | _, _, _, _, .if hwf hc hfc ha hfa hb hfb, hfx =>
    .if (hs.wellFormed hwf) (HasType.substTys hD hs hc hfx) (hfc.substTys s)
      (HasType.substTys hD hs ha hfx) (hfa.substTys s) (HasType.substTys hD hs hb hfx) (hfb.substTys s)
  | _, _, _, _, .match hwf he hx ha, hfx =>
    .match (hs.wellFormed hwf) (HasType.substTys hD hs he hfx)
      (by rw [armRows_substTys]; exact hx.substTys s hD) (ArmsFit.substTys hD hs ha hfx)
  | _, _, _, _, .for hwf he hb hfit, hfx =>
    .for (hs.wellFormed hwf) (HasType.substTys hD hs he hfx) (HasType.substTys hD hs hb hfx)
      (hfit.substTys s)
  | _, _, _, _, .raise hE he hfit, hfx => HasType.raise_substTys hE hfx (HasType.substTys hD hs he hfx) hfit
  | _, _, _, _, .try he, hfx => .try (HasType.substTys hD hs he hfx)
  | _, _, _, _, .tryCatch hwfE hwf he hfe hh hfh, hfx =>
    HasType.tryCatch_substTys hs hwfE hwf
      (HasType.substTys hD hs he fun _ h' => by cases h'; exact hwfE.params_nil) hfe
      (HasType.substTys hD hs hh hfx) hfh
  | _, _, _, _, .while hc hfc hb hfb, hfx =>
    .while (HasType.substTys hD hs hc hfx) (hfc.substTys s) (HasType.substTys hD hs hb hfx)
      (hfb.substTys s)
  | _, _, _, _, .loopBreaks hb hfb, hfx =>
    .loopBreaks (HasType.substTys hD hs hb hfx) (hfb.substTys s)
  | _, _, _, _, .loopForever hb hfb, hfx =>
    .loopForever (HasType.substTys hD hs hb hfx) (hfb.substTys s)
  | _, _, _, _, .break h, _ => .break h
  | _, _, _, _, .continue h, _ => .continue h
  | _, _, _, _, .return he hfit, hfx => .return (HasType.substTys hD hs he hfx) (hfit.substTys s)
  | _, _, _, _, .perform hne hop hA hB hm he hfit, hfx => by
    have h := hfit.substTys s
    rw [Ty.substTys_of_params hA.2.1] at h
    rw [Ty.substTys_of_params hB.2.1]
    exact .perform hne hop hA hB hm (HasType.substTys hD hs he hfx) h
  | _, _, _, _, .resume hr hB hR he hfit, hfx => by
    have h := hfit.substTys s
    rw [Ty.substTys_of_params hB.2.1] at h
    rw [Ty.substTys_of_params hR.2.1]
    exact .resume hr hB hR (HasType.substTys hD hs he hfx) h
  | _, _, _, _, .withH hE heff hh hr hfs hb, hfx =>
    .withH hE heff (HasType.substTys hD hs hh hfx) hr (hfs.substTys hs) (HasType.substTys hD hs hb hfx)
  | _, _, _, _, .withControl hE heff hh hr hfs hb hfit hg, hfx => by
    have h := hfit.substTys s
    rw [Ty.substTys_of_params hg.2.1] at h ⊢
    exact .withControl hE heff (HasType.substTys hD hs hh hfx) hr (hfs.substTys hs)
      (HasType.substTys hD hs hb hfx) h hg

theorem ExprsFit.substTys (hD : D.WellFormed) (hs : s.Fits D scope scope') :
    ∀ {Γ fx es τs}, ExprsFit D scope Γ fx es τs → fx.row.ParamFree →
      ExprsFit D scope' (Γ.substTys s) (fx.substTys s) (substExprTys s es) (τs.map (Ty.substTys s))
  | _, _, _, _, .nil, _ => .nil
  | _, _, _, _, .cons he hfit hes, hfx =>
    .cons (HasType.substTys hD hs he hfx) (hfit.substTys s) (ExprsFit.substTys hD hs hes hfx)

theorem FieldsFit.substTys (hD : D.WellFormed) (hs : s.Fits D scope scope') :
    ∀ {Γ fx fields declared}, FieldsFit D scope Γ fx fields declared → fx.row.ParamFree →
      (∀ p ∈ declared, p.2.params = []) →
      FieldsFit D scope' (Γ.substTys s) (fx.substTys s) (substFieldTys s fields) declared
  | _, _, _, _, .nil, _, _ => .nil
  | _, _, _, _, .cons hl he hfit hfs, hfx, hc => by
    have h := hfit.substTys s
    rw [Ty.substTys_of_params (hc _ (mem_of_lookup hl))] at h
    exact .cons hl (HasType.substTys hD hs he hfx) h (FieldsFit.substTys hD hs hfs hfx hc)

theorem ArgsFit.substTys (hD : D.WellFormed) (hs : s.Fits D scope scope') :
    ∀ {Γ fx args ps}, ArgsFit D scope Γ fx args ps → fx.row.ParamFree →
      ArgsFit D scope' (Γ.substTys s) (fx.substTys s) (substArgTys s args) (substParamTys s ps)
  | _, _, _, _, .nil, _ => .nil
  | _, _, _, _, .value hm he hfit has, hfx =>
    .value hm (HasType.substTys hD hs he hfx) (hfit.substTys s) (ArgsFit.substTys hD hs has hfx)
  | _, _, _, _, .inout hp has, hfx => by
    have hp' := PlaceFits.substTys hD hs hp hfx
    have has' := ArgsFit.substTys hD hs has hfx
    rw [substArgTys_inout]
    exact .inout hp' has'

theorem PlaceFits.substTys (hD : D.WellFormed) (hs : s.Fits D scope scope') :
    ∀ {Γ fx p τ}, PlaceFits D scope Γ fx p τ → fx.row.ParamFree →
      PlaceFits D scope' (Γ.substTys s) (fx.substTys s) (p.substTys s) (τ.substTys s)
  | _, _, _, _, .mk hl hp, hfx => .mk (Ctx.lookup_substTys s hl) (PathFits.substTys hD hs hp hfx)

theorem PathFits.substTys (hD : D.WellFormed) (hs : s.Fits D scope scope') :
    ∀ {Γ fx σ path τ}, PathFits D scope Γ fx σ path τ → fx.row.ParamFree →
      PathFits D scope' (Γ.substTys s) (fx.substTys s) (σ.substTys s) (substPathTys s path) (τ.substTys s)
  | _, _, _, _, _, .nil, _ => .nil
  | _, _, _, _, _, .field hR hf hp, hfx => by
    have h := PathFits.substTys hD hs hp hfx
    rw [Ty.substTys_of_params (hD.fieldParams hR _ (mem_of_lookup hf))] at h
    exact .field hR hf h
  | _, _, _, _, _, .index hi hfit hp, hfx =>
    .index (HasType.substTys hD hs hi hfx) (hfit.substTys s) (PathFits.substTys hD hs hp hfx)
  | _, _, _, _, _, .elem (τs := τs) hf hp, hfx => by
    have h := PathFits.substTys hD hs hp hfx
    show PathFits D scope' _ _ (.tuple (substTyList s τs)) _ _
    rw [substTyList_eq_map]
    exact .elem (by unfold positions at hf ⊢; rw [lookup_positionsFrom_map, hf]; rfl) h

theorem ArmsFit.substTys (hD : D.WellFormed) (hs : s.Fits D scope scope') :
    ∀ {Γ fx arms σ τ}, ArmsFit D scope Γ fx arms σ τ → fx.row.ParamFree →
      ArmsFit D scope' (Γ.substTys s) (fx.substTys s) (substArmTys s arms) (σ.substTys s) (τ.substTys s)
  | _, _, _, _, _, .nil, _ => .nil
  | _, _, _, _, _, .cons hp hbs hnd hb hfit has, hfx => by
    have hb' := HasType.substTys hD hs hb hfx
    rw [Ctx.bindAll_substTys_map] at hb'
    rw [substArmTys_cons]
    exact .cons (hp.substTys s hD) hbs hnd hb' (hfit.substTys s) (ArmsFit.substTys hD hs has hfx)

end

end

/-! ## Instances of functions -/

/-- The scope of an instance of a body: its type parameters instantiated. -/
def RowScope.instantiated (s : RowScope) : RowScope := { s with types := [] }

theorem Forall₂.exists_of_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall₂ R xs ys → ∀ {y : β}, y ∈ ys → ∃ x ∈ xs, R x y
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons hxy h, _, hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, hxy⟩
    · obtain ⟨x, hx, hr⟩ := Forall₂.exists_of_mem_right h hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩

/-- The type a parameter named once is given is the one at its position. -/
theorem Forall₂.lookup_zip {β : Type} {R : TypeParam → β → Prop} :
    ∀ {ps : List TypeParam} {bs : List β}, Forall₂ R ps bs → (ps.map TypeParam.name).Nodup →
      ∀ {p : TypeParam}, p ∈ ps → ∃ b, ((ps.map TypeParam.name).zip bs).lookup p.name = some b ∧ R p b
  | _, _, .nil, _, _, h => nomatch h
  | _, _, .cons (x := p') (y := b') hr h, hnd, p, hp => by
    simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons]
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨b', by simp, hr⟩
    · have hne : (p.name == p'.name) = false := by
        have := (List.nodup_cons.1 hnd).1
        simp only [beq_eq_false_iff_ne]
        rintro heq
        exact this (heq ▸ List.mem_map_of_mem hp)
      rw [hne]
      exact Forall₂.lookup_zip h (List.nodup_cons.1 hnd).2 hp

section

variable {D : Decls}

/-- Type arguments that fit in a scope with no type parameters are ground and
meet their bounds anywhere. -/
theorem TypeArgsFit.fits (hD : D.WellFormed) {d : FnDecl} (hd : d ∈ D.fns) {scope : RowScope}
    (hscope : scope.types = []) {types : List Ty} (h : TypeArgsFit D scope d.typeParams types) :
    (d.typeArgs types).Fits D d.scope d.scope.instantiated := by
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun _ h => h, fun _ _ h => h, fun _ _ h => h⟩
  · obtain ⟨-, hτ⟩ := List.of_mem_zip hp
    obtain ⟨_, _, hc, hw, _⟩ := Forall₂.exists_of_mem_right h hτ
    exact Ty.ground_of_wellFormed hc hw hscope
  · obtain ⟨τ, hl, _, _, hb⟩ := Forall₂.lookup_zip h (hD.typeParams d hd) hp
    refine ⟨τ, hl, fun B hB => ?_⟩
    rcases hb B hB with ⟨q, hq, _⟩ | hi
    · rw [hscope] at hq
      exact nomatch hq
    · exact .inr hi

/-- Closed type arguments have no row variable for an instantiation to replace. -/
theorem TypeArgsFit.substRows {scope : RowScope} {ps : List TypeParam} {τs : List Ty}
    (h : TypeArgsFit D scope ps τs) (θ : RowSubst) : substTysRows θ τs = τs := by
  unfold TypeArgsFit at h
  induction h with
  | nil => rfl
  | cons hx _ ih => rw [substTysRows, Ty.substRows_of_closed θ _ hx.1, ih]

/-- A function's row names no type parameter. -/
theorem Decls.WellFormed.rowParamFree (hD : D.WellFormed) {d : FnDecl} (hd : d ∈ D.fns) :
    d.row.ParamFree :=
  (hD.signatures d hd).2.2 d.row (by simp [FnDecl.type, Ty.rows, Row.mem_rows_self])

/-- A function's body, instantiated with type arguments that fit, checks
against the instantiated signature in the scope of the instance. -/
theorem FnDecl.WellTyped.instance (hD : D.WellFormed) {d : FnDecl} (hd : d ∈ D.fns)
    (h : d.WellTyped D d.scope) {δ : TySubst} (hδ : δ.Fits D d.scope d.scope.instantiated) :
    ∃ σ, HasType D d.scope.instantiated (Ctx.params [] (d.params.map (Param.substTys δ)))
      (Effects.body d.row (d.result.substTys δ)) (d.body.substTys δ) σ ∧ Fits σ (d.result.substTys δ) := by
  obtain ⟨σ, hb, hfit⟩ := h
  have h := HasType.substTys hD hδ hb (hD.rowParamFree hd)
  rw [Ctx.params_substTys] at h
  exact ⟨_, h, hfit.substTys _⟩

end

end Stilt
