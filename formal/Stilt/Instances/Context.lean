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
  covers : ∀ p ∈ scope.types, ∃ σ, s.lookup p.name = some σ ∧ ∀ B ∈ p.bounds, Satisfies D scope' σ B
  vars : ∀ v ∈ scope.vars, v ∈ scope'.vars
  pairs : ∀ v E, scope.pairs v E → scope'.pairs v E
  passOn : ∀ v E, scope.passOn v E → scope'.passOn v E

section

variable {D : Decls} {scope scope' : RowScope} {s : TySubst}

theorem TySubst.Fits.isSome (hs : s.Fits D scope scope') {p : TypeParam} (hp : p ∈ scope.types) :
    (s.lookup p.name).isSome := by
  obtain ⟨σ, hl, _⟩ := hs.covers p hp
  simp [hl]

theorem TySubst.Fits.wellFormed (hs : s.Fits D scope scope') {τ : Ty} (h : τ.WellFormed scope) :
    (τ.substTys s).WellFormed scope' :=
  h.substTys hs.ground hs.viewable (fun _ hp => hs.isSome hp) hs.vars

theorem TySubst.Fits.satisfies (hs : s.Fits D scope scope') {τ : Ty} {B : Name}
    (h : Satisfies D scope τ B) : Satisfies D scope' (τ.substTys s) B := by
  rcases h with ⟨p, hp, rfl, hB⟩ | ⟨h, hh, hi⟩
  · obtain ⟨σ, hl, hσ⟩ := hs.covers p hp
    simpa [Ty.substTys, hl] using hσ B hB
  · rw [Ty.eq_of_head? hh, Head.substTys_type]
    exact .inr ⟨h, by rw [← Ty.eq_of_head? hh]; exact hh, hi⟩

theorem TySubst.Fits.typeArgs (hs : s.Fits D scope scope') {ps : List TypeParam} {τs : List Ty}
    (h : TypeArgsFit D scope ps τs) : TypeArgsFit D scope' ps (τs.map (Ty.substTys s)) := by
  unfold TypeArgsFit at h ⊢
  induction h with
  | nil => exact .nil
  | cons hx _ ih =>
    exact .cons ⟨hx.1.substTys hs.ground, hs.wellFormed hx.2.1, fun B hB => hs.satisfies (hx.2.2 B hB)⟩ ih

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
      ⟨arm.pattern, arm.binders, arm.body.substTys s⟩ :: substArmTys s arms := by
  cases arm; rfl

/-- Instantiating a `match`'s arms leaves their patterns as they are. -/
theorem armRows_substTys (s : TySubst) : ∀ arms : List Arm,
    armRows (substArmTys s arms) = armRows arms
  | [] => rfl
  | ⟨_, _, _⟩ :: arms => by simp [armRows, substArmTys] at *; exact armRows_substTys s arms

theorem Forall₂.length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall₂ R xs ys → xs.length = ys.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [Forall₂.length_eq h]

end Stilt
