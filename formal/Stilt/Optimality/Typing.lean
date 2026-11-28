import Stilt.Optimality.Witness

/-!
# The witness is well typed

The witness of `Stilt.Optimality.Witness` checks: its declarations are well
formed, the callee's body checks against its signature, and `main` checks
against `()` and the pure row, as program.main requires. Each place of the
call is a `var` of the record type with the greatest budget, followed by
fields that type it with its parameter's type (expressions.inout-arguments; effects.inout-function-arguments), and `p_a.extra.v` and `p_b.v` are `i64`.
-/

namespace Stilt.Optimality

variable {ss : List Shape} {a b : Nat} {extra : List Name}

/-- A context of parameters: each parameter's binding, the last one first,
before the context it extends (modes.what-can-be-modified). -/
theorem Ctx.params_eq :
    ∀ (Γ : Ctx) (ps : List Param),
      Ctx.params Γ ps =
        (ps.map fun p => (p.name, (⟨p.type, p.mode = .inout⟩ : Binding))).reverse ++ Γ
  | _, [] => rfl
  | Γ, p :: ps => by
    simp only [Ctx.params, List.foldl_cons] at Ctx.params_eq ⊢
    rw [Ctx.params_eq]
    simp [Ctx.bind]

/-- Each parameter of the callee is a mutable binding of its shape's type. -/
theorem lookup_params {i : Nat} (hi : i < ss.length) :
    (Ctx.params [] (params ss)).lookup (nameOf 'p' i) = some ⟨paramTy ss ss[i], true⟩ := by
  refine lookup_named (fun s => (⟨paramTy ss s, true⟩ : Binding)) hi fun e => ?_
  rw [Ctx.params_eq, List.append_nil, List.mem_reverse, params, map_mapIdx]
  simp

/-- The record literal of a budget has that budget's type (expressions.struct-literal-fields). -/
theorem lit_hasType {D : Decls} {F : List Name} {v : Name} {K : Nat}
    (hD : D.records = recDecls F v K) (hv : v ∉ F) {scope : RowScope} {Γ : Ctx}
    {fx : Effects} : ∀ {b : Nat}, b ≤ K → HasType D scope Γ fx (lit F v b) (recTy b)
  | 0, hb => .record (record?_recName hD hb) rfl (fun _ h => nomatch h)
      (.of_eq (by simp [recDecl, recFields]))
      (by rw [RecordDecl.fieldsAt_nil]
          exact .cons (lookup_recFields_leaf (F := F) 0) (.int (by decide)) (.refl _) .nil)
  | b + 1, hb => by
    refine .record (record?_recName hD hb) rfl (fun _ h => nomatch h)
      (.of_eq (by simp [recDecl, recFields])) ?_
    rw [RecordDecl.fieldsAt_nil]
    refine .cons (lookup_recFields_leaf (F := F) (b + 1)) (.int (by decide)) (.refl _) ?_
    have hlit := lit_hasType hD hv (scope := scope) (Γ := Γ) (fx := fx) (b := b) (by omega)
    suffices ∀ G : List Name, (∀ f ∈ G, f ∈ F) →
        FieldsFit D scope Γ fx (G.map fun f => (f, lit F v b)) (recFields F v (b + 1)) from
      this F fun _ h => h
    intro G hG
    induction G with
    | nil => exact .nil
    | cons f G ih =>
      exact .cons (lookup_recFields_field hv (hG f List.mem_cons_self) b) hlit (.refl _)
        (ih fun g hg => hG g (List.mem_cons_of_mem _ hg))

/-- The variables of `main`: under them, each name is a mutable binding of
their type (values.let-and-var; modes.what-can-be-modified). -/
theorem vars_hasType {D : Decls} {scope : RowScope} {fx : Effects} {τ σ : Ty} {init e : Expr}
    (hwf : τ.WellFormed scope) (hinit : ∀ Γ, HasType D scope Γ fx init τ) :
    ∀ (xs ys : List Name) (Γ : Ctx), (∀ y ∈ ys, Γ.lookup y = some ⟨τ, true⟩) →
      (∀ Γ', (∀ y ∈ ys ++ xs, Γ'.lookup y = some ⟨τ, true⟩) →
        HasType D scope Γ' fx e σ) →
      HasType D scope Γ fx (vars τ init xs e) σ
  | [], ys, Γ, hΓ, he => he Γ (by simpa using hΓ)
  | x :: xs, ys, Γ, hΓ, he => by
    refine .varIn hwf (hinit Γ) (.refl _) (vars_hasType hwf hinit xs (ys ++ [x]) _ ?_ ?_)
    · intro y hy
      by_cases hyx : y = x
      · subst hyx
        simp [Ctx.lookup, Ctx.bind]
      · have hy' : y ∈ ys := by simpa [hyx] using hy
        simpa [Ctx.lookup, Ctx.bind, lookup_cons_ne hyx] using hΓ y hy'
    · simpa using he

theorem recTy_wellFormed (b : Nat) (scope : RowScope) : (recTy b).WellFormed scope :=
  let h := (Head.record (recName b)).ground_type
  Ty.Closed.wellFormed h.1 h.2.1 h.2.2 (Head.viewsViewable_type _) scope

theorem i64_wellFormed (scope : RowScope) : Ty.i64.WellFormed scope :=
  let h := (Head.int .i64).ground_type
  Ty.Closed.wellFormed h.1 h.2.1 h.2.2 (Head.viewsViewable_type _) scope

theorem concrete_recFields {F : List Name} {v : Name} :
    ∀ (b : Nat), ∀ f ∈ recFields F v b, f.2.Concrete
  | 0, f, h => by
    simp only [recFields, List.mem_singleton] at h
    subst h
    exact (Head.int .i64).ground_type.2
  | b + 1, f, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact (Head.int .i64).ground_type.2
    · obtain ⟨g, -, rfl⟩ := List.mem_map.1 h
      exact (Head.record (recName b)).ground_type.2

/-- `let r: i64 = [0][e]` has type `()` when `e` is an `i64` (values.let-and-var;
std.lists). -/
theorem probe_hasType {D : Decls} {scope : RowScope} {Γ : Ctx} {fx : Effects} {e : Expr}
    (he : HasType D scope Γ fx e .i64) :
    HasType D scope Γ fx (.letIn "r" .i64 (probe e) .unit) .unit :=
  .letIn (i64_wellFormed _)
    (.index (.list (i64_wellFormed _) (.cons (.int (by decide)) (.refl _) .nil)) he (.refl _)) (.refl _) .unit

variable (ss a b extra)

theorem substRows_paramTy (σ : RowSubst) (s : Shape) :
    (paramTy ss s).substRows σ = paramTy ss s := by
  simp [paramTy, recTy, Ty.substRows, substTysRows]

theorem paramRows_shapes : ∀ ts : List Shape,
    paramRows (ts.map fun s => (Mode.inout, paramTy ss s)) = []
  | [] => rfl
  | _ :: ts => by simpa [paramRows, paramTy, recTy, Ty.rows, tysRows] using paramRows_shapes ts

theorem paramRows_params : paramRows ((params ss).map Param.sig) = [] := by
  rw [map_sig_params]
  exact paramRows_shapes ss ss

theorem callee_type_subst :
    (callee ss a b extra).type.substRows [] =
      .fn (ss.map fun s => (.inout, paramTy ss s)) .unit Row.pure := by
  simp only [callee, FnDecl.type, Ty.substRows, map_sig_params]
  have : ∀ ts : List Shape,
      substParamRows [] (ts.map fun s => (Mode.inout, paramTy ss s)) =
        ts.map fun s => (Mode.inout, paramTy ss s) := by
    intro ts
    induction ts with
    | nil => rfl
    | cons t ts ih => simp only [List.map_cons, substParamRows, ih, substRows_paramTy]
  simp [this, Row.substRows, Row.pure]

/-- The callee's type, whose parameter types are record types and whose rows
are pure, is well formed anywhere. -/
theorem shapes_wellFormed (scope : RowScope) :
    (Ty.fn (ss.map fun s => (Mode.inout, paramTy ss s)) .unit Row.pure).WellFormed scope := by
  have hp : ∀ ts : List Shape, paramTysParams (ts.map fun s => (Mode.inout, paramTy ss s)) = [] := by
    intro ts
    induction ts with
    | nil => rfl
    | cons t ts ih => simpa [paramTysParams, paramTy, recTy, Ty.params, tysParams] using ih
  have hrows : ∀ ρ ∈ (Ty.fn (ss.map fun s => (Mode.inout, paramTy ss s)) .unit Row.pure).rows,
      ρ = Row.pure := fun ρ hρ => by
    simpa [Ty.rows, paramRows_shapes, Row.rows, Row.pure] using hρ
  have hv : ∀ ts : List Shape, paramTysViews (ts.map fun s => (Mode.inout, paramTy ss s)) = [] := by
    intro ts
    induction ts with
    | nil => rfl
    | cons t ts ih => simpa [paramTysViews, paramTy, recTy, Ty.views] using ih
  refine ⟨fun ρ hρ w hw => ?_, fun T hT => ?_, fun ρ hρ E hE => ?_, fun υ hυ => ?_⟩
  · rw [hrows ρ hρ] at hw
    cases hw
  · simp [Ty.params, hp] at hT
  · rw [hrows ρ hρ] at hE
    cases hE
  · simp [Ty.views, hv, Row.views, Row.pure] at hυ

theorem decls_wellFormed : (decls ss a b extra).WellFormed where
  recordNames := nodup_recNames _
  fieldNames := fun r hr => by
    obtain ⟨b, -, rfl⟩ := mem_recDecls hr
    exact nodup_recFields leafName_not_mem nodup_fieldNames b
  fieldsClosed := fun r hr => by
    obtain ⟨b, -, rfl⟩ := mem_recDecls hr
    exact closed_recFields b
  fieldRows := fun r hr f hf => by
    obtain ⟨b, -, rfl⟩ := mem_recDecls hr
    exact (concrete_recFields b f hf).2
  variantNames := .nil
  ctorNames := fun _ h => nomatch h
  payloadsClosed := fun _ h => nomatch h
  payloadRows := fun _ h => nomatch h
  paramsDeclared := ⟨fun r hr f hf T hT => (by
    obtain ⟨b, -, rfl⟩ := mem_recDecls hr
    rw [(concrete_recFields b f hf).1] at hT
    exact nomatch hT), fun _ h => nomatch h⟩
  typeParams := fun d hd => by
    simp only [decls, Decls.fns_mk, List.mem_singleton] at hd
    subst hd
    exact .nil
  traits := fun _ h => nomatch h
  traitImpls := fun _ h => nomatch h
  implFields := fun _ h => nomatch h
  typeNames := by simpa [Decls.typeNames, decls] using nodup_recNames _
  effectOps := fun _ h => nomatch h
  coherent := .nil
  implMembers := fun _ h => nomatch h
  nameClashes := fun _ h => nomatch h
  boundArgs := fun d hd p hp => by
    simp only [decls, Decls.fns_mk, List.mem_singleton] at hd
    subst hd
    exact nomatch hp
  memberTypes := fun d hd p hp => by
    simp only [decls, Decls.fns_mk, List.mem_singleton] at hd
    subst hd
    exact nomatch hp
  effectsDeclared := by
    refine ⟨fun r hr f hf ρ hρ => ?_, fun _ h => (nomatch h), fun d hd ρ hρ E hE => ?_,
      fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
    · obtain ⟨b, -, rfl⟩ := mem_recDecls hr
      have hf' : f.2.rows = [] := by
        cases b with
        | zero =>
          simp only [recDecl, recFields, List.mem_singleton] at hf
          subst hf
          rfl
        | succ b =>
          simp only [recDecl, recFields, List.mem_cons, List.mem_map] at hf
          rcases hf with rfl | ⟨g, -, rfl⟩ <;> rfl
      rw [hf'] at hρ
      exact nomatch hρ
    · simp only [decls, Decls.fns_mk, List.mem_singleton] at hd
      subst hd
      change ρ ∈ (Ty.fn ((params ss).map Param.sig) .unit Row.pure).rows at hρ
      rw [map_sig_params] at hρ
      have : ρ = Row.pure := by simpa [Ty.rows, paramRows_shapes, Row.rows, Row.pure] using hρ
      subst this
      exact nomatch hE
  fnNames := by simp [decls, callee]
  constNames := by simp [decls]
  constTypes := fun _ h => by simp [decls] at h
  consts := fun _ _ _ h => by simp [decls] at h
  paramNames := fun d hd => by
    simp only [decls, Decls.fns_mk, List.mem_singleton] at hd
    subst hd
    exact nodup_paramNames
  rowParams := fun d hd => by
    simp only [decls, Decls.fns_mk, List.mem_singleton] at hd
    subst hd
    exact .nil
  signatures := fun d hd => by
    simp only [decls, Decls.fns_mk, List.mem_singleton] at hd
    subst hd
    show (Ty.fn ((params ss).map Param.sig) .unit Row.pure).WellFormed _
    rw [map_sig_params]
    exact shapes_wellFormed ss _
  implicitRows := fun d hd => by
    simp only [decls, Decls.fns_mk, List.mem_singleton] at hd
    subst hd
    refine FnDecl.implicitRows_of_none (fun p hp => ?_) fun ρ hρ => ?_
    · simp only [callee, params, List.mem_mapIdx] at hp
      obtain ⟨_, _, rfl⟩ := hp
      rfl
    · simp [callee, FnDecl.type, Ty.rows, paramRows_params, Row.rows, Row.pure] at hρ
      simp [hρ]
  receivers := Decls.receivers_of_nil rfl fun d hd p hp => by
    simp only [decls, List.mem_singleton] at hd
    subst hd
    simp only [callee, params, List.mem_mapIdx] at hp
    obtain ⟨i, _, rfl⟩ := hp
    exact nameOf_ne_selfName (by decide) i

/-- The callee's body checks against its signature: `p_b.v` is an `i64` that
the body may modify, since `p_b` is an `inout` parameter (modes.what-can-be-modified),
`p_a.extra.v` is an `i64`, and the body has type `()`. -/
theorem callee_wellTyped (h : Overlap ss a b extra) :
    (callee ss a b extra).WellTyped (decls ss a b extra) (callee ss a b extra).scope := by
  have hD := decls_records ss a b extra
  have := h.lt_a
  have := h.lt_b
  have hb : ss[b] ∈ ss := List.getElem_mem h.lt_b
  have hlen : ss[a].fields.length + extra.length = ss[b].fields.length := by
    simpa using congrArg List.length h.fields
  have hdepth := length_le_depth hb
  have hassign : HasType (decls ss a b extra) (callee ss a b extra).scope
      (Ctx.params [] (params ss)) ⟨Row.pure, false, false, (callee ss a b extra).result, false, false⟩
      (.assign ⟨nameOf 'p' b, [.field (leafName ss)]⟩ (.int 1)) .unit :=
    .assign (.mk (lookup_params h.lt_b) (fieldPath_leaf hD (Nat.sub_le _ _)).pathFits) (.int (by decide))
      (.refl _)
  have hpath := fieldPath_recTy hD leafName_not_mem (fs := extra)
    (b := depth ss - ss[a].fields.length)
    (fun f hf => mem_fieldNames hb (h.fields ▸ List.mem_append_right _ hf)) (by omega)
    (Nat.sub_le _ _)
  have hproj := hpath.hasType (scope := (callee ss a b extra).scope)
    (fx := ⟨Row.pure, false, false, (callee ss a b extra).result, false, false⟩) (.var (lookup_params h.lt_a))
  refine ⟨.unit, .seq hassign (.refl _)
    (probe_hasType (.field hproj (record?_recName hD (by omega)) rfl ?_)), .refl _⟩
  rw [RecordDecl.fieldsAt_nil]
  exact lookup_recFields_leaf _

/-- `main` checks against `()` and the pure row: each place of the call is a
`var` with fields that give it its parameter's type exactly (expressions.inout-arguments;
effects.inout-function-arguments), and the callee's row is pure (effects.inference). -/
theorem main_hasType :
    HasType (decls ss a b extra) .closed [] ⟨Row.pure, false, false, .unit, false, false⟩ (main ss) .unit := by
  have hD := decls_records ss a b extra
  refine vars_hasType (recTy_wellFormed _ _)
    (fun _ => lit_hasType hD leafName_not_mem (Nat.le_refl _)) (ss.map Shape.root) [] []
    (by simp) fun Γ hΓ => ?_
  have hcallee := HasType.fnRef (scope := .closed) (Γ := Γ) (fx := ⟨Row.pure, false, false, .unit, false, false⟩)
    (types := []) (rows := []) (decls_fn? ss a b extra) rfl
    (Ty.instantiableBy_nil _) (fun _ h => nomatch h) ?_ (fun _ _ _ _ _ hl _ => nomatch hl) .nil
  · rw [show (callee ss a b extra).rowParams.zip [] = [] from rfl,
      show (callee ss a b extra).typeArgs [] = [] from rfl, Ty.substTys_nil,
      callee_type_subst] at hcallee
    have hargs : ∀ ts : List Shape, (∀ t ∈ ts, t ∈ ss) →
        ArgsFit (decls ss a b extra) .closed Γ ⟨Row.pure, false, false, .unit, false, false⟩ (ts.map placeArg)
          (ts.map fun s => (.inout, paramTy ss s)) := by
      intro ts hts
      induction ts with
      | nil => exact .nil
      | cons t ts ih =>
        have ht := hts t List.mem_cons_self
        have hroot : Γ.lookup t.root = some ⟨rootTy ss, true⟩ :=
          hΓ t.root (by simpa using ⟨t, ht, rfl⟩)
        have hpath := fieldPath_recTy hD leafName_not_mem (fs := t.fields) (b := depth ss)
          (fun f hf => mem_fieldNames ht hf) (length_le_depth ht) (Nat.le_refl _)
        exact .inout (.mk hroot hpath.pathFits) (ih fun u hu => hts u (List.mem_cons_of_mem _ hu))
    exact .call hcallee (hargs ss fun _ h => h)
      ⟨Row.Within.refl _, fun h => by simp at h, fun _ _ h => by simp at h, rfl⟩
  · rw [show (callee ss a b extra).rowParams.zip [] = [] from rfl,
      show (callee ss a b extra).typeArgs [] = [] from rfl, Ty.substTys_nil, callee_type_subst]
    exact shapes_wellFormed ss _

/-- The witness is well typed. -/
theorem witness_wellTyped (h : Overlap ss a b extra) : (witness ss a b extra).WellTyped where
  decls := decls_wellFormed ss a b extra
  fns := fun d hd => by
    simp only [witness, decls, Decls.fns_mk, List.mem_singleton] at hd
    subst hd
    exact (callee_wellTyped ss a b extra h).lenient
  closed := by
    intro ρ hρ
    simp [witness, Ty.rows, paramRows, Row.rows, Row.pure] at hρ
    subst hρ
    rfl
  unhandled := ⟨rfl, rfl⟩
  main := ⟨.unit, main_hasType ss a b extra, .refl _⟩
  noEscape := fun d hd => by
    simp only [witness, decls, Decls.fns_mk, List.mem_singleton] at hd
    subst hd
    refine FnDecl.noEscape_of_nil ?_
    simp only [FnDecl.nonEscaping, List.filterMap_eq_nil_iff, callee, params, List.mem_mapIdx]
    rintro _ ⟨_, _, rfl⟩
    rfl

end Stilt.Optimality
