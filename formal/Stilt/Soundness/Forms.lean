import Stilt.Soundness.Cases
import Stilt.Soundness.Patterns
import Stilt.Selection

/-!
# Literals, `match` and `for`

The forms of expressions that build or take apart values of declared types.
A record literal gives each field once (expressions.struct-literal-fields), so the record it
builds holds every declared field, in the declared order, at its declared
type at the literal's type arguments. Fields and payloads have closed types
(effects.row-variables), so at arguments they read as their declared types at the
arguments read (declarations.type-parameters). A `match` runs the first arm whose pattern
matches and whose guard is true (patterns.match and patterns.guards), which its typing checked
against the scrutinee's type, and its arms without guards are exhaustive (patterns.algorithm
and patterns.guards-and-constants), so it always finds one. A
`for` loop runs a turn of its body for each element (expressions.for-iterables),
until a `break` ends it (expressions.break-and-continue).
-/

namespace Stilt

section

variable {D : Decls}

theorem ValuesAt.sem {η : REnv} (names : List Name) (args : List Ty) :
    ∀ {vs : List Value} {τs : List Ty}, (∀ τ ∈ τs, τ.Closed) →
      ValuesAt D η vs (τs.map (Ty.substTys (names.zip args))) →
      Values.Typed D vs τs (names.zip (closeTys η args))
  | [], [], _, _ => .nil
  | _ :: _, τ :: _, hc, .cons hv hvs =>
    .cons ((hc τ List.mem_cons_self).close_substTys names args η ▸ hv)
      (ValuesAt.sem names args (fun τ h => hc τ (List.mem_cons_of_mem _ h)) hvs)
  | [], _ :: _, _, h | _ :: _, [], _, h => nomatch h

theorem ValuesAt.replicate {η : REnv} {τ : Ty} :
    ∀ {vs : List Value} {k : Nat}, ValuesAt D η vs (List.replicate k τ) →
      ∀ v ∈ vs, Value.Typed D v (τ.close η)
  | [], _, _ => fun _ h => nomatch h
  | _ :: _, 0, h => nomatch h
  | _ :: _, _ + 1, .cons hv hvs => by
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact hv
    · exact ValuesAt.replicate hvs u hu

theorem WrittenAt.lookup {η : REnv} {declared : List (Name × Ty)} :
    ∀ {written : List (Name × Value)} {fields : List (Name × Expr)},
      WrittenAt D η declared written fields → written.map Prod.fst = fields.map Prod.fst ∧
        ∀ f v, written.lookup f = some v →
          ∃ τ, declared.lookup f = some τ ∧ Value.Typed D v (τ.close η)
  | _, _, .nil => ⟨rfl, fun _ _ h => nomatch h⟩
  | _, _, .cons (f := g) hl hv hrest => by
    obtain ⟨hnames, hlook⟩ := WrittenAt.lookup hrest
    refine ⟨by simp [hnames], fun f v h => ?_⟩
    by_cases hf : f = g
    · subst hf
      simp only [List.lookup_cons_self, Option.some.injEq] at h
      exact ⟨_, hl, h ▸ hv⟩
    · rw [lookup_cons_ne hf] at h
      exact hlook f v h

theorem List.lookup_of_mem_nodup {β : Type} :
    ∀ {l : List (Name × β)} {k : Name} {b : β}, (l.map Prod.fst).Nodup → (k, b) ∈ l →
      l.lookup k = some b
  | [], _, _, _, h => nomatch h
  | (k', b') :: l, k, b, hnd, h => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 h with h | h
    · cases h
      simp
    · have hk : k ≠ k' := fun hk => hnd.1 (hk ▸ List.mem_map_of_mem (f := Prod.fst) h)
      rw [lookup_cons_ne hk]
      exact List.lookup_of_mem_nodup hnd.2 h

theorem List.lookup_of_mem_map {β : Type} :
    ∀ {l : List (Name × β)} {k : Name}, k ∈ l.map Prod.fst → ∃ b, l.lookup k = some b
  | [], _, h => nomatch h
  | (k', b') :: l, k, h => by
    by_cases hk : k = k'
    · subst hk
      exact ⟨b', by simp⟩
    · rw [lookup_cons_ne hk]
      exact List.lookup_of_mem_map ((List.mem_cons.1 h).resolve_left hk)

/-- The fields of a record literal, looked up in the declared order, give the
record's fields at their declared types. -/
theorem WrittenAt.declare {η : REnv} {declared : List (Name × Ty)} {names : List Name}
    {args : List Ty} (hnd : (declared.map Prod.fst).Nodup) (hc : ∀ f ∈ declared, f.2.Closed)
    {written : List (Name × Value)} {fields : List (Name × Expr)}
    (hw : WrittenAt D η (declared.map (Prod.map id (Ty.substTys (names.zip args)))) written fields)
    (hperm : (fields.map Prod.fst).Perm (declared.map Prod.fst)) :
    ∀ l, (∀ x ∈ l, x ∈ declared) →
      ∃ fs, l.mapM (fun (f, _) => (written.lookup f).map (f, ·)) = some fs ∧
        Fields.Typed D fs l (names.zip (closeTys η args))
  | [], _ => ⟨[], rfl, .nil⟩
  | (f, τ) :: l, hl => by
    have hmem := hl (f, τ) List.mem_cons_self
    obtain ⟨hnames, hlook⟩ := hw.lookup
    have hf : f ∈ written.map Prod.fst := by
      rw [hnames]
      exact hperm.symm.mem_iff.1 (List.mem_map_of_mem (f := Prod.fst) hmem)
    obtain ⟨v, hv⟩ := List.lookup_of_mem_map hf
    obtain ⟨τ', hτ', hvt⟩ := hlook f v hv
    rw [lookup_map_snd, List.lookup_of_mem_nodup hnd hmem] at hτ'
    obtain rfl := Option.some.inj hτ'
    obtain ⟨fs, hfs, hft⟩ :=
      WrittenAt.declare hnd hc hw hperm l fun x h => hl x (List.mem_cons_of_mem _ h)
    refine ⟨(f, v) :: fs, by simp [List.mapM_cons, hv, hfs], .cons ?_ hft⟩
    exact (hc _ hmem).close_substTys names args η ▸ hvt

/-- The arms of a `match` bind the payload's values, the first one outermost,
as `Ctx.bindAll` binds their types. -/
theorem Eval.Ok.withVars {η : REnv} {X : Exits} {α : Type} {P : α → Prop}
    {m : Eval Copy.State α} :
    ∀ {Γ : Ctx} {xs : List Name} {vs : List Value} {τs : List Ty}, xs.length = τs.length →
      ValuesAt D η vs τs → Eval.Ok D (Γ.bindAll xs τs) η X P m →
      Eval.Ok D Γ η X P (Eval.withVars Copy.memory (xs.zip vs) m)
  | _, [], _, [], _, .nil, h => h
  | Γ, x :: _, _, τ :: _, hl, .cons hv hvs, h =>
    Eval.Ok.withVar (b := ⟨τ, false⟩) hv
      (Eval.Ok.withVars (Γ := Γ.bind x ⟨τ, false⟩) (by simpa using hl) hvs h)
  | _, [], _, _ :: _, hl, _, _ => nomatch hl
  | _, _ :: _, _, [], hl, _, _ => nomatch hl

theorem Eval.Ok.forEach {Γ : Ctx} {η : REnv} {X : Exits} {f : Value → Eval Copy.State Bool}
    {Q : Value → Prop} (hf : ∀ u, Q u → Eval.Ok D Γ η X (fun _ => True) (f u)) :
    ∀ {vs : List Value}, (∀ u ∈ vs, Q u) → Eval.Ok D Γ η X (fun _ => True) (Eval.forEach f vs)
  | [], _ => Eval.Ok.pure trivial
  | u :: _, hq =>
    Eval.Ok.bind (hf u (hq u List.mem_cons_self)) fun g _ => by
      cases g
      · exact Eval.Ok.pure trivial
      · exact Eval.Ok.forEach hf fun w hw => hq w (List.mem_cons_of_mem _ hw)

/-- Each arm of a `match` was checked against the scrutinee's type. -/
theorem ArmsFit.mem {scope : RowScope} :
    ∀ {Γ : Ctx} {fx : Effects} {arms : List Arm} {σ τ : Ty}, ArmsFit D scope Γ fx arms σ τ →
      ∀ {arm : Arm}, arm ∈ arms → ∃ σs ρ, PatFits D arm.pattern σ σs ∧
        arm.binders = arm.pattern.binders ∧
          GuardFits D scope (Γ.bindAll arm.binders σs) fx arm.guard ∧
          HasType D scope (Γ.bindAll arm.binders σs) fx arm.body ρ ∧ Fits ρ τ
  | _, _, _, _, _, .nil, _, h => nomatch h
  | _, _, _, _, _, .cons hp hbs _ hg hb hfit hrest, _, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, _, hp, hbs, hg, hb, hfit⟩
    · exact ArmsFit.mem hrest h

theorem substArmRows_eq_map (θ : RowSubst) : ∀ arms : List Arm,
    substArmRows θ arms =
      arms.map fun a => ⟨a.pattern, a.binders, substGuardRows θ a.guard, a.body.substRows θ⟩
  | [] => rfl
  | ⟨_, _, _, _⟩ :: arms => by simp [substArmRows, substArmRows_eq_map θ arms]

theorem Values.Typed.length : ∀ {vs : List Value} {τs : List Ty} {π : SParams},
    Values.Typed D vs τs π → vs.length = τs.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ hvs => by simp [Values.Typed.length hvs]

end

section

variable {D : Decls} {n : Nat} (hs : Sound D n) (hD : D.WellFormed) {scope : RowScope} {η : REnv}
  (hη : η.Respects scope) (θ : RowSubst) {Γ : Ctx} {fx : Effects}
include hs hD hη

theorem record_ok {R : Name} {args : List Ty} {r : RecordDecl} {fields : List (Name × Expr)}
    (hR : D.record? R = some r) (hlen : args.length = r.typeParams.length)
    (hperm : (fields.map Prod.fst).Perm (r.fields.map Prod.fst))
    (hf : FieldsFit D scope Γ fx fields (r.fieldsAt args)) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v ((Ty.record R args).close η))
      (eval D Copy.memory (n + 1) ((Expr.record R args fields).substRows θ)) := by
  refine Eval.Ok.bind (FieldsFit.ok hs hη θ hf) fun written hw => ?_
  have hr := Decls.mem_of_record? hR
  obtain ⟨fs, hfs, hft⟩ := hw.declare (hD.fieldNames r hr) (hD.fieldsClosed r hr) hperm
    r.fields fun _ h => h
  intro γ hγ
  show (Eval.declare D R written γ).Ok D Γ η _ _
  simp only [Eval.declare, hR, hfs]
  exact ⟨.record hR (by rw [length_closeTys]; exact hlen) hft, hγ⟩

theorem variant_ok {T : Name} {args : List Ty} {t : VariantDecl} {C : Name} {τs : List Ty}
    {payload : List Expr} (hT : D.variant? T = some t) (hlen : args.length = t.typeParams.length)
    (hC : (t.ctorsAt args).lookup C = some τs) (hp : ExprsFit D scope Γ fx payload τs) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v ((Ty.variant T args).close η))
      (eval D Copy.memory (n + 1) ((Expr.variant T args C payload).substRows θ)) := by
  obtain ⟨τs₀, hC₀, rfl⟩ := VariantDecl.exists_lookup_ctorsAt hC
  exact Eval.Ok.bind (ExprsFit.ok hs hη θ hp) fun _ hvs => Eval.Ok.pure (.variant hT
    (by rw [length_closeTys]; exact hlen) hC₀
    (hvs.sem _ _ (hD.payloadsClosed t (Decls.mem_of_variant? hT) (C, τs₀) (List.mem_of_lookup hC₀))))

omit hD in
theorem list_ok {τ : Ty} {es : List Expr} (hes : ExprsFit D scope Γ fx es (List.replicate es.length τ)) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v ((Ty.list τ).close η))
      (eval D Copy.memory (n + 1) ((Expr.list τ es).substRows θ)) :=
  Eval.Ok.bind (ExprsFit.ok hs hη θ hes) fun _ hvs => Eval.Ok.pure (.list hvs.replicate)

theorem match_ok {e : Expr} {σ τ : Ty} {arms : List Arm}
    (he : HasType D scope Γ fx e σ) (hx : Exhaustive D (armRows arms) [σ])
    (ha' : ArmsFit D scope Γ fx arms σ τ) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (τ.close η))
      (eval D Copy.memory (n + 1) ((Expr.match e τ arms).substRows θ)) := by
  refine Eval.Ok.bind (hs he hη θ) fun v hv => ?_
  show Eval.Ok D Γ η _ _ (Eval.select Copy.memory (eval D Copy.memory n) (substArmRows θ arms) v)
  obtain ⟨arm, hmem, hg, hm⟩ := Exhaustive.select hD hx hv
  rw [substArmRows_eq_map]
  refine Eval.select_of _ (.inr ⟨_, List.mem_map_of_mem hmem, by simp [hg, substGuardRows], hm⟩)
    (.inr fun a ha us hus => ?_) ?_ ?_
  · obtain ⟨arm, hmem, rfl⟩ := List.mem_map.1 ha
    obtain ⟨σs, ρ, hp, hbs, -, -, -⟩ := ha'.mem hmem
    have hlen : arm.binders.length = σs.length := by rw [hbs, hp.length]
    rcases hus with hm | hus
    · rw [hlen, (hp.bound hD hv hm).length]
    · obtain ⟨q, hq, hqm⟩ := Pattern.mem_ways hus
      rw [hlen, ((hp.alternative q hq).1.bound hD hv hqm).length]
  · intro a ha _ us hm _
    obtain ⟨arm, hmem, rfl⟩ := List.mem_map.1 ha
    obtain ⟨σs, ρ, hp, hbs, -, hb, hfit⟩ := ha'.mem hmem
    exact Eval.Ok.withVars (by rw [hbs, hp.length]) (hp.bound hD hv hm)
      ((hs hb hη θ).mono (fun _ hv => hv.fits (hfit.close η)) (fun _ F hF he => ⟨F, hF, he⟩)
        fun _ h => h)
  · intro a ha g hga us hus _ m hm
    obtain ⟨arm, hmem, rfl⟩ := List.mem_map.1 ha
    obtain ⟨σs, ρ, hp, hbs, hgt, hb, hfit⟩ := ha'.mem hmem
    obtain ⟨q, hq, hqm⟩ := Pattern.mem_ways hus
    obtain ⟨hqp, -⟩ := hp.alternative q hq
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
        refine Eval.Ok.bind (P := fun _ => True)
          (Eval.Ok.withVars hlen hut (Eval.Ok.bind (hs hgt hη θ) fun w hw => ?_)) fun k _ => ?_
        · obtain ⟨k, rfl⟩ := (hw.fits (hfg.close η)).bool_inv
          exact Eval.Ok.pure trivial
        · cases k
          · exact hm
          · exact Eval.Ok.withVars hlen hut
              ((hs hb hη θ).mono (fun _ hv => hv.fits (hfit.close η))
                (fun _ F hF he => ⟨F, hF, he⟩) fun _ h => h)

omit hD in
theorem for_ok {x : Name} {τ : Ty} {e body : Expr} {σ : Ty} (he : HasType D scope Γ fx e (.list τ))
    (hb : HasType D scope (Γ.bind x ⟨τ, false⟩) fx.inLoop body σ) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (Ty.unit.close η))
      (eval D Copy.memory (n + 1) ((Expr.for x τ e body).substRows θ)) := by
  refine Eval.Ok.bind (P := fun vs => ∀ u ∈ vs, Value.Typed D u (τ.close η))
    (Eval.Ok.bind (hs he hη θ) fun v hv => ?_) fun vs hvs => ?_
  · obtain ⟨vs, rfl, hvs⟩ := hv.list_inv
    exact Eval.Ok.pure hvs
  · refine Eval.Ok.bind (Eval.Ok.forEach (fun u hu => ?_) hvs) fun _ _ => Eval.Ok.pure .unit
    exact (Eval.Ok.withVar (b := ⟨τ, false⟩) hu
      ((hs hb hη θ).turn (X' := fx.exits D η) (fun _ F hF he => ⟨F, hF, he⟩) fun _ h => h)).mono
        (fun _ _ => trivial)
      (fun _ F hF he => ⟨F, hF, he⟩) fun _ h => h

end

end Stilt
