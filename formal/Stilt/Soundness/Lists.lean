import Stilt.Soundness.Call

/-!
# Lists of expressions

The evaluator's combinators that run several expressions in turn: the elements
of a list or a payload, the fields of a record literal, the arguments of a
call and the indexes of a place (values.left-to-right). Each keeps `Outcome.Ok` when
every expression it runs does, which `Sound D n` gives at the fuel they run
with.
-/

namespace Stilt

section

variable {D : Decls}

/-- Values of the types at their positions, read under `η`, as expressions
evaluated from left to right give them (values.left-to-right). -/
inductive ValuesAt (D : Decls) (η : REnv) : List Value → List Ty → Prop
  | nil : ValuesAt D η [] []
  | cons {v : Value} {τ : Ty} {vs : List Value} {τs : List Ty} :
      Value.Typed D v (τ.close η) → ValuesAt D η vs τs → ValuesAt D η (v :: vs) (τ :: τs)

/-- The fields of a record literal once evaluated, in the order written: each
named as written, with a value of the type its record declares for it (expressions.struct-literal-fields). -/
inductive WrittenAt (D : Decls) (η : REnv) (declared : List (Name × Ty)) :
    List (Name × Value) → List (Name × Expr) → Prop
  | nil : WrittenAt D η declared [] []
  | cons {f : Name} {v : Value} {e : Expr} {τ : Ty} {written : List (Name × Value)}
      {fields : List (Name × Expr)} :
      declared.lookup f = some τ → Value.Typed D v (τ.close η) →
      WrittenAt D η declared written fields →
      WrittenAt D η declared ((f, v) :: written) ((f, e) :: fields)

variable {n : Nat} (hs : Sound D n) {scope : RowScope} {η : REnv} (hη : η.Respects scope)
  (θ : RowSubst)
include hs hη

theorem ExprsFit.ok :
    ∀ {Γ : Ctx} {fx : Effects} {es : List Expr} {τs : List Ty}, ExprsFit D scope Γ fx es τs →
      Eval.Ok D Γ η (fx.exits D η) (fun vs => ValuesAt D η vs τs)
        (Eval.list (eval D Copy.memory n) (substExprRows θ es))
  | _, _, _, _, .nil => Eval.Ok.pure .nil
  | _, _, _, _, .cons he hfit hrest =>
    Eval.Ok.bind (hs he hη θ) fun _ hv =>
      Eval.Ok.bind (ExprsFit.ok hrest) fun _ hvs =>
        Eval.Ok.pure (.cons (hv.fits (hfit.close η)) hvs)

theorem FieldsFit.ok :
    ∀ {Γ : Ctx} {fx : Effects} {fields : List (Name × Expr)} {declared : List (Name × Ty)},
      FieldsFit D scope Γ fx fields declared →
        Eval.Ok D Γ η (fx.exits D η) (fun written => WrittenAt D η declared written fields)
          (Eval.fields (eval D Copy.memory n) (substFieldRows θ fields))
  | _, _, _, _, .nil => Eval.Ok.pure .nil
  | _, _, _, _, .cons hl he hfit hrest =>
    Eval.Ok.bind (hs he hη θ) fun _ hv =>
      Eval.Ok.bind (FieldsFit.ok hrest) fun _ hw =>
        Eval.Ok.pure (.cons hl (hv.fits (hfit.close η)) hw)

end

theorem List.mem_of_lookup {β : Type} :
    ∀ {l : List (Name × β)} {k : Name} {b : β}, l.lookup k = some b → (k, b) ∈ l
  | [], _, _, h => nomatch h
  | (k', b') :: l, k, b, h => by
    by_cases hk : k = k'
    · subst hk
      simp only [List.lookup_cons_self, Option.some.injEq] at h
      simp [h]
    · rw [lookup_cons_ne hk] at h
      exact List.mem_cons_of_mem _ (List.mem_of_lookup h)

theorem Decls.mem_of_record? {D : Decls} {R : Name} {r : RecordDecl} (h : D.record? R = some r) :
    r ∈ D.records :=
  List.mem_of_find?_eq_some h

theorem Decls.mem_of_variant? {D : Decls} {T : Name} {t : VariantDecl} (h : D.variant? T = some t) :
    t ∈ D.variants :=
  List.mem_of_find?_eq_some h

/-- A field's type at a record type's arguments, read, is its declared type at the
arguments read. -/
theorem Decls.WellFormed.close_fieldsAt {D : Decls} (hD : D.WellFormed) {R : Name} {r : RecordDecl}
    (hR : D.record? R = some r) {args : List Ty} {f : Name} {τ : Ty}
    (hf : (r.fieldsAt args).lookup f = some τ) (η : REnv) :
    ∃ τ₀, r.fields.lookup f = some τ₀ ∧ τ.close η = τ₀.semAt (r.typeParams.zip (closeTys η args)) := by
  rw [RecordDecl.lookup_fieldsAt] at hf
  cases h₀ : r.fields.lookup f with
  | none => rw [h₀] at hf; exact nomatch hf
  | some τ₀ =>
    rw [h₀] at hf
    obtain rfl := Option.some.inj hf
    exact ⟨τ₀, rfl, (hD.fieldsClosed r (Decls.mem_of_record? hR) _ (List.mem_of_lookup h₀)).close_substTys
      _ _ η⟩

/-- A variant's payload types at a variant type's arguments are its declared ones at them. -/
theorem VariantDecl.exists_lookup_ctorsAt {t : VariantDecl} {args : List Ty} {C : Name}
    {τs : List Ty} (hC : (t.ctorsAt args).lookup C = some τs) :
    ∃ τs₀, t.ctors.lookup C = some τs₀ ∧ τs = τs₀.map (Ty.substTys (t.typeArgs args)) := by
  rw [VariantDecl.lookup_ctorsAt] at hC
  cases h₀ : t.ctors.lookup C with
  | none => rw [h₀] at hC; exact nomatch hC
  | some τs₀ => rw [h₀] at hC; exact ⟨τs₀, rfl, (Option.some.inj hC).symm⟩

/-- A typed expression is never the last use of a variable: typing has no rule
for a mark. -/
theorem HasType.not_move {D : Decls} {scope : RowScope} :
    ∀ {Γ : Ctx} {fx : Effects} {e : Expr} {τ : Ty}, HasType D scope Γ fx e τ → ∀ x, e ≠ .move x
  | _, _, _, _, .var _, _ | _, _, _, _, .int _, _ | _, _, _, _, .bool, _ | _, _, _, _, .unit, _
  | _, _, _, _, .record .., _ | _, _, _, _, .variant .., _ | _, _, _, _, .list .., _
  | _, _, _, _, .op .., _ | _, _, _, _, .view .., _ | _, _, _, _, .elem .., _
  | _, _, _, _, .field .., _ | _, _, _, _, .index .., _ | _, _, _, _, .fnRef .., _
  | _, _, _, _, .method .., _
  | _, _, _, _, .closure .., _ | _, _, _, _, .call .., _ | _, _, _, _, .letIn .., _
  | _, _, _, _, .varIn .., _ | _, _, _, _, .assign .., _ | _, _, _, _, .seq .., _
  | _, _, _, _, .if .., _ | _, _, _, _, .match .., _ | _, _, _, _, .for .., _
  | _, _, _, _, .raise .., _ | _, _, _, _, .try .., _ | _, _, _, _, .tryCatch .., _
  | _, _, _, _, .while .., _ | _, _, _, _, .loopBreaks .., _ | _, _, _, _, .loopForever .., _
  | _, _, _, _, .break .., _ | _, _, _, _, .continue .., _ | _, _, _, _, .return .., _
  | _, _, _, _, .perform .., _ | _, _, _, _, .resume .., _ | _, _, _, _, .withH .., _
  | _, _, _, _, .withControl .., _ | _, _, _, _, .held .., _ | _, _, _, _, .letElse .., _
  | _, _, _, _, .orElse .., _ | _, _, _, _, .form .., _ | _, _, _, _, .shaped .., _ => nofun

theorem Expr.substRows_ne_move {e : Expr} (h : ∀ x, e ≠ .move x) (θ : RowSubst) :
    ∀ x, e.substRows θ ≠ .move x := by
  intro x hx
  cases e with
  | move y => exact h y rfl
  | assign p v => obtain ⟨_, _⟩ := p; simp [Expr.substRows] at hx
  | _ => simp [Expr.substRows] at hx

theorem Passed.ofArg_of_ne_move {e : Expr} (h : ∀ x, e ≠ .move x) (v : Value) :
    Passed.ofArg e v = .value v := by
  cases e <;> first | rfl | exact absurd rfl (h _)

section

variable {D : Decls} {n : Nat} (hs : Sound D n) (hD : D.WellFormed) {scope : RowScope}
  {η : REnv} (hη : η.Respects scope) (θ : RowSubst)
include hs hη

include hD in
theorem PathFits.ok :
    ∀ {Γ : Ctx} {fx : Effects} {σ : Ty} {ps : List Projection} {τ : Ty},
      PathFits D scope Γ fx σ ps τ →
        Eval.Ok D Γ η (fx.exits D η) (fun p => PathTyped D (σ.close η) p (τ.close η))
          (Eval.path (eval D Copy.memory n) (substPathRows θ ps))
  | _, _, _, _, _, .nil => Eval.Ok.pure .nil
  | _, _, _, _, _, .field hR _ hf hrest =>
    Eval.Ok.bind (PathFits.ok hrest) fun _ hp => by
      obtain ⟨τ₀, hf₀, hτ⟩ := hD.close_fieldsAt hR hf η
      refine Eval.Ok.pure (.field hR hf₀ ?_)
      rwa [← hτ]
  | _, _, _, _, _, .index hi hfit hrest =>
    Eval.Ok.bind (Eval.Ok.bind (hs hi hη θ) fun v hv => by
        obtain ⟨k, rfl⟩ := (hv.fits (hfit.close η)).i64_inv
        exact Eval.Ok.pure (P := fun _ => True) trivial) fun _ _ =>
      Eval.Ok.bind (PathFits.ok hrest) fun _ hp => Eval.Ok.pure (.index hp)
  | _, _, _, _, _, .elem hf hrest =>
    Eval.Ok.bind (PathFits.ok hrest) fun _ hp => Eval.Ok.pure (.elem (closeTys_lookup η hf) hp)

include hD in
theorem ArgsFit.ok :
    ∀ {Γ : Ctx} {fx : Effects} {args : List Arg} {ps : List (Mode × Ty)},
      ArgsFit D scope Γ fx args ps →
        Eval.Ok D Γ η (fx.exits D η) (fun passed => Passed.Typed D Γ η passed ps)
          (Eval.args (eval D Copy.memory n) (substArgRows θ args))
  | _, _, _, _, .nil => Eval.Ok.pure .nil
  | _, _, .value e :: _, (m, _) :: _, .value hm he hfit hrest => by
    cases m with
    | inout => exact absurd rfl hm
    | «let» =>
      refine Eval.Ok.bind (hs he hη θ) fun v hv => Eval.Ok.bind (ArgsFit.ok hrest) fun _ hp => ?_
      rw [Passed.ofArg_of_ne_move (Expr.substRows_ne_move he.not_move θ)]
      exact Eval.Ok.pure (.value (hv.fits (hfit.close η)) hp)
  | _, _, .inout ⟨_, _⟩ :: _, _, .inout (.mk hl hpath) hrest =>
    Eval.Ok.bind (PathFits.ok hs hD hη θ hpath) fun _ hp =>
      Eval.Ok.bind (ArgsFit.ok hrest) fun _ hps => Eval.Ok.pure (.place hl hp hps)

end

end Stilt
