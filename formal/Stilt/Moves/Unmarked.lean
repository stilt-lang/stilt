import Stilt.Moves.Erase
import Stilt.WellTyped

/-!
# Programs without marks

A well-typed expression has no mark, since typing has no rule for one: its
erasure is itself. So a well-typed program is its own erasure, and marking it
gives a program whose erasure is well typed. Erasing keeps the parameter names
of closures too.
-/

namespace Stilt

mutual

theorem Expr.distinctParams_erase : ∀ e : Expr, e.erase.distinctParams = e.distinctParams
  | .var _ | .move _ | .int _ | .bool _ | .unit | .fnRef .. | .method .. | .break | .continue => rfl
  | .record _ fs => by simp [Expr.erase, Expr.distinctParams, fieldsDistinctParams_erase fs]
  | .variant _ _ es | .list _ es | .op _ es | .view es => by
    simp [Expr.erase, Expr.distinctParams, exprsDistinctParams_erase es]
  | .field e _ | .raise e | .perform _ e | .try e | .loop e | .return e => by
    simp [Expr.erase, Expr.distinctParams, Expr.distinctParams_erase e]
  | .index a b | .seq a b | .withH _ _ a b | .while a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b
  | .tryCatch a _ _ b _ => by
    simp [Expr.erase, Expr.distinctParams, Expr.distinctParams_erase a,
      Expr.distinctParams_erase b]
  | .closure _ _ _ b => by simp [Expr.erase, Expr.distinctParams, Expr.distinctParams_erase b]
  | .held _ hs b => by
    simp [Expr.erase, Expr.distinctParams, exprsDistinctParams_erase hs, Expr.distinctParams_erase b]
  | .call f args _ => by
    simp [Expr.erase, Expr.distinctParams, Expr.distinctParams_erase f,
      argsDistinctParams_erase args]
  | .assign ⟨_, p⟩ v => by
    simp [Expr.erase, Expr.distinctParams, pathDistinctParams_erase p,
      Expr.distinctParams_erase v]
  | .if c _ a b => by
    simp [Expr.erase, Expr.distinctParams, Expr.distinctParams_erase c,
      Expr.distinctParams_erase a, Expr.distinctParams_erase b]
  | .match e _ arms => by
    simp [Expr.erase, Expr.distinctParams, Expr.distinctParams_erase e,
      armsDistinctParams_erase arms]

theorem exprsDistinctParams_erase :
    ∀ es : List Expr, exprsDistinctParams (eraseExprs es) = exprsDistinctParams es
  | [] => rfl
  | e :: es => by
    simp [eraseExprs, exprsDistinctParams, Expr.distinctParams_erase e,
      exprsDistinctParams_erase es]

theorem fieldsDistinctParams_erase :
    ∀ fs : List (Name × Expr), fieldsDistinctParams (eraseFields fs) = fieldsDistinctParams fs
  | [] => rfl
  | (_, e) :: fs => by
    simp [eraseFields, fieldsDistinctParams, Expr.distinctParams_erase e,
      fieldsDistinctParams_erase fs]

theorem argsDistinctParams_erase :
    ∀ args : List Arg, argsDistinctParams (eraseArgs args) = argsDistinctParams args
  | [] => rfl
  | .value e :: args => by
    simp [eraseArgs, argsDistinctParams, Expr.distinctParams_erase e,
      argsDistinctParams_erase args]
  | .inout ⟨_, p⟩ :: args => by
    simp [eraseArgs, argsDistinctParams, pathDistinctParams_erase p,
      argsDistinctParams_erase args]

theorem pathDistinctParams_erase :
    ∀ p : List Projection, pathDistinctParams (erasePath p) = pathDistinctParams p
  | [] => rfl
  | .field _ :: p => by simpa [erasePath, pathDistinctParams] using pathDistinctParams_erase p
  | .index i :: p => by
    simp [erasePath, pathDistinctParams, Expr.distinctParams_erase i, pathDistinctParams_erase p]

theorem armsDistinctParams_erase :
    ∀ arms : List Arm, armsDistinctParams (eraseArms arms) = armsDistinctParams arms
  | [] => rfl
  | ⟨_, _, b⟩ :: arms => by
    simp [eraseArms, armsDistinctParams, Expr.distinctParams_erase b,
      armsDistinctParams_erase arms]

end

/-! ## Typing has no rule for a mark -/

section Typing

variable {D : Decls} {s : RowScope}

mutual

theorem HasType.erase_eq : ∀ {Γ fx e τ}, HasType D s Γ fx e τ → e.erase = e
  | _, _, _, _, .var _ | _, _, _, _, .int _ | _, _, _, _, .bool | _, _, _, _, .unit
  | _, _, _, _, .fnRef .. | _, _, _, _, .method .. | _, _, _, _, .break _
  | _, _, _, _, .continue _ => rfl
  | _, _, _, _, .record _ _ h => by simp [Expr.erase, FieldsFit.erase_eq h]
  | _, _, _, _, .variant _ _ h | _, _, _, _, .list _ h | _, _, _, _, .op _ h _
  | _, _, _, _, .view _ h => by
    simp [Expr.erase, ExprsFit.erase_eq h]
  | _, _, _, _, .field h _ _ | _, _, _, _, .elem h _ | _, _, _, _, .raise _ h _
  | _, _, _, _, .try h | _, _, _, _, .loopBreaks h _ | _, _, _, _, .loopForever h _
  | _, _, _, _, .return h _ | _, _, _, _, .perform _ _ _ _ _ h _
  | _, _, _, _, .resume _ _ _ h _ => by
    simp [Expr.erase, HasType.erase_eq h]
  | _, _, _, _, .withH _ _ h₁ _ _ h₂ _ | _, _, _, _, .withControl _ _ h₁ _ _ h₂ _ _ _ => by
    simp [Expr.erase, HasType.erase_eq h₁, HasType.erase_eq h₂]
  | _, _, _, _, .index h₁ h₂ _ | _, _, _, _, .seq h₁ _ h₂ | _, _, _, _, .letIn _ h₁ _ h₂
  | _, _, _, _, .varIn _ h₁ _ h₂ | _, _, _, _, .for _ h₁ h₂ _
  | _, _, _, _, .while h₁ _ h₂ _ => by
    simp [Expr.erase, HasType.erase_eq h₁, HasType.erase_eq h₂]
  | _, _, _, _, .tryCatch _ _ h₁ _ h₂ _ => by
    simp [Expr.erase, HasType.erase_eq h₁, HasType.erase_eq h₂]
  | _, _, _, _, .held _ _ h₁ h₂ _ => by simp [Expr.erase, ExprsFit.erase_eq h₁, HasType.erase_eq h₂]
  | _, _, _, _, .closure _ _ _ h _ => by simp [Expr.erase, HasType.erase_eq h]
  | _, _, _, _, .call h₁ h₂ _ => by simp [Expr.erase, HasType.erase_eq h₁, ArgsFit.erase_eq h₂]
  | _, _, .assign ⟨_, _⟩ _, _, .assign h₁ h₂ _ => by
    simp [Expr.erase, PlaceFits.erase_eq h₁, HasType.erase_eq h₂]
  | _, _, _, _, .if _ h₁ _ h₂ _ h₃ _ => by
    simp [Expr.erase, HasType.erase_eq h₁, HasType.erase_eq h₂, HasType.erase_eq h₃]
  | _, _, _, _, .match _ h₁ _ h₂ => by simp [Expr.erase, HasType.erase_eq h₁, ArmsFit.erase_eq h₂]

theorem ExprsFit.erase_eq : ∀ {Γ fx es τs}, ExprsFit D s Γ fx es τs → eraseExprs es = es
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons h _ hs => by simp [eraseExprs, HasType.erase_eq h, ExprsFit.erase_eq hs]

theorem FieldsFit.erase_eq :
    ∀ {Γ fx fields declared}, FieldsFit D s Γ fx fields declared → eraseFields fields = fields
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons _ h _ hs => by simp [eraseFields, HasType.erase_eq h, FieldsFit.erase_eq hs]

theorem ArgsFit.erase_eq : ∀ {Γ fx args ps}, ArgsFit D s Γ fx args ps → eraseArgs args = args
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .value _ h _ hs => by simp [eraseArgs, HasType.erase_eq h, ArgsFit.erase_eq hs]
  | _, _, .inout ⟨_, _⟩ :: _, _, .inout h hs => by
    simp [eraseArgs, PlaceFits.erase_eq h, ArgsFit.erase_eq hs]

theorem PlaceFits.erase_eq : ∀ {Γ fx p τ}, PlaceFits D s Γ fx p τ → erasePath p.path = p.path
  | _, _, _, _, .mk _ h => PathFits.erase_eq h

theorem PathFits.erase_eq : ∀ {Γ fx σ path τ}, PathFits D s Γ fx σ path τ → erasePath path = path
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .field _ _ h | _, _, _, _, _, .elem _ h => by
    simp [erasePath, PathFits.erase_eq h]
  | _, _, _, _, _, .index h₁ _ h₂ => by simp [erasePath, HasType.erase_eq h₁, PathFits.erase_eq h₂]

theorem ArmsFit.erase_eq : ∀ {Γ fx arms σ τ}, ArmsFit D s Γ fx arms σ τ → eraseArms arms = arms
  | _, _, _, _, _, .nil => rfl
  | _, _, ⟨_, _, _⟩ :: _, _, _, .cons _ _ _ h _ hs => by
    simp [eraseArms, HasType.erase_eq h, ArmsFit.erase_eq hs]

end

end Typing

/-- A well-typed program has no mark: it is its own erasure. -/
theorem Program.WellTyped.erase_eq {p : Program} (h : p.WellTyped) : p.erase = p := by
  have hfns : p.decls.mapFns FnDecl.erase = p.decls :=
    Decls.mapFns_eq_self FnDecl.erase_qualify (fun _ => rfl) fun d hd => by
      obtain ⟨σ, hty, -⟩ := h.typedIn.fns d hd
      simp [FnDecl.erase, HasType.erase_eq hty]
  obtain ⟨σ, hty, -⟩ := h.main
  simp only [Program.erase, hfns, HasType.erase_eq hty]

end Stilt
