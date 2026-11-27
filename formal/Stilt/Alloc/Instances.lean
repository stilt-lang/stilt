import Stilt.Alloc.Sites
import Stilt.Generics.Commute
import Stilt.Rows

/-!
# Instances of code that makes no value needing storage

A call runs its callee's body instantiated, its type parameters and its row variables replaced
(types.no-type-arguments and effects.row-variables). Replacing row variables changes no site of
`alloc`, and replacing type parameters adds none: a variant's payload whose type argument is a
type parameter counts as one of a recursive type already (`Decls.payloadRecursive`).
-/

namespace Stilt

variable {D : Decls} {lim : Limited}

theorem Decls.recursiveTy_substTys (s : TySubst) :
    ∀ τ : Ty, D.recursiveTy τ = false → D.recursiveTy (τ.substTys s) = false := by
  intro τ h
  cases τ <;> simp_all [Ty.substTys, Decls.recursiveTy]

theorem Decls.recursiveTy_substRows (s : RowSubst) (τ : Ty) :
    D.recursiveTy (τ.substRows s) = D.recursiveTy τ := by
  cases τ <;> simp [Ty.substRows, Decls.recursiveTy]

theorem lookup_zip_substTyList (s : TySubst) (A : Name) :
    ∀ (ps : List Name) (τs : List Ty),
      (ps.zip (substTyList s τs)).lookup A = ((ps.zip τs).lookup A).map (Ty.substTys s)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, τ :: τs => by
    simp only [substTyList, List.zip_cons_cons, List.lookup_cons]
    split
    · rfl
    · exact lookup_zip_substTyList s A ps τs

theorem lookup_zip_substTysRows (s : RowSubst) (A : Name) :
    ∀ (ps : List Name) (τs : List Ty),
      (ps.zip (substTysRows s τs)).lookup A = ((ps.zip τs).lookup A).map (Ty.substRows s)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, τ :: τs => by
    simp only [substTysRows, List.zip_cons_cons, List.lookup_cons]
    split
    · rfl
    · exact lookup_zip_substTysRows s A ps τs

theorem Decls.payloadRecursive_substTys (s : TySubst) {T C : Name} {args : List Ty}
    (h : D.payloadRecursive T args C = false) :
    D.payloadRecursive T (substTyList s args) C = false := by
  unfold Decls.payloadRecursive at h ⊢
  cases hv : D.variant? T with
  | none => rfl
  | some t =>
    rw [hv] at h
    simp only [List.any_eq_false] at h ⊢
    intro τ hτ
    have h' := h τ hτ
    cases τ with
    | param A =>
      simp only [VariantDecl.typeArgs] at h' ⊢
      rw [lookup_zip_substTyList]
      cases hl : (t.typeParams.zip args).lookup A with
      | none => rw [hl] at h'; simp at h'
      | some σ =>
        rw [hl] at h'
        simpa using D.recursiveTy_substTys s σ (by simpa using h')
    | _ => exact h'

theorem Decls.payloadRecursive_substRows (s : RowSubst) (T C : Name) (args : List Ty) :
    D.payloadRecursive T (substTysRows s args) C = D.payloadRecursive T args C := by
  unfold Decls.payloadRecursive
  cases D.variant? T with
  | none => rfl
  | some t =>
    simp only
    congr 1
    funext τ
    cases τ with
    | param A =>
      simp only [VariantDecl.typeArgs]
      rw [lookup_zip_substTysRows]
      cases (t.typeParams.zip args).lookup A <;> simp [Decls.recursiveTy_substRows]
    | _ => rfl

theorem Op.allocates_substTys (s : TySubst) (o : Op) : (o.substTys s).allocates = o.allocates :=
  Op.substTys_congr Op.allocates (fun _ _ => rfl) s o

section

variable (s : TySubst)

mutual

theorem Expr.allocFreeIn_substTys : ∀ e : Expr, e.allocFreeIn D lim = true →
    (e.substTys s).allocFreeIn D lim = true
  | .var _, h | .move _, h | .int _, h | .bool _, h | .unit, h | .break, h | .continue, h
  | .fnRef .., h | .method .., h => h
  | .list _ _, h | .closure .., h | .perform _ _, h | .withH .., h => by
    simp [Expr.allocFreeIn] at h
  | .record _ _ fs, h => by
    simp only [Expr.allocFreeIn, Bool.and_eq_true] at h
    simp only [Expr.substTys, Expr.allocFreeIn, h.1, fieldsAllocFree_substTys fs h.2, Bool.and_self]
  | .variant T args C es, h => by
    simp only [Expr.allocFreeIn, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [Expr.substTys, Expr.allocFreeIn, Decls.payloadRecursive_substTys s h.1,
      exprsAllocFree_substTys es h.2, Bool.not_false, Bool.and_self]
  | .op o es, h => by
    simp only [Expr.allocFreeIn, Bool.and_eq_true] at h
    simp only [Expr.substTys, Expr.allocFreeIn, Op.allocates_substTys, h.1,
      exprsAllocFree_substTys es h.2, Bool.and_self]
  | .view es, h => by
    simp only [Expr.allocFreeIn] at h
    simp only [Expr.substTys, Expr.allocFreeIn, exprsAllocFree_substTys es h]
  | .field e _, h | .raise e, h | .try e, h | .form _ e, h | .return e, h | .loop e, h => by
    simp only [Expr.allocFreeIn] at h
    simp only [Expr.substTys, Expr.allocFreeIn, Expr.allocFreeIn_substTys e h]
  | .index a b, h | .letIn _ _ a b, h | .varIn _ _ a b, h | .seq a b, h | .for _ _ a b, h
  | .while a b, h | .tryCatch a _ _ b _, h => by
    simp only [Expr.allocFreeIn, Bool.and_eq_true] at h
    simp only [Expr.substTys, Expr.allocFreeIn, Expr.allocFreeIn_substTys a h.1,
      Expr.allocFreeIn_substTys b h.2, Bool.and_self]
  | .call f args _, h => by
    simp only [Expr.allocFreeIn, Bool.and_eq_true] at h
    simp only [Expr.substTys, Expr.allocFreeIn, Expr.allocFreeIn_substTys f h.1,
      argsAllocFree_substTys args h.2, Bool.and_self]
  | .assign ⟨_, path⟩ v, h => by
    simp only [Expr.allocFreeIn, Bool.and_eq_true] at h
    simp only [Expr.substTys, Expr.allocFreeIn, pathAllocFree_substTys path h.1,
      Expr.allocFreeIn_substTys v h.2, Bool.and_self]
  | .if c _ a b, h => by
    simp only [Expr.allocFreeIn, Bool.and_eq_true] at h
    simp only [Expr.substTys, Expr.allocFreeIn, Expr.allocFreeIn_substTys c h.1.1,
      Expr.allocFreeIn_substTys a h.1.2, Expr.allocFreeIn_substTys b h.2, Bool.and_self]
  | .match e _ arms, h => by
    simp only [Expr.allocFreeIn, Bool.and_eq_true] at h
    simp only [Expr.substTys, Expr.allocFreeIn, Expr.allocFreeIn_substTys e h.1,
      armsAllocFree_substTys arms h.2, Bool.and_self]
  | .held _ hs b, h => by
    simp only [Expr.allocFreeIn, Bool.and_eq_true] at h
    simp only [Expr.substTys, Expr.allocFreeIn, exprsAllocFree_substTys hs h.1,
      Expr.allocFreeIn_substTys b h.2, Bool.and_self]

theorem exprsAllocFree_substTys : ∀ es : List Expr, exprsAllocFree D lim es = true →
    exprsAllocFree D lim (substExprTys s es) = true
  | [], _ => rfl
  | e :: es, h => by
    simp only [exprsAllocFree, Bool.and_eq_true] at h
    simp only [substExprTys, exprsAllocFree, Expr.allocFreeIn_substTys e h.1,
      exprsAllocFree_substTys es h.2, Bool.and_self]

theorem fieldsAllocFree_substTys : ∀ fs : List (Name × Expr), fieldsAllocFree D lim fs = true →
    fieldsAllocFree D lim (substFieldTys s fs) = true
  | [], _ => rfl
  | (_, e) :: fs, h => by
    simp only [fieldsAllocFree, Bool.and_eq_true] at h
    simp only [substFieldTys, fieldsAllocFree, Expr.allocFreeIn_substTys e h.1,
      fieldsAllocFree_substTys fs h.2, Bool.and_self]

theorem argsAllocFree_substTys : ∀ args : List Arg, argsAllocFree D lim args = true →
    argsAllocFree D lim (substArgTys s args) = true
  | [], _ => rfl
  | .value e :: args, h => by
    simp only [argsAllocFree, Bool.and_eq_true] at h
    simp only [substArgTys, argsAllocFree, Expr.allocFreeIn_substTys e h.1,
      argsAllocFree_substTys args h.2, Bool.and_self]
  | .inout ⟨_, p⟩ :: args, h => by
    simp only [argsAllocFree, Bool.and_eq_true] at h
    simp only [substArgTys, argsAllocFree, pathAllocFree_substTys p h.1,
      argsAllocFree_substTys args h.2, Bool.and_self]

theorem pathAllocFree_substTys : ∀ p : List Projection, pathAllocFree D lim p = true →
    pathAllocFree D lim (substPathTys s p) = true
  | [], _ => rfl
  | .field _ :: p, h => by
    simp only [pathAllocFree] at h
    simp only [substPathTys, pathAllocFree, pathAllocFree_substTys p h]
  | .index i :: p, h => by
    simp only [pathAllocFree, Bool.and_eq_true] at h
    simp only [substPathTys, pathAllocFree, Expr.allocFreeIn_substTys i h.1,
      pathAllocFree_substTys p h.2, Bool.and_self]

theorem armsAllocFree_substTys : ∀ arms : List Arm, armsAllocFree D lim arms = true →
    armsAllocFree D lim (substArmTys s arms) = true
  | [], _ => rfl
  | ⟨_, _, g, b⟩ :: arms, h => by
    simp only [armsAllocFree, Bool.and_eq_true] at h
    simp only [substArmTys, armsAllocFree, guardAllocFree_substTys g h.1.1,
      Expr.allocFreeIn_substTys b h.1.2, armsAllocFree_substTys arms h.2, Bool.and_self]

theorem guardAllocFree_substTys : ∀ g : Option Expr, guardAllocFree D lim g = true →
    guardAllocFree D lim (substGuardTys s g) = true
  | none, _ => rfl
  | some g, h => by
    simp only [guardAllocFree] at h
    simp only [substGuardTys, guardAllocFree, Expr.allocFreeIn_substTys g h]

end

end

section

variable (s : RowSubst)

mutual

theorem Expr.allocFreeIn_substRows : ∀ e : Expr,
    (e.substRows s).allocFreeIn D lim = e.allocFreeIn D lim
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .list .. | .closure .. | .perform .. | .withH .. => rfl
  | .record _ _ fs => by simp [Expr.substRows, Expr.allocFreeIn, fieldsAllocFree_substRows fs]
  | .variant T args C es => by
    simp [Expr.substRows, Expr.allocFreeIn, Decls.payloadRecursive_substRows,
      exprsAllocFree_substRows es]
  | .op _ es | .view es => by simp [Expr.substRows, Expr.allocFreeIn, exprsAllocFree_substRows es]
  | .field e _ | .raise e | .try e | .form _ e | .return e | .loop e => by
    simp [Expr.substRows, Expr.allocFreeIn, Expr.allocFreeIn_substRows e]
  | .index a b | .letIn _ _ a b | .varIn _ _ a b | .seq a b | .for _ _ a b | .while a b
  | .tryCatch a _ _ b _ => by
    simp [Expr.substRows, Expr.allocFreeIn, Expr.allocFreeIn_substRows a,
      Expr.allocFreeIn_substRows b]
  | .call f args _ => by
    simp [Expr.substRows, Expr.allocFreeIn, Expr.allocFreeIn_substRows f,
      argsAllocFree_substRows args]
  | .assign ⟨_, p⟩ v => by
    simp [Expr.substRows, Expr.allocFreeIn, pathAllocFree_substRows p, Expr.allocFreeIn_substRows v]
  | .if c _ a b => by
    simp [Expr.substRows, Expr.allocFreeIn, Expr.allocFreeIn_substRows c,
      Expr.allocFreeIn_substRows a, Expr.allocFreeIn_substRows b]
  | .match e _ arms => by
    simp [Expr.substRows, Expr.allocFreeIn, Expr.allocFreeIn_substRows e,
      armsAllocFree_substRows arms]
  | .held _ hs b => by
    simp [Expr.substRows, Expr.allocFreeIn, exprsAllocFree_substRows hs,
      Expr.allocFreeIn_substRows b]

theorem exprsAllocFree_substRows : ∀ es : List Expr,
    exprsAllocFree D lim (substExprRows s es) = exprsAllocFree D lim es
  | [] => rfl
  | e :: es => by
    simp [substExprRows, exprsAllocFree, Expr.allocFreeIn_substRows e, exprsAllocFree_substRows es]

theorem fieldsAllocFree_substRows : ∀ fs : List (Name × Expr),
    fieldsAllocFree D lim (substFieldRows s fs) = fieldsAllocFree D lim fs
  | [] => rfl
  | (_, e) :: fs => by
    simp [substFieldRows, fieldsAllocFree, Expr.allocFreeIn_substRows e,
      fieldsAllocFree_substRows fs]

theorem argsAllocFree_substRows : ∀ args : List Arg,
    argsAllocFree D lim (substArgRows s args) = argsAllocFree D lim args
  | [] => rfl
  | .value e :: args => by
    simp [substArgRows, argsAllocFree, Expr.allocFreeIn_substRows e, argsAllocFree_substRows args]
  | .inout ⟨_, p⟩ :: args => by
    simp [substArgRows, argsAllocFree, pathAllocFree_substRows p, argsAllocFree_substRows args]

theorem pathAllocFree_substRows : ∀ p : List Projection,
    pathAllocFree D lim (substPathRows s p) = pathAllocFree D lim p
  | [] => rfl
  | .field _ :: p => by simp [substPathRows, pathAllocFree, pathAllocFree_substRows p]
  | .index i :: p => by
    simp [substPathRows, pathAllocFree, Expr.allocFreeIn_substRows i, pathAllocFree_substRows p]

theorem armsAllocFree_substRows : ∀ arms : List Arm,
    armsAllocFree D lim (substArmRows s arms) = armsAllocFree D lim arms
  | [] => rfl
  | ⟨_, _, g, b⟩ :: arms => by
    simp [substArmRows, armsAllocFree, guardAllocFree_substRows g, Expr.allocFreeIn_substRows b,
      armsAllocFree_substRows arms]

theorem guardAllocFree_substRows : ∀ g : Option Expr,
    guardAllocFree D lim (substGuardRows s g) = guardAllocFree D lim g
  | none => rfl
  | some g => by simp [substGuardRows, guardAllocFree, Expr.allocFreeIn_substRows g]

end

end

end Stilt
