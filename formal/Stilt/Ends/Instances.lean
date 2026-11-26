import Stilt.Ends.Syntax
import Stilt.Ends.CountInstances
import Stilt.Generics.Commute

/-!
# Instantiation keeps the bounds

Instantiation rewrites types alone, so an instantiated body holds the same
sites of `div`, and needs the same fuel, as the body.
-/

namespace Stilt

section

variable (s : TySubst) {lim : Limited}

theorem Expr.callable_substTys (e : Expr) : (e.substTys s).callable = e.callable := by
  cases e <;> first | rfl | (rename_i t _; cases t; rfl)

mutual

theorem Expr.divFree_substTys : ∀ e : Expr, (e.substTys s).divFree lim = e.divFree lim
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method .. => rfl
  | .record _ _ fs => by simp [Expr.substTys, Expr.divFree, fieldsDivFree_substTys fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by
    simp [Expr.substTys, Expr.divFree, exprsDivFree_substTys es]
  | .closure _ _ _ e | .field e _ | .raise e | .perform _ e | .try e | .loop e | .return e => by
    simp [Expr.substTys, Expr.divFree, Expr.divFree_substTys e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b
  | .tryCatch a _ _ b _ => by
    simp [Expr.substTys, Expr.divFree, Expr.divFree_substTys a, Expr.divFree_substTys b]
  | .while a b => by
    simp [Expr.substTys, Expr.divFree, Expr.divFree_substTys a, Expr.divFree_substTys b,
      Expr.countsIn_substTys]
  | .call f args _ => by
    simp [Expr.substTys, Expr.divFree, Expr.callable_substTys s f, Expr.divFree_substTys f,
      argsDivFree_substTys args]
  | .assign ⟨_, p⟩ v => by
    simp [Expr.substTys, Expr.divFree, pathDivFree_substTys p, Expr.divFree_substTys v]
  | .if c _ a b => by
    simp [Expr.substTys, Expr.divFree, Expr.divFree_substTys c, Expr.divFree_substTys a, Expr.divFree_substTys b]
  | .match e _ arms => by
    simp [Expr.substTys, Expr.divFree, Expr.divFree_substTys e, armsDivFree_substTys arms]
  | .held _ hs b => by
    simp [Expr.substTys, Expr.divFree, exprsDivFree_substTys hs, Expr.divFree_substTys b]

theorem exprsDivFree_substTys : ∀ es : List Expr, exprsDivFree lim (substExprTys s es) = exprsDivFree lim es
  | [] => rfl
  | e :: es => by simp [substExprTys, exprsDivFree, Expr.divFree_substTys e, exprsDivFree_substTys es]

theorem fieldsDivFree_substTys :
    ∀ fs : List (Name × Expr), fieldsDivFree lim (substFieldTys s fs) = fieldsDivFree lim fs
  | [] => rfl
  | (_, e) :: fs => by simp [substFieldTys, fieldsDivFree, Expr.divFree_substTys e, fieldsDivFree_substTys fs]

theorem argsDivFree_substTys : ∀ args : List Arg, argsDivFree lim (substArgTys s args) = argsDivFree lim args
  | [] => rfl
  | .value e :: args => by simp [substArgTys, argsDivFree, Expr.divFree_substTys e, argsDivFree_substTys args]
  | .inout ⟨_, p⟩ :: args => by
    simp [substArgTys, argsDivFree, pathDivFree_substTys p, argsDivFree_substTys args]

theorem pathDivFree_substTys : ∀ p : List Projection, pathDivFree lim (substPathTys s p) = pathDivFree lim p
  | [] => rfl
  | .field _ :: p => by simpa [substPathTys, pathDivFree] using pathDivFree_substTys p
  | .index i :: p => by simp [substPathTys, pathDivFree, Expr.divFree_substTys i, pathDivFree_substTys p]

theorem armsDivFree_substTys : ∀ arms : List Arm, armsDivFree lim (substArmTys s arms) = armsDivFree lim arms
  | [] => rfl
  | ⟨_, _, b⟩ :: arms => by simp [substArmTys, armsDivFree, Expr.divFree_substTys b, armsDivFree_substTys arms]

end

variable (B : Name → Nat)

mutual

theorem Expr.needs_substTys : ∀ e : Expr, (e.substTys s).needs B = e.needs B
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .closure .. => rfl
  | .record _ _ fs => by simp [Expr.substTys, Expr.needs, fieldsNeeds_substTys fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by simp [Expr.substTys, Expr.needs, exprsNeeds_substTys es]
  | .field e _ | .raise e | .perform _ e | .try e | .loop e | .return e => by
    simp [Expr.substTys, Expr.needs, Expr.needs_substTys e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b | .while a b
  | .tryCatch a _ _ b _ => by
    simp [Expr.substTys, Expr.needs, Expr.needs_substTys a, Expr.needs_substTys b]
  | .call f args _ => by
    simp [Expr.substTys, Expr.needs, Expr.needs_substTys f, Expr.bodyNeeds_substTys f, argsNeeds_substTys args]
  | .assign ⟨_, p⟩ v => by simp [Expr.substTys, Expr.needs, pathNeeds_substTys p, Expr.needs_substTys v]
  | .if c _ a b => by
    simp [Expr.substTys, Expr.needs, Expr.needs_substTys c, Expr.needs_substTys a, Expr.needs_substTys b]
  | .match e _ arms => by simp [Expr.substTys, Expr.needs, Expr.needs_substTys e, armsNeeds_substTys arms]

  | .held _ hs b => by simp [Expr.substTys, Expr.needs, exprsNeeds_substTys hs, Expr.needs_substTys b]
theorem Expr.bodyNeeds_substTys : ∀ e : Expr, (e.substTys s).bodyNeeds B = e.bodyNeeds B
  | .closure _ _ _ b => by simp [Expr.substTys, Expr.bodyNeeds, Expr.needs_substTys b]
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .record .. | .variant .. | .list .. | .op .. | .view _ | .field .. | .index .. | .call .. | .letIn ..
  | .varIn .. | .seq .. | .if .. | .match .. | .for .. | .raise .. | .perform _ .. | .withH .. | .held .. | .try .. | .tryCatch ..
  | .while .. | .loop .. | .return .. => rfl
  | .assign ⟨_, _⟩ _ => rfl

theorem exprsNeeds_substTys : ∀ es : List Expr, exprsNeeds B (substExprTys s es) = exprsNeeds B es
  | [] => rfl
  | e :: es => by simp [substExprTys, exprsNeeds, Expr.needs_substTys e, exprsNeeds_substTys es]

theorem fieldsNeeds_substTys :
    ∀ fs : List (Name × Expr), fieldsNeeds B (substFieldTys s fs) = fieldsNeeds B fs
  | [] => rfl
  | (_, e) :: fs => by simp [substFieldTys, fieldsNeeds, Expr.needs_substTys e, fieldsNeeds_substTys fs]

theorem argsNeeds_substTys : ∀ args : List Arg, argsNeeds B (substArgTys s args) = argsNeeds B args
  | [] => rfl
  | .value e :: args => by simp [substArgTys, argsNeeds, Expr.needs_substTys e, argsNeeds_substTys args]
  | .inout ⟨_, p⟩ :: args => by simp [substArgTys, argsNeeds, pathNeeds_substTys p, argsNeeds_substTys args]

theorem pathNeeds_substTys : ∀ p : List Projection, pathNeeds B (substPathTys s p) = pathNeeds B p
  | [] => rfl
  | .field _ :: p => by simpa [substPathTys, pathNeeds] using pathNeeds_substTys p
  | .index i :: p => by simp [substPathTys, pathNeeds, Expr.needs_substTys i, pathNeeds_substTys p]

theorem armsNeeds_substTys : ∀ arms : List Arm, armsNeeds B (substArmTys s arms) = armsNeeds B arms
  | [] => rfl
  | ⟨_, _, b⟩ :: arms => by simp [substArmTys, armsNeeds, Expr.needs_substTys b, armsNeeds_substTys arms]

end

end

section

variable (s : RowSubst) {lim : Limited}

theorem Expr.callable_substRows (e : Expr) : (e.substRows s).callable = e.callable := by
  cases e <;> first | rfl | (rename_i t _; cases t; rfl)

mutual

theorem Expr.divFree_substRows : ∀ e : Expr, (e.substRows s).divFree lim = e.divFree lim
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method .. => rfl
  | .record _ _ fs => by simp [Expr.substRows, Expr.divFree, fieldsDivFree_substRows fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by
    simp [Expr.substRows, Expr.divFree, exprsDivFree_substRows es]
  | .closure _ _ _ e | .field e _ | .raise e | .perform _ e | .try e | .loop e | .return e => by
    simp [Expr.substRows, Expr.divFree, Expr.divFree_substRows e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b
  | .tryCatch a _ _ b _ => by
    simp [Expr.substRows, Expr.divFree, Expr.divFree_substRows a, Expr.divFree_substRows b]
  | .while a b => by
    simp [Expr.substRows, Expr.divFree, Expr.divFree_substRows a, Expr.divFree_substRows b,
      Expr.countsIn_substRows]
  | .call f args _ => by
    simp [Expr.substRows, Expr.divFree, Expr.callable_substRows s f, Expr.divFree_substRows f,
      argsDivFree_substRows args]
  | .assign ⟨_, p⟩ v => by
    simp [Expr.substRows, Expr.divFree, pathDivFree_substRows p, Expr.divFree_substRows v]
  | .if c _ a b => by
    simp [Expr.substRows, Expr.divFree, Expr.divFree_substRows c, Expr.divFree_substRows a, Expr.divFree_substRows b]
  | .match e _ arms => by
    simp [Expr.substRows, Expr.divFree, Expr.divFree_substRows e, armsDivFree_substRows arms]
  | .held _ hs b => by
    simp [Expr.substRows, Expr.divFree, exprsDivFree_substRows hs, Expr.divFree_substRows b]

theorem exprsDivFree_substRows : ∀ es : List Expr, exprsDivFree lim (substExprRows s es) = exprsDivFree lim es
  | [] => rfl
  | e :: es => by simp [substExprRows, exprsDivFree, Expr.divFree_substRows e, exprsDivFree_substRows es]

theorem fieldsDivFree_substRows :
    ∀ fs : List (Name × Expr), fieldsDivFree lim (substFieldRows s fs) = fieldsDivFree lim fs
  | [] => rfl
  | (_, e) :: fs => by simp [substFieldRows, fieldsDivFree, Expr.divFree_substRows e, fieldsDivFree_substRows fs]

theorem argsDivFree_substRows : ∀ args : List Arg, argsDivFree lim (substArgRows s args) = argsDivFree lim args
  | [] => rfl
  | .value e :: args => by simp [substArgRows, argsDivFree, Expr.divFree_substRows e, argsDivFree_substRows args]
  | .inout ⟨_, p⟩ :: args => by
    simp [substArgRows, argsDivFree, pathDivFree_substRows p, argsDivFree_substRows args]

theorem pathDivFree_substRows : ∀ p : List Projection, pathDivFree lim (substPathRows s p) = pathDivFree lim p
  | [] => rfl
  | .field _ :: p => by simpa [substPathRows, pathDivFree] using pathDivFree_substRows p
  | .index i :: p => by simp [substPathRows, pathDivFree, Expr.divFree_substRows i, pathDivFree_substRows p]

theorem armsDivFree_substRows : ∀ arms : List Arm, armsDivFree lim (substArmRows s arms) = armsDivFree lim arms
  | [] => rfl
  | ⟨_, _, b⟩ :: arms => by simp [substArmRows, armsDivFree, Expr.divFree_substRows b, armsDivFree_substRows arms]

end

variable (B : Name → Nat)

mutual

theorem Expr.needs_substRows : ∀ e : Expr, (e.substRows s).needs B = e.needs B
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .closure .. => rfl
  | .record _ _ fs => by simp [Expr.substRows, Expr.needs, fieldsNeeds_substRows fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by simp [Expr.substRows, Expr.needs, exprsNeeds_substRows es]
  | .field e _ | .raise e | .perform _ e | .try e | .loop e | .return e => by
    simp [Expr.substRows, Expr.needs, Expr.needs_substRows e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b | .while a b
  | .tryCatch a _ _ b _ => by
    simp [Expr.substRows, Expr.needs, Expr.needs_substRows a, Expr.needs_substRows b]
  | .call f args _ => by
    simp [Expr.substRows, Expr.needs, Expr.needs_substRows f, Expr.bodyNeeds_substRows f, argsNeeds_substRows args]
  | .assign ⟨_, p⟩ v => by simp [Expr.substRows, Expr.needs, pathNeeds_substRows p, Expr.needs_substRows v]
  | .if c _ a b => by
    simp [Expr.substRows, Expr.needs, Expr.needs_substRows c, Expr.needs_substRows a, Expr.needs_substRows b]
  | .match e _ arms => by simp [Expr.substRows, Expr.needs, Expr.needs_substRows e, armsNeeds_substRows arms]

  | .held _ hs b => by simp [Expr.substRows, Expr.needs, exprsNeeds_substRows hs, Expr.needs_substRows b]
theorem Expr.bodyNeeds_substRows : ∀ e : Expr, (e.substRows s).bodyNeeds B = e.bodyNeeds B
  | .closure _ _ _ b => by simp [Expr.substRows, Expr.bodyNeeds, Expr.needs_substRows b]
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .record .. | .variant .. | .list .. | .op .. | .view _ | .field .. | .index .. | .call .. | .letIn ..
  | .varIn .. | .seq .. | .if .. | .match .. | .for .. | .raise .. | .perform _ .. | .withH .. | .held .. | .try .. | .tryCatch ..
  | .while .. | .loop .. | .return .. => rfl
  | .assign ⟨_, _⟩ _ => rfl

theorem exprsNeeds_substRows : ∀ es : List Expr, exprsNeeds B (substExprRows s es) = exprsNeeds B es
  | [] => rfl
  | e :: es => by simp [substExprRows, exprsNeeds, Expr.needs_substRows e, exprsNeeds_substRows es]

theorem fieldsNeeds_substRows :
    ∀ fs : List (Name × Expr), fieldsNeeds B (substFieldRows s fs) = fieldsNeeds B fs
  | [] => rfl
  | (_, e) :: fs => by simp [substFieldRows, fieldsNeeds, Expr.needs_substRows e, fieldsNeeds_substRows fs]

theorem argsNeeds_substRows : ∀ args : List Arg, argsNeeds B (substArgRows s args) = argsNeeds B args
  | [] => rfl
  | .value e :: args => by simp [substArgRows, argsNeeds, Expr.needs_substRows e, argsNeeds_substRows args]
  | .inout ⟨_, p⟩ :: args => by simp [substArgRows, argsNeeds, pathNeeds_substRows p, argsNeeds_substRows args]

theorem pathNeeds_substRows : ∀ p : List Projection, pathNeeds B (substPathRows s p) = pathNeeds B p
  | [] => rfl
  | .field _ :: p => by simpa [substPathRows, pathNeeds] using pathNeeds_substRows p
  | .index i :: p => by simp [substPathRows, pathNeeds, Expr.needs_substRows i, pathNeeds_substRows p]

theorem armsNeeds_substRows : ∀ arms : List Arm, armsNeeds B (substArmRows s arms) = armsNeeds B arms
  | [] => rfl
  | ⟨_, _, b⟩ :: arms => by simp [substArmRows, armsNeeds, Expr.needs_substRows b, armsNeeds_substRows arms]

end

end

end Stilt
