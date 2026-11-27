import Stilt.Ends.Instances

/-!
# Instantiation keeps the depth

Instantiation rewrites types alone, so an instantiated body has the same depth as the body.
-/

namespace Stilt

section

variable (s : TySubst)

mutual

theorem Expr.depth_substTys : ∀ e : Expr, (e.substTys s).depth = e.depth
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method .. => rfl
  | .closure _ _ _ b => by simp [Expr.substTys, Expr.depth, Expr.depth_substTys b]
  | .record _ _ fs => by simp [Expr.substTys, Expr.depth, fieldsDepth_substTys fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by
    simp [Expr.substTys, Expr.depth, exprsDepth_substTys es]
  | .field e _ | .raise e | .perform _ e | .try e | .form _ e | .loop e | .return e => by
    simp [Expr.substTys, Expr.depth, Expr.depth_substTys e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b
  | .while a b | .tryCatch a _ _ b _ => by
    simp [Expr.substTys, Expr.depth, Expr.depth_substTys a, Expr.depth_substTys b]
  | .call f args _ => by
    simp [Expr.substTys, Expr.depth, Expr.depth_substTys f, Expr.bodyDepth_substTys f,
      argsDepth_substTys args]
  | .assign ⟨_, p⟩ v => by
    simp [Expr.substTys, Expr.depth, pathDepth_substTys p, Expr.depth_substTys v]
  | .if c _ a b => by
    simp [Expr.substTys, Expr.depth, Expr.depth_substTys c, Expr.depth_substTys a,
      Expr.depth_substTys b]
  | .match e _ arms => by
    simp [Expr.substTys, Expr.depth, Expr.depth_substTys e, armsDepth_substTys arms]
  | .held _ hs b => by
    simp [Expr.substTys, Expr.depth, exprsDepth_substTys hs, Expr.depth_substTys b]

theorem Expr.bodyDepth_substTys : ∀ e : Expr, (e.substTys s).bodyDepth = e.bodyDepth
  | .closure _ _ _ b => by simp [Expr.substTys, Expr.bodyDepth, Expr.depth_substTys b]
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .record .. | .variant .. | .list .. | .op .. | .view _ | .field .. | .index .. | .call ..
  | .letIn .. | .varIn .. | .seq .. | .if .. | .match .. | .for .. | .raise .. | .perform _ ..
  | .withH .. | .held .. | .try .. | .form .. | .tryCatch .. | .assign ⟨_, _⟩ _ | .while .. | .loop _
  | .return _ => rfl

theorem exprsDepth_substTys : ∀ es : List Expr, exprsDepth (substExprTys s es) = exprsDepth es
  | [] => rfl
  | e :: es => by simp [substExprTys, exprsDepth, Expr.depth_substTys e, exprsDepth_substTys es]

theorem fieldsDepth_substTys :
    ∀ fs : List (Name × Expr), fieldsDepth (substFieldTys s fs) = fieldsDepth fs
  | [] => rfl
  | (_, e) :: fs => by
    simp [substFieldTys, fieldsDepth, Expr.depth_substTys e, fieldsDepth_substTys fs]

theorem argsDepth_substTys : ∀ args : List Arg, argsDepth (substArgTys s args) = argsDepth args
  | [] => rfl
  | .value e :: args => by
    simp [substArgTys, argsDepth, Expr.depth_substTys e, argsDepth_substTys args]
  | .inout ⟨_, p⟩ :: args => by
    simp [substArgTys, argsDepth, pathDepth_substTys p, argsDepth_substTys args]

theorem pathDepth_substTys : ∀ p : List Projection, pathDepth (substPathTys s p) = pathDepth p
  | [] => rfl
  | .field _ :: p => by simpa [substPathTys, pathDepth] using pathDepth_substTys p
  | .index i :: p => by simp [substPathTys, pathDepth, Expr.depth_substTys i, pathDepth_substTys p]

theorem armsDepth_substTys : ∀ arms : List Arm, armsDepth (substArmTys s arms) = armsDepth arms
  | [] => rfl
  | ⟨_, _, g, b⟩ :: arms => by
    simp [substArmTys, armsDepth, guardDepth_substTys g, Expr.depth_substTys b,
      armsDepth_substTys arms]

theorem guardDepth_substTys : ∀ g : Option Expr, guardDepth (substGuardTys s g) = guardDepth g
  | none => rfl
  | some g => by simp [substGuardTys, guardDepth, Expr.depth_substTys g]

end

end

section

variable (s : RowSubst)

mutual

theorem Expr.depth_substRows : ∀ e : Expr, (e.substRows s).depth = e.depth
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method .. => rfl
  | .closure _ _ _ b => by simp [Expr.substRows, Expr.depth, Expr.depth_substRows b]
  | .record _ _ fs => by simp [Expr.substRows, Expr.depth, fieldsDepth_substRows fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by
    simp [Expr.substRows, Expr.depth, exprsDepth_substRows es]
  | .field e _ | .raise e | .perform _ e | .try e | .form _ e | .loop e | .return e => by
    simp [Expr.substRows, Expr.depth, Expr.depth_substRows e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b
  | .while a b | .tryCatch a _ _ b _ => by
    simp [Expr.substRows, Expr.depth, Expr.depth_substRows a, Expr.depth_substRows b]
  | .call f args _ => by
    simp [Expr.substRows, Expr.depth, Expr.depth_substRows f, Expr.bodyDepth_substRows f,
      argsDepth_substRows args]
  | .assign ⟨_, p⟩ v => by
    simp [Expr.substRows, Expr.depth, pathDepth_substRows p, Expr.depth_substRows v]
  | .if c _ a b => by
    simp [Expr.substRows, Expr.depth, Expr.depth_substRows c, Expr.depth_substRows a,
      Expr.depth_substRows b]
  | .match e _ arms => by
    simp [Expr.substRows, Expr.depth, Expr.depth_substRows e, armsDepth_substRows arms]
  | .held _ hs b => by
    simp [Expr.substRows, Expr.depth, exprsDepth_substRows hs, Expr.depth_substRows b]

theorem Expr.bodyDepth_substRows : ∀ e : Expr, (e.substRows s).bodyDepth = e.bodyDepth
  | .closure _ _ _ b => by simp [Expr.substRows, Expr.bodyDepth, Expr.depth_substRows b]
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .record .. | .variant .. | .list .. | .op .. | .view _ | .field .. | .index .. | .call ..
  | .letIn .. | .varIn .. | .seq .. | .if .. | .match .. | .for .. | .raise .. | .perform _ ..
  | .withH .. | .held .. | .try .. | .form .. | .tryCatch .. | .assign ⟨_, _⟩ _ | .while .. | .loop _
  | .return _ => rfl

theorem exprsDepth_substRows : ∀ es : List Expr, exprsDepth (substExprRows s es) = exprsDepth es
  | [] => rfl
  | e :: es => by simp [substExprRows, exprsDepth, Expr.depth_substRows e, exprsDepth_substRows es]

theorem fieldsDepth_substRows :
    ∀ fs : List (Name × Expr), fieldsDepth (substFieldRows s fs) = fieldsDepth fs
  | [] => rfl
  | (_, e) :: fs => by
    simp [substFieldRows, fieldsDepth, Expr.depth_substRows e, fieldsDepth_substRows fs]

theorem argsDepth_substRows : ∀ args : List Arg, argsDepth (substArgRows s args) = argsDepth args
  | [] => rfl
  | .value e :: args => by
    simp [substArgRows, argsDepth, Expr.depth_substRows e, argsDepth_substRows args]
  | .inout ⟨_, p⟩ :: args => by
    simp [substArgRows, argsDepth, pathDepth_substRows p, argsDepth_substRows args]

theorem pathDepth_substRows : ∀ p : List Projection, pathDepth (substPathRows s p) = pathDepth p
  | [] => rfl
  | .field _ :: p => by simpa [substPathRows, pathDepth] using pathDepth_substRows p
  | .index i :: p => by simp [substPathRows, pathDepth, Expr.depth_substRows i, pathDepth_substRows p]

theorem armsDepth_substRows : ∀ arms : List Arm, armsDepth (substArmRows s arms) = armsDepth arms
  | [] => rfl
  | ⟨_, _, g, b⟩ :: arms => by
    simp [substArmRows, armsDepth, guardDepth_substRows g, Expr.depth_substRows b,
      armsDepth_substRows arms]

theorem guardDepth_substRows : ∀ g : Option Expr, guardDepth (substGuardRows s g) = guardDepth g
  | none => rfl
  | some g => by simp [substGuardRows, guardDepth, Expr.depth_substRows g]

end

end

end Stilt
