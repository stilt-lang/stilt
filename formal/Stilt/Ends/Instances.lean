import Stilt.Ends.Syntax
import Stilt.Ends.CountInstances
import Stilt.Generics.Commute

/-!
# Instantiation keeps the check

Instantiation rewrites types alone, so an instantiated body holds the same
sites of `div`, gives its variables the same roles, and has the same depth, as the body.
-/

namespace Stilt

section

variable (s : TySubst) {lim : Limited} {B : Name → Nat} {me : Option (Name × Nat)}

theorem Expr.callable_substTys (e : Expr) : (e.substTys s).callable = e.callable := by
  cases e <;> first | rfl | (rename_i t _; cases t; rfl)

theorem Expr.isSelf_substTys (e : Expr) : (e.substTys s).isSelf me = e.isSelf me := by
  cases e <;> first | rfl | (rename_i t _; cases t; rfl)

theorem Expr.roleIn_substTys (R : Roles) : ∀ e : Expr, (e.substTys s).roleIn R = e.roleIn R
  | .field e _ => by simp [Expr.substTys, Expr.roleIn, Expr.roleIn_substTys R e]
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .record .. | .variant .. | .list .. | .op .. | .view _ | .index .. | .call .. | .letIn ..
  | .varIn .. | .seq .. | .if .. | .match .. | .for .. | .raise .. | .perform _ .. | .withH ..
  | .held .. | .try .. | .tryCatch .. | .closure .. | .assign ⟨_, _⟩ _ | .while .. | .loop _
  | .return _ => rfl

theorem argPart_substTys (R : Roles) : ∀ (k : Nat) (args : List Arg),
    argPart R k (substArgTys s args) = argPart R k args
  | 0, .value e :: _ => by simp [substArgTys, argPart, Expr.roleIn_substTys s R e]
  | 0, .inout ⟨_, _⟩ :: _ => rfl
  | k + 1, .value _ :: args | k + 1, .inout ⟨_, _⟩ :: args => by
    simp [substArgTys, argPart, argPart_substTys R k args]
  | 0, [] | _ + 1, [] => rfl

theorem descends_substTys (R : Roles) (args : List Arg) :
    descends me R (substArgTys s args) = descends me R args := by
  simp [descends, argPart_substTys]

mutual

theorem Expr.divFree_substTys : ∀ (R : Roles) (e : Expr),
    (e.substTys s).divFree lim B me R = e.divFree lim B me R
  | _, .var _ | _, .move _ | _, .int _ | _, .bool _ | _, .unit | _, .break | _, .continue
  | _, .fnRef .. | _, .method .. => rfl
  | R, .record _ _ fs => by simp [Expr.substTys, Expr.divFree, fieldsDivFree_substTys R fs]
  | R, .variant _ _ _ es | R, .list _ es | R, .op _ es | R, .view es => by
    simp [Expr.substTys, Expr.divFree, exprsDivFree_substTys R es]
  | _, .closure _ _ _ e => by simp [Expr.substTys, Expr.divFree, Expr.divFree_substTys [] e]
  | R, .field e _ | R, .raise e | R, .try e | R, .return e => by
    simp [Expr.substTys, Expr.divFree, Expr.divFree_substTys R e]
  | _, .perform _ _ | _, .loop _ => rfl
  | R, .index a b | R, .seq a b | R, .withH _ _ a b => by
    simp [Expr.substTys, Expr.divFree, Expr.divFree_substTys R a, Expr.divFree_substTys R b]
  | R, .letIn x _ a b => by
    simp [Expr.substTys, Expr.divFree, Expr.divFree_substTys R a, Expr.divFree_substTys _ b,
      Expr.writes_substTys, Expr.roleIn_substTys]
  | R, .varIn x _ a b => by
    simp [Expr.substTys, Expr.divFree, Expr.divFree_substTys R a, Expr.divFree_substTys _ b]
  | R, .for _ _ a b | R, .tryCatch a _ _ b _ => by
    simp [Expr.substTys, Expr.divFree, Expr.divFree_substTys R a, Expr.divFree_substTys [] b]
  | _, .while a b => by
    simp [Expr.substTys, Expr.divFree, Expr.divFree_substTys [] a, Expr.divFree_substTys [] b,
      Expr.countsIn_substTys]
  | R, .call f args _ => by
    simp [Expr.substTys, Expr.divFree, Expr.callable_substTys s f, Expr.isSelf_substTys s f,
      Expr.divFree_substTys R f, argsDivFree_substTys R args, descends_substTys]
  | R, .assign ⟨_, p⟩ v => by
    simp [Expr.substTys, Expr.divFree, pathDivFree_substTys R p, Expr.divFree_substTys R v]
  | R, .if c _ a b => by
    simp [Expr.substTys, Expr.divFree, Expr.divFree_substTys R c, Expr.divFree_substTys R a,
      Expr.divFree_substTys R b]
  | R, .match e _ arms => by
    simp [Expr.substTys, Expr.divFree, Expr.divFree_substTys R e, armsDivFree_substTys R _ arms,
      Expr.roleIn_substTys]
  | R, .held _ hs b => by
    simp [Expr.substTys, Expr.divFree, exprsDivFree_substTys R hs, Expr.divFree_substTys [] b]

theorem exprsDivFree_substTys : ∀ (R : Roles) (es : List Expr),
    exprsDivFree lim B me R (substExprTys s es) = exprsDivFree lim B me R es
  | _, [] => rfl
  | R, e :: es => by
    simp [substExprTys, exprsDivFree, Expr.divFree_substTys R e, exprsDivFree_substTys R es]

theorem fieldsDivFree_substTys : ∀ (R : Roles) (fs : List (Name × Expr)),
    fieldsDivFree lim B me R (substFieldTys s fs) = fieldsDivFree lim B me R fs
  | _, [] => rfl
  | R, (_, e) :: fs => by
    simp [substFieldTys, fieldsDivFree, Expr.divFree_substTys R e, fieldsDivFree_substTys R fs]

theorem argsDivFree_substTys : ∀ (R : Roles) (args : List Arg),
    argsDivFree lim B me R (substArgTys s args) = argsDivFree lim B me R args
  | _, [] => rfl
  | R, .value e :: args => by
    simp [substArgTys, argsDivFree, Expr.divFree_substTys R e, argsDivFree_substTys R args]
  | R, .inout ⟨_, p⟩ :: args => by
    simp [substArgTys, argsDivFree, pathDivFree_substTys R p, argsDivFree_substTys R args]

theorem pathDivFree_substTys : ∀ (R : Roles) (p : List Projection),
    pathDivFree lim B me R (substPathTys s p) = pathDivFree lim B me R p
  | _, [] => rfl
  | R, .field _ :: p => by simpa [substPathTys, pathDivFree] using pathDivFree_substTys R p
  | R, .index i :: p => by
    simp [substPathTys, pathDivFree, Expr.divFree_substTys R i, pathDivFree_substTys R p]

theorem armsDivFree_substTys : ∀ (R : Roles) (r : Role) (arms : List Arm),
    armsDivFree lim B me R r (substArmTys s arms) = armsDivFree lim B me R r arms
  | _, _, [] => rfl
  | R, r, ⟨_, _, b⟩ :: arms => by
    simp [substArmTys, armsDivFree, Expr.divFree_substTys _ b, armsDivFree_substTys R r arms,
      Arm.role, Expr.writes_substTys]

end

mutual

theorem Expr.depth_substTys : ∀ e : Expr, (e.substTys s).depth = e.depth
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .closure .. => rfl
  | .record _ _ fs => by simp [Expr.substTys, Expr.depth, fieldsDepth_substTys fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by
    simp [Expr.substTys, Expr.depth, exprsDepth_substTys es]
  | .field e _ | .raise e | .perform _ e | .try e | .loop e | .return e => by
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
  | .withH .. | .held .. | .try .. | .tryCatch .. | .assign ⟨_, _⟩ _ | .while .. | .loop _
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
  | ⟨_, _, b⟩ :: arms => by
    simp [substArmTys, armsDepth, Expr.depth_substTys b, armsDepth_substTys arms]

end

end

section

variable (s : RowSubst) {lim : Limited} {B : Name → Nat} {me : Option (Name × Nat)}

theorem Expr.callable_substRows (e : Expr) : (e.substRows s).callable = e.callable := by
  cases e <;> first | rfl | (rename_i t _; cases t; rfl)

theorem Expr.isSelf_substRows (e : Expr) : (e.substRows s).isSelf me = e.isSelf me := by
  cases e <;> first | rfl | (rename_i t _; cases t; rfl)

theorem Expr.roleIn_substRows (R : Roles) : ∀ e : Expr, (e.substRows s).roleIn R = e.roleIn R
  | .field e _ => by simp [Expr.substRows, Expr.roleIn, Expr.roleIn_substRows R e]
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .record .. | .variant .. | .list .. | .op .. | .view _ | .index .. | .call .. | .letIn ..
  | .varIn .. | .seq .. | .if .. | .match .. | .for .. | .raise .. | .perform _ .. | .withH ..
  | .held .. | .try .. | .tryCatch .. | .closure .. | .assign ⟨_, _⟩ _ | .while .. | .loop _
  | .return _ => rfl

theorem argPart_substRows (R : Roles) : ∀ (k : Nat) (args : List Arg),
    argPart R k (substArgRows s args) = argPart R k args
  | 0, .value e :: _ => by simp [substArgRows, argPart, Expr.roleIn_substRows s R e]
  | 0, .inout ⟨_, _⟩ :: _ => rfl
  | k + 1, .value _ :: args | k + 1, .inout ⟨_, _⟩ :: args => by
    simp [substArgRows, argPart, argPart_substRows R k args]
  | 0, [] | _ + 1, [] => rfl

theorem descends_substRows (R : Roles) (args : List Arg) :
    descends me R (substArgRows s args) = descends me R args := by
  simp [descends, argPart_substRows]

mutual

theorem Expr.divFree_substRows : ∀ (R : Roles) (e : Expr),
    (e.substRows s).divFree lim B me R = e.divFree lim B me R
  | _, .var _ | _, .move _ | _, .int _ | _, .bool _ | _, .unit | _, .break | _, .continue
  | _, .fnRef .. | _, .method .. => rfl
  | R, .record _ _ fs => by simp [Expr.substRows, Expr.divFree, fieldsDivFree_substRows R fs]
  | R, .variant _ _ _ es | R, .list _ es | R, .op _ es | R, .view es => by
    simp [Expr.substRows, Expr.divFree, exprsDivFree_substRows R es]
  | _, .closure _ _ _ e => by simp [Expr.substRows, Expr.divFree, Expr.divFree_substRows [] e]
  | R, .field e _ | R, .raise e | R, .try e | R, .return e => by
    simp [Expr.substRows, Expr.divFree, Expr.divFree_substRows R e]
  | _, .perform _ _ | _, .loop _ => rfl
  | R, .index a b | R, .seq a b | R, .withH _ _ a b => by
    simp [Expr.substRows, Expr.divFree, Expr.divFree_substRows R a, Expr.divFree_substRows R b]
  | R, .letIn x _ a b => by
    simp [Expr.substRows, Expr.divFree, Expr.divFree_substRows R a, Expr.divFree_substRows _ b,
      Expr.writes_substRows, Expr.roleIn_substRows]
  | R, .varIn x _ a b => by
    simp [Expr.substRows, Expr.divFree, Expr.divFree_substRows R a, Expr.divFree_substRows _ b]
  | R, .for _ _ a b | R, .tryCatch a _ _ b _ => by
    simp [Expr.substRows, Expr.divFree, Expr.divFree_substRows R a, Expr.divFree_substRows [] b]
  | _, .while a b => by
    simp [Expr.substRows, Expr.divFree, Expr.divFree_substRows [] a, Expr.divFree_substRows [] b,
      Expr.countsIn_substRows]
  | R, .call f args _ => by
    simp [Expr.substRows, Expr.divFree, Expr.callable_substRows s f, Expr.isSelf_substRows s f,
      Expr.divFree_substRows R f, argsDivFree_substRows R args, descends_substRows]
  | R, .assign ⟨_, p⟩ v => by
    simp [Expr.substRows, Expr.divFree, pathDivFree_substRows R p, Expr.divFree_substRows R v]
  | R, .if c _ a b => by
    simp [Expr.substRows, Expr.divFree, Expr.divFree_substRows R c, Expr.divFree_substRows R a,
      Expr.divFree_substRows R b]
  | R, .match e _ arms => by
    simp [Expr.substRows, Expr.divFree, Expr.divFree_substRows R e, armsDivFree_substRows R _ arms,
      Expr.roleIn_substRows]
  | R, .held _ hs b => by
    simp [Expr.substRows, Expr.divFree, exprsDivFree_substRows R hs, Expr.divFree_substRows [] b]

theorem exprsDivFree_substRows : ∀ (R : Roles) (es : List Expr),
    exprsDivFree lim B me R (substExprRows s es) = exprsDivFree lim B me R es
  | _, [] => rfl
  | R, e :: es => by
    simp [substExprRows, exprsDivFree, Expr.divFree_substRows R e, exprsDivFree_substRows R es]

theorem fieldsDivFree_substRows : ∀ (R : Roles) (fs : List (Name × Expr)),
    fieldsDivFree lim B me R (substFieldRows s fs) = fieldsDivFree lim B me R fs
  | _, [] => rfl
  | R, (_, e) :: fs => by
    simp [substFieldRows, fieldsDivFree, Expr.divFree_substRows R e, fieldsDivFree_substRows R fs]

theorem argsDivFree_substRows : ∀ (R : Roles) (args : List Arg),
    argsDivFree lim B me R (substArgRows s args) = argsDivFree lim B me R args
  | _, [] => rfl
  | R, .value e :: args => by
    simp [substArgRows, argsDivFree, Expr.divFree_substRows R e, argsDivFree_substRows R args]
  | R, .inout ⟨_, p⟩ :: args => by
    simp [substArgRows, argsDivFree, pathDivFree_substRows R p, argsDivFree_substRows R args]

theorem pathDivFree_substRows : ∀ (R : Roles) (p : List Projection),
    pathDivFree lim B me R (substPathRows s p) = pathDivFree lim B me R p
  | _, [] => rfl
  | R, .field _ :: p => by simpa [substPathRows, pathDivFree] using pathDivFree_substRows R p
  | R, .index i :: p => by
    simp [substPathRows, pathDivFree, Expr.divFree_substRows R i, pathDivFree_substRows R p]

theorem armsDivFree_substRows : ∀ (R : Roles) (r : Role) (arms : List Arm),
    armsDivFree lim B me R r (substArmRows s arms) = armsDivFree lim B me R r arms
  | _, _, [] => rfl
  | R, r, ⟨_, _, b⟩ :: arms => by
    simp [substArmRows, armsDivFree, Expr.divFree_substRows _ b, armsDivFree_substRows R r arms,
      Arm.role, Expr.writes_substRows]

end

mutual

theorem Expr.depth_substRows : ∀ e : Expr, (e.substRows s).depth = e.depth
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .closure .. => rfl
  | .record _ _ fs => by simp [Expr.substRows, Expr.depth, fieldsDepth_substRows fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by
    simp [Expr.substRows, Expr.depth, exprsDepth_substRows es]
  | .field e _ | .raise e | .perform _ e | .try e | .loop e | .return e => by
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
  | .withH .. | .held .. | .try .. | .tryCatch .. | .assign ⟨_, _⟩ _ | .while .. | .loop _
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
  | ⟨_, _, b⟩ :: arms => by
    simp [substArmRows, armsDepth, Expr.depth_substRows b, armsDepth_substRows arms]

end

end

end Stilt
