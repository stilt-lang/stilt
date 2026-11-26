import Stilt.Locks.Syntax
import Stilt.Generics.Commute

/-!
# Instantiation keeps the fact

Instantiation rewrites types and rows alone, and a site of `locks` is a `when`, a name of a
function or a method's name, none of which it changes: an instantiated body holds a site of
`locks` exactly when the body does (shared.locks).
-/

namespace Stilt

variable (D : Decls) (L : List Name)

section

variable (s : TySubst)

mutual

theorem Expr.lockFree_substTys : ∀ e : Expr, (e.substTys s).lockFree D L = e.lockFree D L
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .held .. => rfl
  | .closure _ _ _ b => by simp only [Expr.substTys, Expr.lockFree, Expr.lockFree_substTys b]
  | .record _ _ fs => by simp [Expr.substTys, Expr.lockFree, fieldsLockFree_substTys fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by
    simp [Expr.substTys, Expr.lockFree, exprsLockFree_substTys es]
  | .field e _ | .raise e | .perform _ e | .try e | .form _ e | .loop e | .return e => by
    simp [Expr.substTys, Expr.lockFree, Expr.lockFree_substTys e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b
  | .tryCatch a _ _ b _ | .while a b => by
    simp [Expr.substTys, Expr.lockFree, Expr.lockFree_substTys a, Expr.lockFree_substTys b]
  | .call f args _ => by
    simp [Expr.substTys, Expr.lockFree, Expr.lockFree_substTys f, argsLockFree_substTys args]
  | .assign ⟨_, p⟩ v => by
    simp [Expr.substTys, Expr.lockFree, pathLockFree_substTys p, Expr.lockFree_substTys v]
  | .if c _ a b => by
    simp [Expr.substTys, Expr.lockFree, Expr.lockFree_substTys c, Expr.lockFree_substTys a,
      Expr.lockFree_substTys b]
  | .match e _ arms => by
    simp [Expr.substTys, Expr.lockFree, Expr.lockFree_substTys e, armsLockFree_substTys arms]

theorem exprsLockFree_substTys : ∀ es : List Expr,
    exprsLockFree D L (substExprTys s es) = exprsLockFree D L es
  | [] => rfl
  | e :: es => by
    simp [substExprTys, exprsLockFree, Expr.lockFree_substTys e, exprsLockFree_substTys es]

theorem fieldsLockFree_substTys : ∀ fs : List (Name × Expr),
    fieldsLockFree D L (substFieldTys s fs) = fieldsLockFree D L fs
  | [] => rfl
  | (_, e) :: fs => by
    simp [substFieldTys, fieldsLockFree, Expr.lockFree_substTys e, fieldsLockFree_substTys fs]

theorem argsLockFree_substTys : ∀ args : List Arg,
    argsLockFree D L (substArgTys s args) = argsLockFree D L args
  | [] => rfl
  | .value e :: args => by
    simp [substArgTys, argsLockFree, Expr.lockFree_substTys e, argsLockFree_substTys args]
  | .inout ⟨_, p⟩ :: args => by
    simp [substArgTys, argsLockFree, pathLockFree_substTys p, argsLockFree_substTys args]

theorem pathLockFree_substTys : ∀ p : List Projection,
    pathLockFree D L (substPathTys s p) = pathLockFree D L p
  | [] => rfl
  | .field _ :: p => by simpa [substPathTys, pathLockFree] using pathLockFree_substTys p
  | .index i :: p => by
    simp [substPathTys, pathLockFree, Expr.lockFree_substTys i, pathLockFree_substTys p]

theorem armsLockFree_substTys : ∀ arms : List Arm,
    armsLockFree D L (substArmTys s arms) = armsLockFree D L arms
  | [] => rfl
  | ⟨_, _, b⟩ :: arms => by
    simp [substArmTys, armsLockFree, Expr.lockFree_substTys b, armsLockFree_substTys arms]

end

end

section

variable (s : RowSubst)

mutual

theorem Expr.lockFree_substRows : ∀ e : Expr, (e.substRows s).lockFree D L = e.lockFree D L
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .held .. => rfl
  | .closure _ _ _ b => by simp only [Expr.substRows, Expr.lockFree, Expr.lockFree_substRows b]
  | .record _ _ fs => by simp [Expr.substRows, Expr.lockFree, fieldsLockFree_substRows fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by
    simp [Expr.substRows, Expr.lockFree, exprsLockFree_substRows es]
  | .field e _ | .raise e | .perform _ e | .try e | .form _ e | .loop e | .return e => by
    simp [Expr.substRows, Expr.lockFree, Expr.lockFree_substRows e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b
  | .tryCatch a _ _ b _ | .while a b => by
    simp [Expr.substRows, Expr.lockFree, Expr.lockFree_substRows a, Expr.lockFree_substRows b]
  | .call f args _ => by
    simp [Expr.substRows, Expr.lockFree, Expr.lockFree_substRows f, argsLockFree_substRows args]
  | .assign ⟨_, p⟩ v => by
    simp [Expr.substRows, Expr.lockFree, pathLockFree_substRows p, Expr.lockFree_substRows v]
  | .if c _ a b => by
    simp [Expr.substRows, Expr.lockFree, Expr.lockFree_substRows c, Expr.lockFree_substRows a,
      Expr.lockFree_substRows b]
  | .match e _ arms => by
    simp [Expr.substRows, Expr.lockFree, Expr.lockFree_substRows e, armsLockFree_substRows arms]

theorem exprsLockFree_substRows : ∀ es : List Expr,
    exprsLockFree D L (substExprRows s es) = exprsLockFree D L es
  | [] => rfl
  | e :: es => by
    simp [substExprRows, exprsLockFree, Expr.lockFree_substRows e, exprsLockFree_substRows es]

theorem fieldsLockFree_substRows : ∀ fs : List (Name × Expr),
    fieldsLockFree D L (substFieldRows s fs) = fieldsLockFree D L fs
  | [] => rfl
  | (_, e) :: fs => by
    simp [substFieldRows, fieldsLockFree, Expr.lockFree_substRows e, fieldsLockFree_substRows fs]

theorem argsLockFree_substRows : ∀ args : List Arg,
    argsLockFree D L (substArgRows s args) = argsLockFree D L args
  | [] => rfl
  | .value e :: args => by
    simp [substArgRows, argsLockFree, Expr.lockFree_substRows e, argsLockFree_substRows args]
  | .inout ⟨_, p⟩ :: args => by
    simp [substArgRows, argsLockFree, pathLockFree_substRows p, argsLockFree_substRows args]

theorem pathLockFree_substRows : ∀ p : List Projection,
    pathLockFree D L (substPathRows s p) = pathLockFree D L p
  | [] => rfl
  | .field _ :: p => by simpa [substPathRows, pathLockFree] using pathLockFree_substRows p
  | .index i :: p => by
    simp [substPathRows, pathLockFree, Expr.lockFree_substRows i, pathLockFree_substRows p]

theorem armsLockFree_substRows : ∀ arms : List Arm,
    armsLockFree D L (substArmRows s arms) = armsLockFree D L arms
  | [] => rfl
  | ⟨_, _, b⟩ :: arms => by
    simp [substArmRows, armsLockFree, Expr.lockFree_substRows b, armsLockFree_substRows arms]

end

end

end Stilt
