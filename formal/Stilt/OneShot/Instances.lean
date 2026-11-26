import Stilt.OneShot.Syntax
import Stilt.Generics.Commute

/-!
# Instantiation keeps the check

Instantiation rewrites types and rows alone, and a row keeps its own `resume`,
so an instantiated body performs as many `resume`s, and passes the check of
handlers.resume-at-most-once as the body does.
-/

namespace Stilt

section

variable (s : TySubst)

mutual

theorem Expr.resumes_substTys : ∀ e : Expr, (e.substTys s).resumes = e.resumes
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .closure .. => rfl
  | .record _ _ fs => by simp [Expr.substTys, Expr.resumes, fieldsResumes_substTys fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by
    simp [Expr.substTys, Expr.resumes, exprsResumes_substTys es]
  | .field e _ | .raise e | .perform _ e | .try e | .form _ e | .loop e | .return e => by
    simp [Expr.substTys, Expr.resumes, Expr.resumes_substTys e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b
  | .tryCatch a _ _ b _ | .while a b => by
    simp [Expr.substTys, Expr.resumes, Expr.resumes_substTys a, Expr.resumes_substTys b]
  | .held _ hs b => by
    simp [Expr.substTys, Expr.resumes, exprsResumes_substTys hs, Expr.resumes_substTys b]
  | .call f args _ => by simp [Expr.substTys, Expr.resumes, Expr.resumes_substTys f, argsResumes_substTys args]
  | .assign ⟨_, p⟩ v => by
    simp [Expr.substTys, Expr.resumes, pathResumes_substTys p, Expr.resumes_substTys v]
  | .if c _ a b => by
    simp [Expr.substTys, Expr.resumes, Expr.resumes_substTys c, Expr.resumes_substTys a, Expr.resumes_substTys b]
  | .match e _ arms => by
    simp [Expr.substTys, Expr.resumes, Expr.resumes_substTys e, armsResumes_substTys arms]

theorem exprsResumes_substTys : ∀ es : List Expr, exprsResumes (substExprTys s es) = exprsResumes es
  | [] => rfl
  | e :: es => by simp [substExprTys, exprsResumes, Expr.resumes_substTys e, exprsResumes_substTys es]

theorem fieldsResumes_substTys :
    ∀ fs : List (Name × Expr), fieldsResumes (substFieldTys s fs) = fieldsResumes fs
  | [] => rfl
  | (_, e) :: fs => by simp [substFieldTys, fieldsResumes, Expr.resumes_substTys e, fieldsResumes_substTys fs]

theorem argsResumes_substTys : ∀ args : List Arg, argsResumes (substArgTys s args) = argsResumes args
  | [] => rfl
  | .value e :: args => by simp [substArgTys, argsResumes, Expr.resumes_substTys e, argsResumes_substTys args]
  | .inout ⟨_, p⟩ :: args => by
    simp [substArgTys, argsResumes, pathResumes_substTys p, argsResumes_substTys args]

theorem pathResumes_substTys : ∀ p : List Projection, pathResumes (substPathTys s p) = pathResumes p
  | [] => rfl
  | .field _ :: p => by simpa [substPathTys, pathResumes] using pathResumes_substTys p
  | .index i :: p => by simp [substPathTys, pathResumes, Expr.resumes_substTys i, pathResumes_substTys p]

theorem armsResumes_substTys : ∀ arms : List Arm, armsResumes (substArmTys s arms) = armsResumes arms
  | [] => rfl
  | ⟨_, _, b⟩ :: arms => by simp [substArmTys, armsResumes, Expr.resumes_substTys b, armsResumes_substTys arms]

end

mutual

theorem Expr.oneShot_substTys : ∀ e : Expr, (e.substTys s).oneShot = e.oneShot
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method .. => rfl
  | .closure _ _ _ b => by
    simp only [Expr.substTys, Expr.oneShot, Expr.oneShot_substTys b, Expr.resumes_substTys s b]
  | .record _ _ fs => by simp [Expr.substTys, Expr.oneShot, fieldsOneShot_substTys fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by
    simp [Expr.substTys, Expr.oneShot, exprsOneShot_substTys es]
  | .field e _ | .raise e | .perform _ e | .try e | .form _ e | .loop e | .return e => by
    simp [Expr.substTys, Expr.oneShot, Expr.oneShot_substTys e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b
  | .tryCatch a _ _ b _ | .while a b => by
    simp [Expr.substTys, Expr.oneShot, Expr.oneShot_substTys a, Expr.oneShot_substTys b]
  | .held _ hs b => by
    simp [Expr.substTys, Expr.oneShot, exprsOneShot_substTys hs, Expr.oneShot_substTys b]
  | .call f args _ => by simp [Expr.substTys, Expr.oneShot, Expr.oneShot_substTys f, argsOneShot_substTys args]
  | .assign ⟨_, p⟩ v => by
    simp [Expr.substTys, Expr.oneShot, pathOneShot_substTys p, Expr.oneShot_substTys v]
  | .if c _ a b => by
    simp [Expr.substTys, Expr.oneShot, Expr.oneShot_substTys c, Expr.oneShot_substTys a, Expr.oneShot_substTys b]
  | .match e _ arms => by
    simp [Expr.substTys, Expr.oneShot, Expr.oneShot_substTys e, armsOneShot_substTys arms]

theorem exprsOneShot_substTys : ∀ es : List Expr, exprsOneShot (substExprTys s es) = exprsOneShot es
  | [] => rfl
  | e :: es => by simp [substExprTys, exprsOneShot, Expr.oneShot_substTys e, exprsOneShot_substTys es]

theorem fieldsOneShot_substTys :
    ∀ fs : List (Name × Expr), fieldsOneShot (substFieldTys s fs) = fieldsOneShot fs
  | [] => rfl
  | (_, e) :: fs => by simp [substFieldTys, fieldsOneShot, Expr.oneShot_substTys e, fieldsOneShot_substTys fs]

theorem argsOneShot_substTys : ∀ args : List Arg, argsOneShot (substArgTys s args) = argsOneShot args
  | [] => rfl
  | .value e :: args => by simp [substArgTys, argsOneShot, Expr.oneShot_substTys e, argsOneShot_substTys args]
  | .inout ⟨_, p⟩ :: args => by
    simp [substArgTys, argsOneShot, pathOneShot_substTys p, argsOneShot_substTys args]

theorem pathOneShot_substTys : ∀ p : List Projection, pathOneShot (substPathTys s p) = pathOneShot p
  | [] => rfl
  | .field _ :: p => by simpa [substPathTys, pathOneShot] using pathOneShot_substTys p
  | .index i :: p => by simp [substPathTys, pathOneShot, Expr.oneShot_substTys i, pathOneShot_substTys p]

theorem armsOneShot_substTys : ∀ arms : List Arm, armsOneShot (substArmTys s arms) = armsOneShot arms
  | [] => rfl
  | ⟨_, _, b⟩ :: arms => by simp [substArmTys, armsOneShot, Expr.oneShot_substTys b, armsOneShot_substTys arms]

end

end

section

variable (s : RowSubst)

theorem Row.resumes_substRows (ρ : Row) : (ρ.substRows s).resumes = ρ.resumes := by
  simp only [Row.resumes, Row.substRows_resume]

mutual

theorem Expr.resumes_substRows : ∀ e : Expr, (e.substRows s).resumes = e.resumes
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .closure .. => rfl
  | .record _ _ fs => by simp [Expr.substRows, Expr.resumes, fieldsResumes_substRows fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by
    simp [Expr.substRows, Expr.resumes, exprsResumes_substRows es]
  | .field e _ | .raise e | .perform _ e | .try e | .form _ e | .loop e | .return e => by
    simp [Expr.substRows, Expr.resumes, Expr.resumes_substRows e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b
  | .tryCatch a _ _ b _ | .while a b => by
    simp [Expr.substRows, Expr.resumes, Expr.resumes_substRows a, Expr.resumes_substRows b]
  | .held _ hs b => by
    simp [Expr.substRows, Expr.resumes, exprsResumes_substRows hs, Expr.resumes_substRows b]
  | .call f args _ => by simp [Expr.substRows, Expr.resumes, Expr.resumes_substRows f, argsResumes_substRows args]
  | .assign ⟨_, p⟩ v => by
    simp [Expr.substRows, Expr.resumes, pathResumes_substRows p, Expr.resumes_substRows v]
  | .if c _ a b => by
    simp [Expr.substRows, Expr.resumes, Expr.resumes_substRows c, Expr.resumes_substRows a, Expr.resumes_substRows b]
  | .match e _ arms => by
    simp [Expr.substRows, Expr.resumes, Expr.resumes_substRows e, armsResumes_substRows arms]

theorem exprsResumes_substRows : ∀ es : List Expr, exprsResumes (substExprRows s es) = exprsResumes es
  | [] => rfl
  | e :: es => by simp [substExprRows, exprsResumes, Expr.resumes_substRows e, exprsResumes_substRows es]

theorem fieldsResumes_substRows :
    ∀ fs : List (Name × Expr), fieldsResumes (substFieldRows s fs) = fieldsResumes fs
  | [] => rfl
  | (_, e) :: fs => by simp [substFieldRows, fieldsResumes, Expr.resumes_substRows e, fieldsResumes_substRows fs]

theorem argsResumes_substRows : ∀ args : List Arg, argsResumes (substArgRows s args) = argsResumes args
  | [] => rfl
  | .value e :: args => by simp [substArgRows, argsResumes, Expr.resumes_substRows e, argsResumes_substRows args]
  | .inout ⟨_, p⟩ :: args => by
    simp [substArgRows, argsResumes, pathResumes_substRows p, argsResumes_substRows args]

theorem pathResumes_substRows : ∀ p : List Projection, pathResumes (substPathRows s p) = pathResumes p
  | [] => rfl
  | .field _ :: p => by simpa [substPathRows, pathResumes] using pathResumes_substRows p
  | .index i :: p => by simp [substPathRows, pathResumes, Expr.resumes_substRows i, pathResumes_substRows p]

theorem armsResumes_substRows : ∀ arms : List Arm, armsResumes (substArmRows s arms) = armsResumes arms
  | [] => rfl
  | ⟨_, _, b⟩ :: arms => by simp [substArmRows, armsResumes, Expr.resumes_substRows b, armsResumes_substRows arms]

end

mutual

theorem Expr.oneShot_substRows : ∀ e : Expr, (e.substRows s).oneShot = e.oneShot
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method .. => rfl
  | .closure _ _ _ b => by
    simp only [Expr.substRows, Expr.oneShot, Expr.oneShot_substRows b, Expr.resumes_substRows s b,
      Row.resumes_substRows]
  | .record _ _ fs => by simp [Expr.substRows, Expr.oneShot, fieldsOneShot_substRows fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by
    simp [Expr.substRows, Expr.oneShot, exprsOneShot_substRows es]
  | .field e _ | .raise e | .perform _ e | .try e | .form _ e | .loop e | .return e => by
    simp [Expr.substRows, Expr.oneShot, Expr.oneShot_substRows e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b
  | .tryCatch a _ _ b _ | .while a b => by
    simp [Expr.substRows, Expr.oneShot, Expr.oneShot_substRows a, Expr.oneShot_substRows b]
  | .held _ hs b => by
    simp [Expr.substRows, Expr.oneShot, exprsOneShot_substRows hs, Expr.oneShot_substRows b]
  | .call f args _ => by simp [Expr.substRows, Expr.oneShot, Expr.oneShot_substRows f, argsOneShot_substRows args]
  | .assign ⟨_, p⟩ v => by
    simp [Expr.substRows, Expr.oneShot, pathOneShot_substRows p, Expr.oneShot_substRows v]
  | .if c _ a b => by
    simp [Expr.substRows, Expr.oneShot, Expr.oneShot_substRows c, Expr.oneShot_substRows a, Expr.oneShot_substRows b]
  | .match e _ arms => by
    simp [Expr.substRows, Expr.oneShot, Expr.oneShot_substRows e, armsOneShot_substRows arms]

theorem exprsOneShot_substRows : ∀ es : List Expr, exprsOneShot (substExprRows s es) = exprsOneShot es
  | [] => rfl
  | e :: es => by simp [substExprRows, exprsOneShot, Expr.oneShot_substRows e, exprsOneShot_substRows es]

theorem fieldsOneShot_substRows :
    ∀ fs : List (Name × Expr), fieldsOneShot (substFieldRows s fs) = fieldsOneShot fs
  | [] => rfl
  | (_, e) :: fs => by simp [substFieldRows, fieldsOneShot, Expr.oneShot_substRows e, fieldsOneShot_substRows fs]

theorem argsOneShot_substRows : ∀ args : List Arg, argsOneShot (substArgRows s args) = argsOneShot args
  | [] => rfl
  | .value e :: args => by simp [substArgRows, argsOneShot, Expr.oneShot_substRows e, argsOneShot_substRows args]
  | .inout ⟨_, p⟩ :: args => by
    simp [substArgRows, argsOneShot, pathOneShot_substRows p, argsOneShot_substRows args]

theorem pathOneShot_substRows : ∀ p : List Projection, pathOneShot (substPathRows s p) = pathOneShot p
  | [] => rfl
  | .field _ :: p => by simpa [substPathRows, pathOneShot] using pathOneShot_substRows p
  | .index i :: p => by simp [substPathRows, pathOneShot, Expr.oneShot_substRows i, pathOneShot_substRows p]

theorem armsOneShot_substRows : ∀ arms : List Arm, armsOneShot (substArmRows s arms) = armsOneShot arms
  | [] => rfl
  | ⟨_, _, b⟩ :: arms => by simp [substArmRows, armsOneShot, Expr.oneShot_substRows b, armsOneShot_substRows arms]

end

end

end Stilt
