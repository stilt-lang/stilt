import Stilt.Moves.Analysis
import Stilt.Generics.Commute

/-!
# Instantiation keeps the marks

A call instantiates the type parameters and the row variables of the body it
runs (types.no-type-arguments and effects.inference). The analysis looks at variables, never at
the types that instantiation rewrites, so an instantiated body mentions the
same variables and its marks are last uses exactly when the body's are.
-/

namespace Stilt

section

variable (s : RowSubst)

theorem inoutLive_substRows (ps : List Param) : inoutLive (ps.map (Param.substRows s)) = inoutLive ps := by
  simp [inoutLive, Param.substRows, List.filter_map, Function.comp_def, List.map_map]

theorem inoutRoots_substArgRows : ∀ args : List Arg, inoutRoots (substArgRows s args) = inoutRoots args
  | [] => rfl
  | .value _ :: args => by simp [substArgRows, inoutRoots, inoutRoots_substArgRows args]
  | .inout ⟨_, _⟩ :: args => by simp [substArgRows, inoutRoots, inoutRoots_substArgRows args]

mutual

theorem Expr.mentions_substRows : ∀ e : Expr, (e.substRows s).mentions = e.mentions
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method .. => rfl
  | .closure _ _ _ body => by
    simp only [Expr.substRows, Expr.mentions, Expr.mentions_substRows body, List.map_map]
    rfl
  | .record _ _ fs => by simp [Expr.substRows, Expr.mentions, fieldsMentions_substRows fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by
    simp [Expr.substRows, Expr.mentions, exprsMentions_substRows es]
  | .field e _ | .raise e | .perform _ e | .try e | .form _ e | .loop e | .return e => by
    simp [Expr.substRows, Expr.mentions, Expr.mentions_substRows e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b | .while a b
  | .tryCatch a _ _ b _ => by
    simp [Expr.substRows, Expr.mentions, Expr.mentions_substRows a, Expr.mentions_substRows b]
  | .held _ hs b => by
    simp [Expr.substRows, Expr.mentions, exprsMentions_substRows hs, Expr.mentions_substRows b,
      Function.comp_def]
  | .call f args _ => by
    simp [Expr.substRows, Expr.mentions, Expr.mentions_substRows f, argsMentions_substRows args]
  | .assign ⟨_, p⟩ v => by
    simp [Expr.substRows, Expr.mentions, pathMentions_substRows p, Expr.mentions_substRows v]
  | .if c _ a b => by
    simp [Expr.substRows, Expr.mentions, Expr.mentions_substRows c, Expr.mentions_substRows a,
      Expr.mentions_substRows b]
  | .match e _ arms => by
    simp [Expr.substRows, Expr.mentions, Expr.mentions_substRows e, armsMentions_substRows arms]

theorem exprsMentions_substRows :
    ∀ es : List Expr, exprsMentions (substExprRows s es) = exprsMentions es
  | [] => rfl
  | e :: es => by
    simp [substExprRows, exprsMentions, Expr.mentions_substRows e, exprsMentions_substRows es]

theorem fieldsMentions_substRows :
    ∀ fs : List (Name × Expr), fieldsMentions (substFieldRows s fs) = fieldsMentions fs
  | [] => rfl
  | (_, e) :: fs => by
    simp [substFieldRows, fieldsMentions, Expr.mentions_substRows e, fieldsMentions_substRows fs]

theorem argsMentions_substRows :
    ∀ args : List Arg, argsMentions (substArgRows s args) = argsMentions args
  | [] => rfl
  | .value e :: args => by
    simp [substArgRows, argsMentions, Expr.mentions_substRows e, argsMentions_substRows args]
  | .inout ⟨_, p⟩ :: args => by
    simp [substArgRows, argsMentions, pathMentions_substRows p, argsMentions_substRows args]

theorem pathMentions_substRows :
    ∀ p : List Projection, pathMentions (substPathRows s p) = pathMentions p
  | [] => rfl
  | .field _ :: p => by simpa [substPathRows, pathMentions] using pathMentions_substRows p
  | .index i :: p => by
    simp [substPathRows, pathMentions, Expr.mentions_substRows i, pathMentions_substRows p]

theorem armsMentions_substRows :
    ∀ arms : List Arm, armsMentions (substArmRows s arms) = armsMentions arms
  | [] => rfl
  | ⟨_, _, g, b⟩ :: arms => by
    simp [substArmRows, armsMentions, guardMentions_substRows g, Expr.mentions_substRows b,
      armsMentions_substRows arms]

theorem guardMentions_substRows :
    ∀ g : Option Expr, guardMentions (substGuardRows s g) = guardMentions g
  | none => rfl
  | some g => by simp [substGuardRows, guardMentions, Expr.mentions_substRows g]

end

mutual

theorem Expr.movesOk_substRows : ∀ (e : Expr) (L : Live), (e.substRows s).movesOk L = e.movesOk L
  | .var _, _ | .move _, _ | .int _, _ | .bool _, _ | .unit, _ | .break, _ | .continue, _ | .fnRef .., _ | .method .., _ => rfl
  | .record _ _ fs, L => fieldsMovesOk_substRows fs L
  | .variant _ _ _ es, L | .list _ es, L | .op _ es, L | .view es, L => exprsMovesOk_substRows es L
  | .field e _, L | .raise e, L | .perform _ e, L | .try e, L | .form _ e, L | .return e, L => Expr.movesOk_substRows e L
  | .closure ps _ _ b, _ => by
    simp [Expr.substRows, Expr.movesOk, inoutLive_substRows, Expr.movesOk_substRows b]
  | .index a b, L => by
    simp [Expr.substRows, Expr.movesOk, Expr.mentions_substRows, Expr.movesOk_substRows a,
      Expr.movesOk_substRows b]
  | .held _ hs b, L => by
    simp [Expr.substRows, Expr.movesOk, Expr.mentions_substRows, exprsMovesOk_substRows hs,
      Expr.movesOk_substRows b, Function.comp_def]
  | .seq a b, L | .withH _ _ a b, L | .letIn _ _ a b, L | .varIn _ _ a b, L | .tryCatch a _ _ b _, L => by
    simp [Expr.substRows, Expr.movesOk, Expr.mentions_substRows, Expr.movesOk_substRows a,
      Expr.movesOk_substRows b]
  | .for _ _ a b, L | .while a b, L => by
    simp [Expr.substRows, Expr.movesOk, Expr.mentions_substRows, Expr.movesOk_substRows a,
      Expr.movesOk_substRows b]
  | .loop b, L => by
    simp [Expr.substRows, Expr.movesOk, Expr.mentions_substRows, Expr.movesOk_substRows b]
  | .call f args _, L => by
    simp [Expr.substRows, Expr.movesOk, argsMentions_substRows, inoutRoots_substArgRows,
      Expr.movesOk_substRows f, argsMovesOk_substRows args]
  | .assign ⟨_, p⟩ v, L => by
    simp [Expr.substRows, Expr.movesOk, Expr.mentions_substRows, pathMovesOk_substRows p,
      Expr.movesOk_substRows v]
  | .if c _ a b, L => by
    simp [Expr.substRows, Expr.movesOk, Expr.mentions_substRows, Expr.movesOk_substRows c,
      Expr.movesOk_substRows a, Expr.movesOk_substRows b]
  | .match e _ arms, L => by
    simp [Expr.substRows, Expr.movesOk, armsMentions_substRows, Expr.movesOk_substRows e,
      armsMovesOk_substRows arms]

theorem exprsMovesOk_substRows : ∀ (es : List Expr) (L : Live),
    exprsMovesOk L (substExprRows s es) = exprsMovesOk L es
  | [], _ => rfl
  | e :: es, L => by
    simp [substExprRows, exprsMovesOk, exprsMentions_substRows, Expr.movesOk_substRows e,
      exprsMovesOk_substRows es]

theorem fieldsMovesOk_substRows : ∀ (fs : List (Name × Expr)) (L : Live),
    fieldsMovesOk L (substFieldRows s fs) = fieldsMovesOk L fs
  | [], _ => rfl
  | (_, e) :: fs, L => by
    simp [substFieldRows, fieldsMovesOk, fieldsMentions_substRows, Expr.movesOk_substRows e,
      fieldsMovesOk_substRows fs]

theorem argsMovesOk_substRows : ∀ (args : List Arg) (L : Live),
    argsMovesOk L (substArgRows s args) = argsMovesOk L args
  | [], _ => rfl
  | .value e :: args, L => by
    simp [substArgRows, argsMovesOk, argsMentions_substRows, Expr.movesOk_substRows e,
      argsMovesOk_substRows args]
  | .inout ⟨_, p⟩ :: args, L => by
    simp [substArgRows, argsMovesOk, argsMentions_substRows, pathMovesOk_substRows p,
      argsMovesOk_substRows args]

theorem pathMovesOk_substRows : ∀ (p : List Projection) (L : Live),
    pathMovesOk L (substPathRows s p) = pathMovesOk L p
  | [], _ => rfl
  | .field _ :: p, L => pathMovesOk_substRows p L
  | .index i :: p, L => by
    simp [substPathRows, pathMovesOk, pathMentions_substRows, Expr.movesOk_substRows i,
      pathMovesOk_substRows p]

theorem armsMovesOk_substRows : ∀ (arms : List Arm) (L : Live),
    armsMovesOk L (substArmRows s arms) = armsMovesOk L arms
  | [], _ => rfl
  | ⟨_, _, g, b⟩ :: arms, L => by
    simp [substArmRows, armsMovesOk, armsMentions_substRows, Expr.mentions_substRows,
      guardMentions_substRows, guardMovesOk_substRows g, Expr.movesOk_substRows b, armsMovesOk_substRows arms]

theorem guardMovesOk_substRows : ∀ (g : Option Expr) (L : Live),
    guardMovesOk L (substGuardRows s g) = guardMovesOk L g
  | none, _ => rfl
  | some g, L => by simp [substGuardRows, guardMovesOk, Expr.movesOk_substRows g]

end

end

section

variable (s : TySubst)

theorem inoutLive_substTys (ps : List Param) : inoutLive (ps.map (Param.substTys s)) = inoutLive ps := by
  simp [inoutLive, Param.substTys, List.filter_map, Function.comp_def, List.map_map]

theorem inoutRoots_substArgTys : ∀ args : List Arg, inoutRoots (substArgTys s args) = inoutRoots args
  | [] => rfl
  | .value _ :: args => by simp [substArgTys, inoutRoots, inoutRoots_substArgTys args]
  | .inout ⟨_, _⟩ :: args => by simp [substArgTys, inoutRoots, inoutRoots_substArgTys args]

mutual

theorem Expr.mentions_substTys : ∀ e : Expr, (e.substTys s).mentions = e.mentions
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method .. => rfl
  | .closure _ _ _ body => by
    simp only [Expr.substTys, Expr.mentions, Expr.mentions_substTys body, List.map_map]
    rfl
  | .record _ _ fs => by simp [Expr.substTys, Expr.mentions, fieldsMentions_substTys fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by
    simp [Expr.substTys, Expr.mentions, exprsMentions_substTys es]
  | .field e _ | .raise e | .perform _ e | .try e | .form _ e | .loop e | .return e => by
    simp [Expr.substTys, Expr.mentions, Expr.mentions_substTys e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b | .while a b
  | .tryCatch a _ _ b _ => by
    simp [Expr.substTys, Expr.mentions, Expr.mentions_substTys a, Expr.mentions_substTys b]
  | .held _ hs b => by
    simp [Expr.substTys, Expr.mentions, exprsMentions_substTys hs, Expr.mentions_substTys b,
      Function.comp_def]
  | .call f args _ => by
    simp [Expr.substTys, Expr.mentions, Expr.mentions_substTys f, argsMentions_substTys args]
  | .assign ⟨_, p⟩ v => by
    simp [Expr.substTys, Expr.mentions, pathMentions_substTys p, Expr.mentions_substTys v]
  | .if c _ a b => by
    simp [Expr.substTys, Expr.mentions, Expr.mentions_substTys c, Expr.mentions_substTys a,
      Expr.mentions_substTys b]
  | .match e _ arms => by
    simp [Expr.substTys, Expr.mentions, Expr.mentions_substTys e, armsMentions_substTys arms]

theorem exprsMentions_substTys :
    ∀ es : List Expr, exprsMentions (substExprTys s es) = exprsMentions es
  | [] => rfl
  | e :: es => by
    simp [substExprTys, exprsMentions, Expr.mentions_substTys e, exprsMentions_substTys es]

theorem fieldsMentions_substTys :
    ∀ fs : List (Name × Expr), fieldsMentions (substFieldTys s fs) = fieldsMentions fs
  | [] => rfl
  | (_, e) :: fs => by
    simp [substFieldTys, fieldsMentions, Expr.mentions_substTys e, fieldsMentions_substTys fs]

theorem argsMentions_substTys :
    ∀ args : List Arg, argsMentions (substArgTys s args) = argsMentions args
  | [] => rfl
  | .value e :: args => by
    simp [substArgTys, argsMentions, Expr.mentions_substTys e, argsMentions_substTys args]
  | .inout ⟨_, p⟩ :: args => by
    simp [substArgTys, argsMentions, pathMentions_substTys p, argsMentions_substTys args]

theorem pathMentions_substTys :
    ∀ p : List Projection, pathMentions (substPathTys s p) = pathMentions p
  | [] => rfl
  | .field _ :: p => by simpa [substPathTys, pathMentions] using pathMentions_substTys p
  | .index i :: p => by
    simp [substPathTys, pathMentions, Expr.mentions_substTys i, pathMentions_substTys p]

theorem armsMentions_substTys :
    ∀ arms : List Arm, armsMentions (substArmTys s arms) = armsMentions arms
  | [] => rfl
  | ⟨_, _, g, b⟩ :: arms => by
    simp [substArmTys, armsMentions, guardMentions_substTys g, Expr.mentions_substTys b,
      armsMentions_substTys arms]

theorem guardMentions_substTys :
    ∀ g : Option Expr, guardMentions (substGuardTys s g) = guardMentions g
  | none => rfl
  | some g => by simp [substGuardTys, guardMentions, Expr.mentions_substTys g]

end

mutual

theorem Expr.movesOk_substTys : ∀ (e : Expr) (L : Live), (e.substTys s).movesOk L = e.movesOk L
  | .var _, _ | .move _, _ | .int _, _ | .bool _, _ | .unit, _ | .break, _ | .continue, _ | .fnRef .., _ | .method .., _ => rfl
  | .record _ _ fs, L => fieldsMovesOk_substTys fs L
  | .variant _ _ _ es, L | .list _ es, L | .op _ es, L | .view es, L => exprsMovesOk_substTys es L
  | .field e _, L | .raise e, L | .perform _ e, L | .try e, L | .form _ e, L | .return e, L => Expr.movesOk_substTys e L
  | .closure ps _ _ b, _ => by
    simp [Expr.substTys, Expr.movesOk, inoutLive_substTys, Expr.movesOk_substTys b]
  | .index a b, L => by
    simp [Expr.substTys, Expr.movesOk, Expr.mentions_substTys, Expr.movesOk_substTys a,
      Expr.movesOk_substTys b]
  | .held _ hs b, L => by
    simp [Expr.substTys, Expr.movesOk, Expr.mentions_substTys, exprsMovesOk_substTys hs,
      Expr.movesOk_substTys b, Function.comp_def]
  | .seq a b, L | .withH _ _ a b, L | .letIn _ _ a b, L | .varIn _ _ a b, L | .tryCatch a _ _ b _, L => by
    simp [Expr.substTys, Expr.movesOk, Expr.mentions_substTys, Expr.movesOk_substTys a,
      Expr.movesOk_substTys b]
  | .for _ _ a b, L | .while a b, L => by
    simp [Expr.substTys, Expr.movesOk, Expr.mentions_substTys, Expr.movesOk_substTys a,
      Expr.movesOk_substTys b]
  | .loop b, L => by
    simp [Expr.substTys, Expr.movesOk, Expr.mentions_substTys, Expr.movesOk_substTys b]
  | .call f args _, L => by
    simp [Expr.substTys, Expr.movesOk, argsMentions_substTys, inoutRoots_substArgTys,
      Expr.movesOk_substTys f, argsMovesOk_substTys args]
  | .assign ⟨_, p⟩ v, L => by
    simp [Expr.substTys, Expr.movesOk, Expr.mentions_substTys, pathMovesOk_substTys p,
      Expr.movesOk_substTys v]
  | .if c _ a b, L => by
    simp [Expr.substTys, Expr.movesOk, Expr.mentions_substTys, Expr.movesOk_substTys c,
      Expr.movesOk_substTys a, Expr.movesOk_substTys b]
  | .match e _ arms, L => by
    simp [Expr.substTys, Expr.movesOk, armsMentions_substTys, Expr.movesOk_substTys e,
      armsMovesOk_substTys arms]

theorem exprsMovesOk_substTys : ∀ (es : List Expr) (L : Live),
    exprsMovesOk L (substExprTys s es) = exprsMovesOk L es
  | [], _ => rfl
  | e :: es, L => by
    simp [substExprTys, exprsMovesOk, exprsMentions_substTys, Expr.movesOk_substTys e,
      exprsMovesOk_substTys es]

theorem fieldsMovesOk_substTys : ∀ (fs : List (Name × Expr)) (L : Live),
    fieldsMovesOk L (substFieldTys s fs) = fieldsMovesOk L fs
  | [], _ => rfl
  | (_, e) :: fs, L => by
    simp [substFieldTys, fieldsMovesOk, fieldsMentions_substTys, Expr.movesOk_substTys e,
      fieldsMovesOk_substTys fs]

theorem argsMovesOk_substTys : ∀ (args : List Arg) (L : Live),
    argsMovesOk L (substArgTys s args) = argsMovesOk L args
  | [], _ => rfl
  | .value e :: args, L => by
    simp [substArgTys, argsMovesOk, argsMentions_substTys, Expr.movesOk_substTys e,
      argsMovesOk_substTys args]
  | .inout ⟨_, p⟩ :: args, L => by
    simp [substArgTys, argsMovesOk, argsMentions_substTys, pathMovesOk_substTys p,
      argsMovesOk_substTys args]

theorem pathMovesOk_substTys : ∀ (p : List Projection) (L : Live),
    pathMovesOk L (substPathTys s p) = pathMovesOk L p
  | [], _ => rfl
  | .field _ :: p, L => pathMovesOk_substTys p L
  | .index i :: p, L => by
    simp [substPathTys, pathMovesOk, pathMentions_substTys, Expr.movesOk_substTys i,
      pathMovesOk_substTys p]

theorem armsMovesOk_substTys : ∀ (arms : List Arm) (L : Live),
    armsMovesOk L (substArmTys s arms) = armsMovesOk L arms
  | [], _ => rfl
  | ⟨_, _, g, b⟩ :: arms, L => by
    simp [substArmTys, armsMovesOk, armsMentions_substTys, Expr.mentions_substTys,
      guardMentions_substTys, guardMovesOk_substTys g, Expr.movesOk_substTys b, armsMovesOk_substTys arms]

theorem guardMovesOk_substTys : ∀ (g : Option Expr) (L : Live),
    guardMovesOk L (substGuardTys s g) = guardMovesOk L g
  | none, _ => rfl
  | some g, L => by simp [substGuardTys, guardMovesOk, Expr.movesOk_substTys g]

end

end

end Stilt
