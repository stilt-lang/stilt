import Stilt.Panics.Shapes

/-!
# Instantiation keeps code panic-free

A call instantiates the type parameters of the body it runs, and its row
variables (`Stilt.Panics.RowInstances`). Instantiation rewrites types alone, and keeps every operation, every
literal, every place and every test, so an instantiated body writes what the
body writes and is panic-free exactly when the body is.
-/

namespace Stilt

section

variable (s : TySubst) {lim : Limited}

theorem Expr.nonnegIn_substTys : ∀ (G : List Known) (e : Expr), (e.substTys s).nonnegIn G = e.nonnegIn G
  | _, .op o [] => by cases o <;> rfl
  | _, .op o [a] => by cases o <;> rfl
  | G, .op o [a, b] => by
    cases o
    case arith o k =>
      simp [Expr.substTys, substExprTys, Op.substTys, Expr.nonnegIn, Expr.nonnegIn_substTys G a,
        Expr.writes_substTys s a, Expr.nonnegIn_substTys (withoutNames G a.writes) b]
    all_goals rfl
  | _, .op o (_ :: _ :: _ :: _) => by cases o <;> rfl
  | _, .assign ⟨_, _⟩ _ => rfl
  | _, .var _ | _, .move _ | _, .int _ | _, .bool _ | _, .unit | _, .break | _, .continue
  | _, .fnRef .. | _, .method .. | _, .record .. | _, .variant .. | _, .list .. | _, .field ..
  | _, .index .. | _, .closure .. | _, .call .. | _, .letIn .. | _, .varIn .. | _, .seq ..
  | _, .if .. | _, .match .. | _, .for .. | _, .raise .. | _, .try .. | _, .form .. | _, .tryCatch ..
  | _, .while .. | _, .loop .. | _, .return .. | _, .perform .. | _, .withH .. | _, .view ..
  | _, .held .. => rfl

theorem Expr.bindFacts_substTys (G : List Known) (x : Name) (e : Expr) :
    (e.substTys s).bindFacts G x = e.bindFacts G x := by
  unfold Expr.bindFacts
  rw [Expr.nonnegIn_substTys]
  cases e
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

theorem literalOperand_substTys : ∀ es : List Expr, literalOperand (substExprTys s es) = literalOperand es
  | [] => rfl
  | [_] => by simp [substExprTys, literalOperand]
  | [_, b] => by
    cases b
    case assign t _ =>
      obtain ⟨_, _⟩ := t
      simp [substExprTys, Expr.substTys, literalOperand]
    all_goals simp [substExprTys, Expr.substTys, literalOperand]
  | _ :: _ :: _ :: _ => by simp [substExprTys, literalOperand]

theorem guardedStore_substTys (G : List Known) (x : Name) (p : List Projection) (v : Expr) :
    guardedStore G ⟨x, substPathTys s p⟩ (v.substTys s) = guardedStore G ⟨x, p⟩ v := by
  unfold guardedStore
  rcases p with _ | ⟨q, _ | ⟨_, _⟩⟩
  · rfl
  · cases q with
    | field f => rfl
    | index i => simp [substPathTys, Expr.offset?_substTys, Expr.resizes_substTys s]
  · rename_i r rs
    cases q <;> cases r <;> rfl

theorem guardedIndex_substTys (G : List Known) (e i : Expr) :
    guardedIndex G (e.substTys s) (i.substTys s) = guardedIndex G e i := by
  simp [guardedIndex, Expr.readVar?_substTys, Expr.offset?_substTys]

theorem guardedKey_substTys (G : List Known) :
    ∀ es : List Expr, guardedKey G (substExprTys s es) = guardedKey G es
  | [] => rfl
  | [_] => by simp [substExprTys, guardedKey]
  | [a, k] => by
    rw [substExprTys, substExprTys, substExprTys]
    simp [guardedKey, Expr.readVar?_substTys, Expr.keyTerm?_substTys]
  | _ :: _ :: _ :: _ => by simp [substExprTys, guardedKey]

theorem guardedDivisor_substTys (G : List Known) :
    ∀ es : List Expr, guardedDivisor G (substExprTys s es) = guardedDivisor G es
  | [] => rfl
  | [_] => by simp [substExprTys, guardedDivisor]
  | [a, b] => by rw [substExprTys, substExprTys, substExprTys]; simp [guardedDivisor, Expr.readVar?_substTys, Expr.writes_substTys s a]
  | _ :: _ :: _ :: _ => by simp [substExprTys, guardedDivisor]

mutual

theorem Expr.panicFree_substTys : ∀ (G : List Known) (e : Expr), (e.substTys s).panicFreeIn lim G = e.panicFreeIn lim G
  | _, .var _ | _, .move _ | _, .int _ | _, .bool _ | _, .unit | _, .break | _, .continue
  | _, .fnRef .. | _, .method .. => rfl
  | G, .held ns hs b => by
    simp [Expr.substTys, Expr.panicFreeIn, exprsPanicFree_substTys G hs, exprsWrites_substTys s hs,
      Function.comp_def,
      Expr.panicFree_substTys (withoutNames (withoutNames G (exprsWrites hs)) (ns.map fun x => x.fst)) b]
  | G, .index e i => by
    simp [Expr.substTys, Expr.panicFreeIn, guardedIndex_substTys s G e i, Expr.isVar_substTys,
      Expr.panicFree_substTys G e, Expr.writes_substTys s e, Expr.panicFree_substTys (withoutNames G e.writes) i]
  | G, .record _ _ fs => by simp [Expr.substTys, Expr.panicFreeIn, fieldsPanicFree_substTys G fs]
  | G, .variant _ _ _ es | G, .list _ es => by
    simp [Expr.substTys, Expr.panicFreeIn, exprsPanicFree_substTys G es]
  | G, .view es => by
    simp [Expr.substTys, Expr.panicFreeIn, exprsPanicFree_substTys G es, length_substExprTys]
  | G, .op o es => by
    cases o <;> simp [Expr.substTys, Expr.panicFreeIn, Op.panicFreeOn, exprsPanicFree_substTys G es,
      literalDivisor, literalOperand_substTys s es, Op.overflowFreeOn, guardedDivisor_substTys s G es,
      guardedKey_substTys s G es, Op.panicFree, Op.byDivisor, Op.overflowFreeBy, Op.overflowFree]
  | _, .closure _ _ _ e => by simp [Expr.substTys, Expr.panicFreeIn, Expr.panicFree_substTys [] e]
  | G, .field e _ | G, .raise e | G, .try e | G, .form _ e | G, .return e => by
    simp [Expr.substTys, Expr.panicFreeIn, Expr.panicFree_substTys G e]
  | _, .loop e => by simp [Expr.substTys, Expr.panicFreeIn, Expr.panicFree_substTys [] e]
  | G, .perform _ e => by simp [Expr.substTys, Expr.panicFreeIn, Expr.panicFree_substTys G e]
  | G, .withH _ _ h b => by
    simp [Expr.substTys, Expr.panicFreeIn, Expr.panicFree_substTys G h, Expr.writes_substTys s h,
      Expr.panicFree_substTys (withoutNames G h.writes) b]
  | G, .seq a b => by
    simp [Expr.substTys, Expr.panicFreeIn, Expr.panicFree_substTys G a, Expr.writes_substTys s a,
      Expr.resizes_substTys s a, Expr.after_substTys s a,
      Expr.panicFree_substTys (withoutWrites G a.writes a.resizes ++ a.after) b]
  | G, .letIn x _ a b | G, .varIn x _ a b => by
    simp [Expr.substTys, Expr.panicFreeIn, Expr.panicFree_substTys G a, Expr.writes_substTys s a,
      Expr.bindFacts_substTys s G x a,
      Expr.panicFree_substTys (withoutNames (withoutNames G a.writes) [x] ++ a.bindFacts G x) b]
  | G, .for x _ a b => by
    simp [Expr.substTys, Expr.panicFreeIn, Expr.panicFree_substTys G a, Expr.writes_substTys s a,
      Expr.writes_substTys s b, Expr.rangeFacts_substTys s G x b a,
      Expr.panicFree_substTys (withoutNames (withoutNames (withoutNames G a.writes) b.writes) [x] ++
        a.rangeFacts G x b) b]
  | G, .tryCatch a _ x b _ => by
    simp [Expr.substTys, Expr.panicFreeIn, Expr.panicFree_substTys G a, Expr.writes_substTys s a,
      Expr.panicFree_substTys (withoutNames (withoutNames G a.writes) [x]) b]
  | _, .while c b => by
    simp [Expr.substTys, Expr.panicFreeIn, Expr.panicFree_substTys [] c, Expr.facts_substTys s c,
      Expr.panicFree_substTys c.facts b]
  | G, .call f args _ => by
    simp [Expr.substTys, Expr.panicFreeIn, Expr.panicFree_substTys G f, Expr.writes_substTys s f,
      argsPanicFree_substTys (withoutNames G f.writes) args]
  | G, .assign ⟨x, p⟩ v => by
    simp [Expr.substTys, Expr.panicFreeIn, indexFree_substPathTys s x p, guardedStore_substTys s G x p v, byVar_substPathTys,
      Expr.panicFree_substTys G v,
      pathPanicFree_substTys G p, pathWrites_substTys s p,
      Expr.panicFree_substTys (withoutNames G (pathWrites p)) v]
  | G, .if c _ a b => by
    simp [Expr.substTys, Expr.panicFreeIn, Expr.panicFree_substTys G c, Expr.writes_substTys s c, Expr.facts_substTys s c,
      Expr.negFacts_substTys s c, Expr.panicFree_substTys (withoutNames G c.writes ++ c.facts) a,
      Expr.panicFree_substTys (withoutNames G c.writes ++ c.negFacts) b]
  | G, .match e _ arms => by
    simp [Expr.substTys, Expr.panicFreeIn, Expr.panicFree_substTys G e, Expr.writes_substTys s e,
      armsPanicFree_substTys (withoutNames G e.writes) arms]

theorem exprsPanicFree_substTys : ∀ (G : List Known) (es : List Expr),
    exprsPanicFree lim G (substExprTys s es) = exprsPanicFree lim G es
  | _, [] => rfl
  | G, e :: es => by
    simp [substExprTys, exprsPanicFree, Expr.panicFree_substTys G e, Expr.writes_substTys s e,
      exprsPanicFree_substTys (withoutNames G e.writes) es]

theorem fieldsPanicFree_substTys : ∀ (G : List Known) (fs : List (Name × Expr)),
    fieldsPanicFree lim G (substFieldTys s fs) = fieldsPanicFree lim G fs
  | _, [] => rfl
  | G, (_, e) :: fs => by
    simp [substFieldTys, fieldsPanicFree, Expr.panicFree_substTys G e, Expr.writes_substTys s e,
      fieldsPanicFree_substTys (withoutNames G e.writes) fs]

theorem argsPanicFree_substTys : ∀ (G : List Known) (args : List Arg),
    argsPanicFree lim G (substArgTys s args) = argsPanicFree lim G args
  | _, [] => rfl
  | G, .value e :: args => by
    simp [substArgTys, argsPanicFree, Expr.panicFree_substTys G e, Expr.writes_substTys s e,
      argsPanicFree_substTys (withoutNames G e.writes) args]
  | G, .inout ⟨x, p⟩ :: args => by
    simp [substArgTys, argsPanicFree, indexFree_substPathTys s x p, argsPanicFree_substTys G args]

theorem pathPanicFree_substTys : ∀ (G : List Known) (p : List Projection),
    pathPanicFree lim G (substPathTys s p) = pathPanicFree lim G p
  | _, [] => rfl
  | G, .field _ :: p => by simp [substPathTys, pathPanicFree, pathPanicFree_substTys G p]
  | G, .index i :: p => by
    simp [substPathTys, pathPanicFree, Expr.panicFree_substTys G i, Expr.writes_substTys s i,
      pathPanicFree_substTys (withoutNames G i.writes) p]

theorem armsPanicFree_substTys : ∀ (G : List Known) (arms : List Arm),
    armsPanicFree lim G (substArmTys s arms) = armsPanicFree lim G arms
  | _, [] => rfl
  | G, ⟨_, bs, g, b⟩ :: arms => by
    simp [substArmTys, armsPanicFree, guardWrites_substTys, guardPanicFree_substTys _ g,
      Expr.panicFree_substTys _ b, armsPanicFree_substTys _ arms]

theorem guardPanicFree_substTys : ∀ (G : List Known) (g : Option Expr),
    guardPanicFree lim G (substGuardTys s g) = guardPanicFree lim G g
  | _, none => rfl
  | G, some g => by simp [substGuardTys, guardPanicFree, Expr.panicFree_substTys G g]

end

end

end Stilt
