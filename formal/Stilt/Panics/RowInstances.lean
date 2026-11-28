import Stilt.Panics.RowShapes

/-!
# Instantiating row variables keeps code panic-free

A call instantiates the row variables of the body it runs, as it does its type
parameters (`Stilt.Panics.Instances`): the instantiated body writes what the
body writes and is panic-free exactly when the body is.
-/

namespace Stilt

section

variable (s : RowSubst) {lim : Limited}

theorem Expr.nonnegIn_substRows : ∀ (G : List Known) (e : Expr), (e.substRows s).nonnegIn G = e.nonnegIn G
  | _, .op o [] => by cases o <;> rfl
  | _, .op o [a] => by cases o <;> rfl
  | G, .op o [a, b] => by
    cases o
    case arith o k =>
      simp [Expr.substRows, substExprRows, Expr.nonnegIn, Expr.nonnegIn_substRows G a,
        Expr.writes_substRows s a, Expr.nonnegIn_substRows (withoutNames G a.writes) b]
    all_goals rfl
  | _, .op o (_ :: _ :: _ :: _) => by cases o <;> rfl
  | _, .assign ⟨_, _⟩ _ => rfl
  | _, .var _ | _, .move _ | _, .int _ | _, .bool _ | _, .unit | _, .break | _, .continue
  | _, .fnRef .. | _, .method .. | _, .record .. | _, .variant .. | _, .list .. | _, .field ..
  | _, .index .. | _, .closure .. | _, .call .. | _, .letIn .. | _, .varIn .. | _, .seq ..
  | _, .if .. | _, .match .. | _, .for .. | _, .raise .. | _, .try .. | _, .form .. | _, .tryCatch ..
  | _, .while .. | _, .loop .. | _, .return .. | _, .perform .. | _, .withH .. | _, .view ..
  | _, .held .. => rfl

theorem Expr.bindFacts_substRows (G : List Known) (x : Name) (e : Expr) :
    (e.substRows s).bindFacts G x = e.bindFacts G x := by
  unfold Expr.bindFacts
  rw [Expr.nonnegIn_substRows]
  cases e
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

theorem literalOperand_substRows : ∀ es : List Expr, literalOperand (substExprRows s es) = literalOperand es
  | [] => rfl
  | [_] => by simp [substExprRows, literalOperand]
  | [_, b] => by
    cases b
    case assign t _ =>
      obtain ⟨_, _⟩ := t
      simp [substExprRows, Expr.substRows, literalOperand]
    all_goals simp [substExprRows, Expr.substRows, literalOperand]
  | _ :: _ :: _ :: _ => by simp [substExprRows, literalOperand]

theorem guardedStore_substRows (G : List Known) (x : Name) (p : List Projection) (v : Expr) :
    guardedStore G ⟨x, substPathRows s p⟩ (v.substRows s) = guardedStore G ⟨x, p⟩ v := by
  unfold guardedStore
  rcases p with _ | ⟨q, _ | ⟨_, _⟩⟩
  · rfl
  · cases q with
    | field f => rfl
    | index i => simp [substPathRows, Expr.offset?_substRows, Expr.resizes_substRows s]
  · rename_i r rs
    cases q <;> cases r <;> rfl

theorem guardedIndex_substRows (G : List Known) (e i : Expr) :
    guardedIndex G (e.substRows s) (i.substRows s) = guardedIndex G e i := by
  simp [guardedIndex, Expr.readVar?_substRows, Expr.offset?_substRows]

theorem guardedKey_substRows (G : List Known) :
    ∀ es : List Expr, guardedKey G (substExprRows s es) = guardedKey G es
  | [] => rfl
  | [_] => by simp [substExprRows, guardedKey]
  | [a, k] => by
    rw [substExprRows, substExprRows, substExprRows]
    simp [guardedKey, Expr.readVar?_substRows, Expr.keyTerm?_substRows]
  | _ :: _ :: _ :: _ => by simp [substExprRows, guardedKey]

theorem guardedDivisor_substRows (G : List Known) :
    ∀ es : List Expr, guardedDivisor G (substExprRows s es) = guardedDivisor G es
  | [] => rfl
  | [_] => by simp [substExprRows, guardedDivisor]
  | [a, b] => by rw [substExprRows, substExprRows, substExprRows]; simp [guardedDivisor, Expr.readVar?_substRows, Expr.writes_substRows s a]
  | _ :: _ :: _ :: _ => by simp [substExprRows, guardedDivisor]

mutual

theorem Expr.panicFree_substRows : ∀ (G : List Known) (e : Expr), (e.substRows s).panicFreeIn lim G = e.panicFreeIn lim G
  | _, .var _ | _, .move _ | _, .int _ | _, .bool _ | _, .unit | _, .break | _, .continue
  | _, .fnRef .. | _, .method .. => rfl
  | G, .held ns hs b => by
    simp [Expr.substRows, Expr.panicFreeIn, exprsPanicFree_substRows G hs, exprsWrites_substRows s hs,
      Function.comp_def,
      Expr.panicFree_substRows (withoutNames (withoutNames G (exprsWrites hs)) (ns.map fun x => x.fst)) b]
  | G, .index e i => by
    simp [Expr.substRows, Expr.panicFreeIn, guardedIndex_substRows s G e i, Expr.isVar_substRows,
      Expr.panicFree_substRows G e, Expr.writes_substRows s e, Expr.panicFree_substRows (withoutNames G e.writes) i]
  | G, .record _ _ fs => by simp [Expr.substRows, Expr.panicFreeIn, fieldsPanicFree_substRows G fs]
  | G, .variant _ _ _ es | G, .list _ es => by
    simp [Expr.substRows, Expr.panicFreeIn, exprsPanicFree_substRows G es]
  | G, .view es => by
    simp [Expr.substRows, Expr.panicFreeIn, exprsPanicFree_substRows G es, length_substExprRows]
  | G, .op _ es => by
    simp [Expr.substRows, Expr.panicFreeIn, Op.panicFreeOn, exprsPanicFree_substRows G es,
      literalDivisor, literalOperand_substRows s es, Op.overflowFreeOn, guardedDivisor_substRows s G es,
      guardedKey_substRows s G es]
  | _, .closure _ _ _ e => by simp [Expr.substRows, Expr.panicFreeIn, Expr.panicFree_substRows [] e]
  | G, .field e _ | G, .raise e | G, .try e | G, .form _ e | G, .return e => by
    simp [Expr.substRows, Expr.panicFreeIn, Expr.panicFree_substRows G e]
  | _, .loop e => by simp [Expr.substRows, Expr.panicFreeIn, Expr.panicFree_substRows [] e]
  | G, .perform _ e => by simp [Expr.substRows, Expr.panicFreeIn, Expr.panicFree_substRows G e]
  | G, .withH _ _ h b => by
    simp [Expr.substRows, Expr.panicFreeIn, Expr.panicFree_substRows G h, Expr.writes_substRows s h,
      Expr.panicFree_substRows (withoutNames G h.writes) b]
  | G, .seq a b => by
    simp [Expr.substRows, Expr.panicFreeIn, Expr.panicFree_substRows G a, Expr.writes_substRows s a,
      Expr.resizes_substRows s a, Expr.after_substRows s a,
      Expr.panicFree_substRows (withoutWrites G a.writes a.resizes ++ a.after) b]
  | G, .letIn x _ a b | G, .varIn x _ a b => by
    simp [Expr.substRows, Expr.panicFreeIn, Expr.panicFree_substRows G a, Expr.writes_substRows s a,
      Expr.bindFacts_substRows s G x a,
      Expr.panicFree_substRows (withoutNames (withoutNames G a.writes) [x] ++ a.bindFacts G x) b]
  | G, .for x _ a b => by
    simp [Expr.substRows, Expr.panicFreeIn, Expr.panicFree_substRows G a, Expr.writes_substRows s a,
      Expr.writes_substRows s b, Expr.rangeFacts_substRows s G x b a,
      Expr.panicFree_substRows (withoutNames (withoutNames (withoutNames G a.writes) b.writes) [x] ++
        a.rangeFacts G x b) b]
  | G, .tryCatch a _ x b _ => by
    simp [Expr.substRows, Expr.panicFreeIn, Expr.panicFree_substRows G a, Expr.writes_substRows s a,
      Expr.panicFree_substRows (withoutNames (withoutNames G a.writes) [x]) b]
  | _, .while c b => by
    simp [Expr.substRows, Expr.panicFreeIn, Expr.panicFree_substRows [] c, Expr.facts_substRows s c,
      Expr.panicFree_substRows c.facts b]
  | G, .call f args _ => by
    simp [Expr.substRows, Expr.panicFreeIn, Expr.panicFree_substRows G f, Expr.writes_substRows s f,
      argsPanicFree_substRows (withoutNames G f.writes) args]
  | G, .assign ⟨x, p⟩ v => by
    simp [Expr.substRows, Expr.panicFreeIn, indexFree_substPathRows s x p, guardedStore_substRows s G x p v, byVar_substPathRows,
      Expr.panicFree_substRows G v,
      pathPanicFree_substRows G p, pathWrites_substRows s p,
      Expr.panicFree_substRows (withoutNames G (pathWrites p)) v]
  | G, .if c _ a b => by
    simp [Expr.substRows, Expr.panicFreeIn, Expr.panicFree_substRows G c, Expr.writes_substRows s c, Expr.facts_substRows s c,
      Expr.negFacts_substRows s c, Expr.panicFree_substRows (withoutNames G c.writes ++ c.facts) a,
      Expr.panicFree_substRows (withoutNames G c.writes ++ c.negFacts) b]
  | G, .match e _ arms => by
    simp [Expr.substRows, Expr.panicFreeIn, Expr.panicFree_substRows G e, Expr.writes_substRows s e,
      armsPanicFree_substRows (withoutNames G e.writes) arms]

theorem exprsPanicFree_substRows : ∀ (G : List Known) (es : List Expr),
    exprsPanicFree lim G (substExprRows s es) = exprsPanicFree lim G es
  | _, [] => rfl
  | G, e :: es => by
    simp [substExprRows, exprsPanicFree, Expr.panicFree_substRows G e, Expr.writes_substRows s e,
      exprsPanicFree_substRows (withoutNames G e.writes) es]

theorem fieldsPanicFree_substRows : ∀ (G : List Known) (fs : List (Name × Expr)),
    fieldsPanicFree lim G (substFieldRows s fs) = fieldsPanicFree lim G fs
  | _, [] => rfl
  | G, (_, e) :: fs => by
    simp [substFieldRows, fieldsPanicFree, Expr.panicFree_substRows G e, Expr.writes_substRows s e,
      fieldsPanicFree_substRows (withoutNames G e.writes) fs]

theorem argsPanicFree_substRows : ∀ (G : List Known) (args : List Arg),
    argsPanicFree lim G (substArgRows s args) = argsPanicFree lim G args
  | _, [] => rfl
  | G, .value e :: args => by
    simp [substArgRows, argsPanicFree, Expr.panicFree_substRows G e, Expr.writes_substRows s e,
      argsPanicFree_substRows (withoutNames G e.writes) args]
  | G, .inout ⟨x, p⟩ :: args => by
    simp [substArgRows, argsPanicFree, indexFree_substPathRows s x p, argsPanicFree_substRows G args]

theorem pathPanicFree_substRows : ∀ (G : List Known) (p : List Projection),
    pathPanicFree lim G (substPathRows s p) = pathPanicFree lim G p
  | _, [] => rfl
  | G, .field _ :: p => by simp [substPathRows, pathPanicFree, pathPanicFree_substRows G p]
  | G, .index i :: p => by
    simp [substPathRows, pathPanicFree, Expr.panicFree_substRows G i, Expr.writes_substRows s i,
      pathPanicFree_substRows (withoutNames G i.writes) p]

theorem armsPanicFree_substRows : ∀ (G : List Known) (arms : List Arm),
    armsPanicFree lim G (substArmRows s arms) = armsPanicFree lim G arms
  | _, [] => rfl
  | G, ⟨_, bs, g, b⟩ :: arms => by
    simp [substArmRows, armsPanicFree, guardWrites_substRows, guardPanicFree_substRows _ g,
      Expr.panicFree_substRows _ b, armsPanicFree_substRows _ arms]

theorem guardPanicFree_substRows : ∀ (G : List Known) (g : Option Expr),
    guardPanicFree lim G (substGuardRows s g) = guardPanicFree lim G g
  | _, none => rfl
  | G, some g => by simp [substGuardRows, guardPanicFree, Expr.panicFree_substRows G g]

end

end

end Stilt
