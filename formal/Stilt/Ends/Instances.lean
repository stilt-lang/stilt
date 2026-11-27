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

variable (s : TySubst) {lim : Limited} {B : Name → Nat} {H : Name → List Nat}
  {me : Option (Name × Descent)}

theorem Expr.haltingIn_substTys (R : Roles) (e : Expr) : (e.substTys s).haltingIn R = e.haltingIn R := by
  cases e <;> first | rfl | (rename_i t _; cases t; rfl)

theorem haltingArg_substTys (R : Roles) (e : Expr) :
    haltingArg lim B H me R (e.substTys s) = haltingArg lim B H me R e := by
  cases e <;> first | rfl | (rename_i t _; cases t; rfl)

theorem Expr.callable_substTys (e : Expr) : (e.substTys s).callable = e.callable := by
  cases e <;> first | rfl | (rename_i t _; cases t; rfl)

theorem Expr.isSelf_substTys (e : Expr) : (e.substTys s).isSelf me = e.isSelf me := by
  cases e <;> first | rfl | (rename_i t _; cases t; rfl)

theorem Expr.roleIn_substTys (R : Roles) : ∀ e : Expr, (e.substTys s).roleIn R = e.roleIn R
  | .field e _ => by simp [Expr.substTys, Expr.roleIn, Expr.roleIn_substTys R e]
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .record .. | .variant .. | .list .. | .op .. | .view _ | .index .. | .call .. | .letIn ..
  | .varIn .. | .seq .. | .if .. | .match .. | .for .. | .raise .. | .perform _ .. | .withH ..
  | .held .. | .try .. | .form .. | .tryCatch .. | .closure .. | .assign ⟨_, _⟩ _ | .while .. | .loop _
  | .return _ => rfl

theorem argPart_substTys (R : Roles) : ∀ (k : Nat) (args : List Arg),
    argPart R k (substArgTys s args) = argPart R k args
  | 0, .value e :: _ => by simp [substArgTys, argPart, Expr.roleIn_substTys s R e]
  | 0, .inout ⟨_, _⟩ :: _ => rfl
  | k + 1, .value _ :: args | k + 1, .inout ⟨_, _⟩ :: args => by
    simp [substArgTys, argPart, argPart_substTys R k args]
  | 0, [] | _ + 1, [] => rfl

theorem argWith_substTys {ok : Expr → Bool} (hok : ∀ e, ok (e.substTys s) = ok e) :
    ∀ (k : Nat) (args : List Arg), argWith ok k (substArgTys s args) = argWith ok k args
  | 0, .value e :: _ => by simp [substArgTys, argWith, hok e]
  | 0, .inout ⟨_, _⟩ :: _ => rfl
  | k + 1, .value _ :: args | k + 1, .inout ⟨_, _⟩ :: args => by
    simp [substArgTys, argWith, argWith_substTys hok k args]
  | 0, [] | _ + 1, [] => rfl

theorem Expr.passesHalting_substTys (R : Roles) (e : Expr) (args : List Arg) :
    (e.substTys s).passesHalting lim B H me R (substArgTys s args) = e.passesHalting lim B H me R args := by
  cases e <;> try rfl
  case assign t _ => cases t; rfl
  simp [Expr.substTys, Expr.passesHalting, argWith_substTys s (haltingArg_substTys s R)]

theorem Expr.shrinksIn_substTys (R : Roles) (grow : Bool) (e : Expr) :
    (e.substTys s).shrinksIn R grow = e.shrinksIn R grow := by
  cases e
  case op o es =>
    rcases es with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> cases o <;> try rfl
    simp only [Expr.substTys, substExprTys, Op.substTys, Expr.shrinksIn, Expr.movesBy,
      Expr.readVar?_substTys, Expr.intLit?_substTys]
  all_goals first | rfl | (rename_i t _; cases t; rfl)

theorem descends_substTys (R : Roles) (args : List Arg) :
    descends me R (substArgTys s args) = descends me R args := by
  unfold descends
  congr 1
  funext ⟨_, d⟩
  cases d with
  | parts k => simp [Descent.calls, argPart_substTys]
  | shrinks k g b =>
    have h₁ := argWith_substTys s (ok := Expr.shrinksIn R g) (Expr.shrinksIn_substTys s R g) k args
    cases b with
    | lit c => simp [Descent.calls, ShrinkBound.passedIn, h₁]
    | param j =>
      have h₂ := argWith_substTys s (ok := fun e => e.roleIn R == .limit)
        (fun e => by simp [Expr.roleIn_substTys]) j args
      simp [Descent.calls, ShrinkBound.passedIn, h₁, h₂]

theorem Expr.negated_substTys : ∀ e : Expr, (e.substTys s).negated.countings = e.negated.countings
  | .op o es => by
    rcases es with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> cases o <;> try rfl
    simp only [Expr.substTys, substExprTys, Op.substTys, Expr.negated, Expr.countings,
      Expr.readVar?_substTys, Expr.bound?_substTys]
  | .assign ⟨_, _⟩ _ => rfl
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .record .. | .variant .. | .list .. | .field .. | .index .. | .closure .. | .call ..
  | .letIn .. | .varIn .. | .seq .. | .match .. | .for .. | .raise .. | .perform _ .. | .withH ..
  | .held .. | .try .. | .form .. | .tryCatch .. | .while .. | .loop .. | .return .. | .view .. | .if .. => rfl

theorem Roles.held_substTys (R : Roles) (c : Expr) : R.held me (c.substTys s) = R.held me c := by
  unfold Roles.held; rw [Expr.countings_substTys]

theorem Roles.held_negated_substTys (R : Roles) (c : Expr) :
    R.held me (c.substTys s).negated = R.held me c.negated := by
  unfold Roles.held; rw [Expr.negated_substTys]

mutual

theorem Expr.divFree_substTys : ∀ (R : Roles) (e : Expr),
    (e.substTys s).divFree lim B H me R = e.divFree lim B H me R
  | _, .var _ | _, .move _ | _, .int _ | _, .bool _ | _, .unit | _, .break | _, .continue
  | _, .fnRef .. | _, .method .. => rfl
  | R, .record _ _ fs => by simp [Expr.substTys, Expr.divFree, fieldsDivFree_substTys R fs]
  | R, .variant _ _ _ es | R, .list _ es | R, .op _ es | R, .view es => by
    simp [Expr.substTys, Expr.divFree, exprsDivFree_substTys R es]
  | _, .closure _ _ _ e => by simp [Expr.substTys, Expr.divFree, Expr.divFree_substTys [] e]
  | R, .field e _ | R, .raise e | R, .try e | R, .form _ e | R, .return e => by
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
      Expr.haltingIn_substTys s R f, Expr.passesHalting_substTys s R f args,
      Expr.divFree_substTys R f, argsDivFree_substTys R args, descends_substTys]
  | R, .assign ⟨_, p⟩ v => by
    simp [Expr.substTys, Expr.divFree, pathDivFree_substTys R p, Expr.divFree_substTys R v]
  | R, .if c _ a b => by
    simp [Expr.substTys, Expr.divFree, Expr.divFree_substTys R c, Expr.divFree_substTys _ a,
      Expr.divFree_substTys _ b, Roles.held_substTys, Roles.held_negated_substTys]
  | R, .match e _ arms => by
    simp [Expr.substTys, Expr.divFree, Expr.divFree_substTys R e, armsDivFree_substTys R _ arms,
      Expr.roleIn_substTys]
  | R, .held _ hs b => by
    simp [Expr.substTys, Expr.divFree, exprsDivFree_substTys R hs, Expr.divFree_substTys [] b]

theorem exprsDivFree_substTys : ∀ (R : Roles) (es : List Expr),
    exprsDivFree lim B H me R (substExprTys s es) = exprsDivFree lim B H me R es
  | _, [] => rfl
  | R, e :: es => by
    simp [substExprTys, exprsDivFree, Expr.divFree_substTys R e, exprsDivFree_substTys R es]

theorem fieldsDivFree_substTys : ∀ (R : Roles) (fs : List (Name × Expr)),
    fieldsDivFree lim B H me R (substFieldTys s fs) = fieldsDivFree lim B H me R fs
  | _, [] => rfl
  | R, (_, e) :: fs => by
    simp [substFieldTys, fieldsDivFree, Expr.divFree_substTys R e, fieldsDivFree_substTys R fs]

theorem argsDivFree_substTys : ∀ (R : Roles) (args : List Arg),
    argsDivFree lim B H me R (substArgTys s args) = argsDivFree lim B H me R args
  | _, [] => rfl
  | R, .value e :: args => by
    simp [substArgTys, argsDivFree, Expr.divFree_substTys R e, argsDivFree_substTys R args]
  | R, .inout ⟨_, p⟩ :: args => by
    simp [substArgTys, argsDivFree, pathDivFree_substTys R p, argsDivFree_substTys R args]

theorem pathDivFree_substTys : ∀ (R : Roles) (p : List Projection),
    pathDivFree lim B H me R (substPathTys s p) = pathDivFree lim B H me R p
  | _, [] => rfl
  | R, .field _ :: p => by simpa [substPathTys, pathDivFree] using pathDivFree_substTys R p
  | R, .index i :: p => by
    simp [substPathTys, pathDivFree, Expr.divFree_substTys R i, pathDivFree_substTys R p]

theorem armsDivFree_substTys : ∀ (R : Roles) (r : Role) (arms : List Arm),
    armsDivFree lim B H me R r (substArmTys s arms) = armsDivFree lim B H me R r arms
  | _, _, [] => rfl
  | R, r, ⟨_, _, g, b⟩ :: arms => by
    simp [substArmTys, armsDivFree, guardDivFree_substTys, Expr.divFree_substTys _ b,
      armsDivFree_substTys R r arms, Arm.role, Expr.writes_substTys, guardWrites_substTys]

theorem guardDivFree_substTys : ∀ (R : Roles) (g : Option Expr),
    guardDivFree lim B H me R (substGuardTys s g) = guardDivFree lim B H me R g
  | _, none => rfl
  | R, some g => by simp [substGuardTys, guardDivFree, Expr.divFree_substTys R g]

end

end

section

variable (s : RowSubst) {lim : Limited} {B : Name → Nat} {H : Name → List Nat}
  {me : Option (Name × Descent)}

theorem Expr.haltingIn_substRows (R : Roles) (e : Expr) : (e.substRows s).haltingIn R = e.haltingIn R := by
  cases e <;> first | rfl | (rename_i t _; cases t; rfl)

theorem haltingArg_substRows (R : Roles) (e : Expr) :
    haltingArg lim B H me R (e.substRows s) = haltingArg lim B H me R e := by
  cases e <;> first | rfl | (rename_i t _; cases t; rfl)

theorem Expr.callable_substRows (e : Expr) : (e.substRows s).callable = e.callable := by
  cases e <;> first | rfl | (rename_i t _; cases t; rfl)

theorem Expr.isSelf_substRows (e : Expr) : (e.substRows s).isSelf me = e.isSelf me := by
  cases e <;> first | rfl | (rename_i t _; cases t; rfl)

theorem Expr.roleIn_substRows (R : Roles) : ∀ e : Expr, (e.substRows s).roleIn R = e.roleIn R
  | .field e _ => by simp [Expr.substRows, Expr.roleIn, Expr.roleIn_substRows R e]
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .record .. | .variant .. | .list .. | .op .. | .view _ | .index .. | .call .. | .letIn ..
  | .varIn .. | .seq .. | .if .. | .match .. | .for .. | .raise .. | .perform _ .. | .withH ..
  | .held .. | .try .. | .form .. | .tryCatch .. | .closure .. | .assign ⟨_, _⟩ _ | .while .. | .loop _
  | .return _ => rfl

theorem argPart_substRows (R : Roles) : ∀ (k : Nat) (args : List Arg),
    argPart R k (substArgRows s args) = argPart R k args
  | 0, .value e :: _ => by simp [substArgRows, argPart, Expr.roleIn_substRows s R e]
  | 0, .inout ⟨_, _⟩ :: _ => rfl
  | k + 1, .value _ :: args | k + 1, .inout ⟨_, _⟩ :: args => by
    simp [substArgRows, argPart, argPart_substRows R k args]
  | 0, [] | _ + 1, [] => rfl

theorem argWith_substRows {ok : Expr → Bool} (hok : ∀ e, ok (e.substRows s) = ok e) :
    ∀ (k : Nat) (args : List Arg), argWith ok k (substArgRows s args) = argWith ok k args
  | 0, .value e :: _ => by simp [substArgRows, argWith, hok e]
  | 0, .inout ⟨_, _⟩ :: _ => rfl
  | k + 1, .value _ :: args | k + 1, .inout ⟨_, _⟩ :: args => by
    simp [substArgRows, argWith, argWith_substRows hok k args]
  | 0, [] | _ + 1, [] => rfl

theorem Expr.passesHalting_substRows (R : Roles) (e : Expr) (args : List Arg) :
    (e.substRows s).passesHalting lim B H me R (substArgRows s args) = e.passesHalting lim B H me R args := by
  cases e <;> try rfl
  case assign t _ => cases t; rfl
  simp [Expr.substRows, Expr.passesHalting, argWith_substRows s (haltingArg_substRows s R)]

theorem Expr.shrinksIn_substRows (R : Roles) (grow : Bool) (e : Expr) :
    (e.substRows s).shrinksIn R grow = e.shrinksIn R grow := by
  cases e
  case op o es =>
    rcases es with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> cases o <;> try rfl
    simp only [Expr.substRows, substExprRows, Expr.shrinksIn, Expr.movesBy,
      Expr.readVar?_substRows, Expr.intLit?_substRows]
  all_goals first | rfl | (rename_i t _; cases t; rfl)

theorem descends_substRows (R : Roles) (args : List Arg) :
    descends me R (substArgRows s args) = descends me R args := by
  unfold descends
  congr 1
  funext ⟨_, d⟩
  cases d with
  | parts k => simp [Descent.calls, argPart_substRows]
  | shrinks k g b =>
    have h₁ := argWith_substRows s (ok := Expr.shrinksIn R g) (Expr.shrinksIn_substRows s R g) k args
    cases b with
    | lit c => simp [Descent.calls, ShrinkBound.passedIn, h₁]
    | param j =>
      have h₂ := argWith_substRows s (ok := fun e => e.roleIn R == .limit)
        (fun e => by simp [Expr.roleIn_substRows]) j args
      simp [Descent.calls, ShrinkBound.passedIn, h₁, h₂]

theorem Expr.negated_substRows : ∀ e : Expr, (e.substRows s).negated.countings = e.negated.countings
  | .op o es => by
    rcases es with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> cases o <;> try rfl
    simp only [Expr.substRows, substExprRows, Expr.negated, Expr.countings,
      Expr.readVar?_substRows, Expr.bound?_substRows]
  | .assign ⟨_, _⟩ _ => rfl
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .record .. | .variant .. | .list .. | .field .. | .index .. | .closure .. | .call ..
  | .letIn .. | .varIn .. | .seq .. | .match .. | .for .. | .raise .. | .perform _ .. | .withH ..
  | .held .. | .try .. | .form .. | .tryCatch .. | .while .. | .loop .. | .return .. | .view .. | .if .. => rfl

theorem Roles.held_substRows (R : Roles) (c : Expr) : R.held me (c.substRows s) = R.held me c := by
  unfold Roles.held; rw [Expr.countings_substRows]

theorem Roles.held_negated_substRows (R : Roles) (c : Expr) :
    R.held me (c.substRows s).negated = R.held me c.negated := by
  unfold Roles.held; rw [Expr.negated_substRows]

mutual

theorem Expr.divFree_substRows : ∀ (R : Roles) (e : Expr),
    (e.substRows s).divFree lim B H me R = e.divFree lim B H me R
  | _, .var _ | _, .move _ | _, .int _ | _, .bool _ | _, .unit | _, .break | _, .continue
  | _, .fnRef .. | _, .method .. => rfl
  | R, .record _ _ fs => by simp [Expr.substRows, Expr.divFree, fieldsDivFree_substRows R fs]
  | R, .variant _ _ _ es | R, .list _ es | R, .op _ es | R, .view es => by
    simp [Expr.substRows, Expr.divFree, exprsDivFree_substRows R es]
  | _, .closure _ _ _ e => by simp [Expr.substRows, Expr.divFree, Expr.divFree_substRows [] e]
  | R, .field e _ | R, .raise e | R, .try e | R, .form _ e | R, .return e => by
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
      Expr.haltingIn_substRows s R f, Expr.passesHalting_substRows s R f args,
      Expr.divFree_substRows R f, argsDivFree_substRows R args, descends_substRows]
  | R, .assign ⟨_, p⟩ v => by
    simp [Expr.substRows, Expr.divFree, pathDivFree_substRows R p, Expr.divFree_substRows R v]
  | R, .if c _ a b => by
    simp [Expr.substRows, Expr.divFree, Expr.divFree_substRows R c, Expr.divFree_substRows _ a,
      Expr.divFree_substRows _ b, Roles.held_substRows, Roles.held_negated_substRows]
  | R, .match e _ arms => by
    simp [Expr.substRows, Expr.divFree, Expr.divFree_substRows R e, armsDivFree_substRows R _ arms,
      Expr.roleIn_substRows]
  | R, .held _ hs b => by
    simp [Expr.substRows, Expr.divFree, exprsDivFree_substRows R hs, Expr.divFree_substRows [] b]

theorem exprsDivFree_substRows : ∀ (R : Roles) (es : List Expr),
    exprsDivFree lim B H me R (substExprRows s es) = exprsDivFree lim B H me R es
  | _, [] => rfl
  | R, e :: es => by
    simp [substExprRows, exprsDivFree, Expr.divFree_substRows R e, exprsDivFree_substRows R es]

theorem fieldsDivFree_substRows : ∀ (R : Roles) (fs : List (Name × Expr)),
    fieldsDivFree lim B H me R (substFieldRows s fs) = fieldsDivFree lim B H me R fs
  | _, [] => rfl
  | R, (_, e) :: fs => by
    simp [substFieldRows, fieldsDivFree, Expr.divFree_substRows R e, fieldsDivFree_substRows R fs]

theorem argsDivFree_substRows : ∀ (R : Roles) (args : List Arg),
    argsDivFree lim B H me R (substArgRows s args) = argsDivFree lim B H me R args
  | _, [] => rfl
  | R, .value e :: args => by
    simp [substArgRows, argsDivFree, Expr.divFree_substRows R e, argsDivFree_substRows R args]
  | R, .inout ⟨_, p⟩ :: args => by
    simp [substArgRows, argsDivFree, pathDivFree_substRows R p, argsDivFree_substRows R args]

theorem pathDivFree_substRows : ∀ (R : Roles) (p : List Projection),
    pathDivFree lim B H me R (substPathRows s p) = pathDivFree lim B H me R p
  | _, [] => rfl
  | R, .field _ :: p => by simpa [substPathRows, pathDivFree] using pathDivFree_substRows R p
  | R, .index i :: p => by
    simp [substPathRows, pathDivFree, Expr.divFree_substRows R i, pathDivFree_substRows R p]

theorem armsDivFree_substRows : ∀ (R : Roles) (r : Role) (arms : List Arm),
    armsDivFree lim B H me R r (substArmRows s arms) = armsDivFree lim B H me R r arms
  | _, _, [] => rfl
  | R, r, ⟨_, _, g, b⟩ :: arms => by
    simp [substArmRows, armsDivFree, guardDivFree_substRows, Expr.divFree_substRows _ b,
      armsDivFree_substRows R r arms, Arm.role, Expr.writes_substRows, guardWrites_substRows]

theorem guardDivFree_substRows : ∀ (R : Roles) (g : Option Expr),
    guardDivFree lim B H me R (substGuardRows s g) = guardDivFree lim B H me R g
  | _, none => rfl
  | R, some g => by simp [substGuardRows, guardDivFree, Expr.divFree_substRows R g]

end

end

end Stilt
