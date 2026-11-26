import Stilt.Ends.Counting
import Stilt.Panics.RowInstances

/-!
# Instantiation keeps counting loops

A call instantiates the type parameters and the row variables of the body it
runs. Instantiation rewrites types alone, so an instantiated `while` counts
exactly when the `while` does.
-/

namespace Stilt

section

variable (s : TySubst)

mutual

theorem Expr.contFree_substTys : ∀ e : Expr, (e.substTys s).contFree = e.contFree
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .closure .. | .loop _ => rfl
  | .record _ _ fs => by simp [Expr.substTys, Expr.contFree, fieldsContFree_substTys fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by simp [Expr.substTys, Expr.contFree, exprsContFree_substTys es]
  | .field e _ | .raise e | .perform _ e | .try e | .form _ e | .return e | .for _ _ e _ | .while e _ => by
    simp [Expr.substTys, Expr.contFree, Expr.contFree_substTys e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b | .tryCatch a _ _ b _ => by
    simp [Expr.substTys, Expr.contFree, Expr.contFree_substTys a, Expr.contFree_substTys b]
  | .call f args _ => by simp [Expr.substTys, Expr.contFree, Expr.contFree_substTys f, argsContFree_substTys args]
  | .assign ⟨_, p⟩ v => by simp [Expr.substTys, Expr.contFree, pathContFree_substTys p, Expr.contFree_substTys v]
  | .if c _ a b => by
    simp [Expr.substTys, Expr.contFree, Expr.contFree_substTys c, Expr.contFree_substTys a, Expr.contFree_substTys b]
  | .match e _ arms => by simp [Expr.substTys, Expr.contFree, Expr.contFree_substTys e, armsContFree_substTys arms]
  | .held _ hs b => by simp [Expr.substTys, Expr.contFree, exprsContFree_substTys hs, Expr.contFree_substTys b]

theorem exprsContFree_substTys : ∀ es : List Expr, exprsContFree (substExprTys s es) = exprsContFree es
  | [] => rfl
  | e :: es => by simp [substExprTys, exprsContFree, Expr.contFree_substTys e, exprsContFree_substTys es]

theorem fieldsContFree_substTys :
    ∀ fs : List (Name × Expr), fieldsContFree (substFieldTys s fs) = fieldsContFree fs
  | [] => rfl
  | (_, e) :: fs => by simp [substFieldTys, fieldsContFree, Expr.contFree_substTys e, fieldsContFree_substTys fs]

theorem argsContFree_substTys : ∀ args : List Arg, argsContFree (substArgTys s args) = argsContFree args
  | [] => rfl
  | .value e :: args => by simp [substArgTys, argsContFree, Expr.contFree_substTys e, argsContFree_substTys args]
  | .inout ⟨_, p⟩ :: args => by simp [substArgTys, argsContFree, pathContFree_substTys p, argsContFree_substTys args]

theorem pathContFree_substTys : ∀ p : List Projection, pathContFree (substPathTys s p) = pathContFree p
  | [] => rfl
  | .field _ :: p => by simpa [substPathTys, pathContFree] using pathContFree_substTys p
  | .index i :: p => by simp [substPathTys, pathContFree, Expr.contFree_substTys i, pathContFree_substTys p]

theorem armsContFree_substTys : ∀ arms : List Arm, armsContFree (substArmTys s arms) = armsContFree arms
  | [] => rfl
  | ⟨_, _, b⟩ :: arms => by simp [substArmTys, armsContFree, Expr.contFree_substTys b, armsContFree_substTys arms]

end

theorem Expr.bound?_substTys : ∀ e : Expr, (e.substTys s).bound? = e.bound?
  | .op o es => by
    rcases es with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> cases o <;> try rfl
    all_goals first
      | (rename_i l; cases l <;> first | rfl | (cases a <;> first | rfl | (rename_i t _; cases t; rfl)))
      | simp only [Expr.substTys, substExprTys, Op.substTys, Expr.bound?, Expr.bound?_substTys a,
          Expr.bound?_substTys b]
  | .assign ⟨_, _⟩ _ => rfl
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .record .. | .variant .. | .list .. | .field .. | .index .. | .closure .. | .call ..
  | .letIn .. | .varIn .. | .seq .. | .if .. | .match .. | .for .. | .raise .. | .perform _ .. | .withH .. | .held .. | .try .. | .form .. | .tryCatch ..
  | .while .. | .loop .. | .return .. | .view .. => rfl

theorem Expr.countings_substTys : ∀ e : Expr, (e.substTys s).countings = e.countings
  | .op o es => by
    rcases es with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> cases o <;> try rfl
    simp only [Expr.substTys, substExprTys, Op.substTys, Expr.countings, Expr.readVar?_substTys,
      Expr.bound?_substTys]
  | .if a τ x y => by
    simp only [Expr.substTys, Expr.countings, Expr.isBool_substTys, Expr.countings_substTys a]
  | .assign ⟨_, _⟩ _ => rfl
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .record .. | .variant .. | .list .. | .field .. | .index .. | .closure .. | .call ..
  | .letIn .. | .varIn .. | .seq .. | .match .. | .for .. | .raise .. | .perform _ .. | .withH .. | .held .. | .try .. | .form .. | .tryCatch ..
  | .while .. | .loop .. | .return .. | .view .. => rfl

theorem Expr.movesBy_substTys (v : Name) (grow : Bool) (e : Expr) :
    (e.substTys s).movesBy v grow = e.movesBy v grow := by
  cases e
  case op o es =>
    rcases es with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> cases o <;> try rfl
    simp only [Expr.substTys, substExprTys, Op.substTys, Expr.movesBy, Expr.readVar?_substTys,
      Expr.intLit?_substTys]
  case view es => rfl
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

theorem Expr.isStep_substTys (v : Name) (grow : Bool) (e : Expr) :
    (e.substTys s).isStep v grow = e.isStep v grow := by
  cases e
  case assign t value =>
    obtain ⟨x, p⟩ := t
    cases p with
    | nil => simp [Expr.substTys, substPathTys, Expr.isStep, Expr.movesBy_substTys]
    | cons q ps => cases q <;> simp [Expr.substTys, substPathTys, Expr.isStep]
  all_goals rfl

theorem Expr.steps_substTys (v : Name) (grow : Bool) : ∀ e : Expr,
    (e.substTys s).steps v grow = e.steps v grow
  | .seq a b => by
    simp only [Expr.substTys, Expr.steps, Expr.steps_substTys v grow a, Expr.steps_substTys v grow b,
      Expr.writes_substTys s, Expr.contFree_substTys]
  | .assign ⟨x, p⟩ value => by
    exact Expr.isStep_substTys s v grow (.assign ⟨x, p⟩ value)
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .record .. | .variant .. | .list .. | .op .. | .view _ | .field .. | .index .. | .closure .. | .call ..
  | .letIn .. | .varIn .. | .if .. | .match .. | .for .. | .raise .. | .perform _ .. | .withH .. | .held .. | .try .. | .form .. | .tryCatch ..
  | .while .. | .loop .. | .return .. => rfl

theorem Expr.countsIn_substTys (c body : Expr) :
    Expr.countsIn (c.substTys s) (body.substTys s) = Expr.countsIn c body := by
  simp only [Expr.countsIn, Expr.countings_substTys, Expr.steps_substTys, Expr.writes_substTys s]

end

section

variable (s : RowSubst)

mutual

theorem Expr.contFree_substRows : ∀ e : Expr, (e.substRows s).contFree = e.contFree
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .closure .. | .loop _ => rfl
  | .record _ _ fs => by simp [Expr.substRows, Expr.contFree, fieldsContFree_substRows fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by simp [Expr.substRows, Expr.contFree, exprsContFree_substRows es]
  | .field e _ | .raise e | .perform _ e | .try e | .form _ e | .return e | .for _ _ e _ | .while e _ => by
    simp [Expr.substRows, Expr.contFree, Expr.contFree_substRows e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b | .tryCatch a _ _ b _ => by
    simp [Expr.substRows, Expr.contFree, Expr.contFree_substRows a, Expr.contFree_substRows b]
  | .call f args _ => by simp [Expr.substRows, Expr.contFree, Expr.contFree_substRows f, argsContFree_substRows args]
  | .assign ⟨_, p⟩ v => by simp [Expr.substRows, Expr.contFree, pathContFree_substRows p, Expr.contFree_substRows v]
  | .if c _ a b => by
    simp [Expr.substRows, Expr.contFree, Expr.contFree_substRows c, Expr.contFree_substRows a, Expr.contFree_substRows b]
  | .match e _ arms => by simp [Expr.substRows, Expr.contFree, Expr.contFree_substRows e, armsContFree_substRows arms]
  | .held _ hs b => by simp [Expr.substRows, Expr.contFree, exprsContFree_substRows hs, Expr.contFree_substRows b]

theorem exprsContFree_substRows : ∀ es : List Expr, exprsContFree (substExprRows s es) = exprsContFree es
  | [] => rfl
  | e :: es => by simp [substExprRows, exprsContFree, Expr.contFree_substRows e, exprsContFree_substRows es]

theorem fieldsContFree_substRows :
    ∀ fs : List (Name × Expr), fieldsContFree (substFieldRows s fs) = fieldsContFree fs
  | [] => rfl
  | (_, e) :: fs => by simp [substFieldRows, fieldsContFree, Expr.contFree_substRows e, fieldsContFree_substRows fs]

theorem argsContFree_substRows : ∀ args : List Arg, argsContFree (substArgRows s args) = argsContFree args
  | [] => rfl
  | .value e :: args => by simp [substArgRows, argsContFree, Expr.contFree_substRows e, argsContFree_substRows args]
  | .inout ⟨_, p⟩ :: args => by simp [substArgRows, argsContFree, pathContFree_substRows p, argsContFree_substRows args]

theorem pathContFree_substRows : ∀ p : List Projection, pathContFree (substPathRows s p) = pathContFree p
  | [] => rfl
  | .field _ :: p => by simpa [substPathRows, pathContFree] using pathContFree_substRows p
  | .index i :: p => by simp [substPathRows, pathContFree, Expr.contFree_substRows i, pathContFree_substRows p]

theorem armsContFree_substRows : ∀ arms : List Arm, armsContFree (substArmRows s arms) = armsContFree arms
  | [] => rfl
  | ⟨_, _, b⟩ :: arms => by simp [substArmRows, armsContFree, Expr.contFree_substRows b, armsContFree_substRows arms]

end

theorem Expr.bound?_substRows : ∀ e : Expr, (e.substRows s).bound? = e.bound?
  | .op o es => by
    rcases es with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> cases o <;> try rfl
    all_goals first
      | (rename_i l; cases l <;> first | rfl | (cases a <;> first | rfl | (rename_i t _; cases t; rfl)))
      | simp only [Expr.substRows, substExprRows, Expr.bound?, Expr.bound?_substRows a, Expr.bound?_substRows b]
  | .assign ⟨_, _⟩ _ => rfl
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .record .. | .variant .. | .list .. | .field .. | .index .. | .closure .. | .call ..
  | .letIn .. | .varIn .. | .seq .. | .if .. | .match .. | .for .. | .raise .. | .perform _ .. | .withH .. | .held .. | .try .. | .form .. | .tryCatch ..
  | .while .. | .loop .. | .return .. | .view .. => rfl

theorem Expr.countings_substRows : ∀ e : Expr, (e.substRows s).countings = e.countings
  | .op o es => by
    rcases es with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> cases o <;> try rfl
    simp only [Expr.substRows, substExprRows, Expr.countings, Expr.readVar?_substRows, Expr.bound?_substRows]
  | .if a τ x y => by
    simp only [Expr.substRows, Expr.countings, Expr.isBool_substRows, Expr.countings_substRows a]
  | .assign ⟨_, _⟩ _ => rfl
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .record .. | .variant .. | .list .. | .field .. | .index .. | .closure .. | .call ..
  | .letIn .. | .varIn .. | .seq .. | .match .. | .for .. | .raise .. | .perform _ .. | .withH .. | .held .. | .try .. | .form .. | .tryCatch ..
  | .while .. | .loop .. | .return .. | .view .. => rfl

theorem Expr.movesBy_substRows (v : Name) (grow : Bool) (e : Expr) :
    (e.substRows s).movesBy v grow = e.movesBy v grow := by
  cases e
  case op o es =>
    rcases es with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> cases o <;> try rfl
    simp only [Expr.substRows, substExprRows, Expr.movesBy, Expr.readVar?_substRows, Expr.intLit?_substRows]
  case view es => rfl
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

theorem Expr.isStep_substRows (v : Name) (grow : Bool) (e : Expr) :
    (e.substRows s).isStep v grow = e.isStep v grow := by
  cases e
  case assign t value =>
    obtain ⟨x, p⟩ := t
    cases p with
    | nil => simp [Expr.substRows, substPathRows, Expr.isStep, Expr.movesBy_substRows]
    | cons q ps => cases q <;> simp [Expr.substRows, substPathRows, Expr.isStep]
  all_goals rfl

theorem Expr.steps_substRows (v : Name) (grow : Bool) : ∀ e : Expr,
    (e.substRows s).steps v grow = e.steps v grow
  | .seq a b => by
    simp only [Expr.substRows, Expr.steps, Expr.steps_substRows v grow a, Expr.steps_substRows v grow b,
      Expr.writes_substRows s, Expr.contFree_substRows]
  | .assign ⟨x, p⟩ value => by
    exact Expr.isStep_substRows s v grow (.assign ⟨x, p⟩ value)
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .record .. | .variant .. | .list .. | .op .. | .view _ | .field .. | .index .. | .closure .. | .call ..
  | .letIn .. | .varIn .. | .if .. | .match .. | .for .. | .raise .. | .perform _ .. | .withH .. | .held .. | .try .. | .form .. | .tryCatch ..
  | .while .. | .loop .. | .return .. => rfl

theorem Expr.countsIn_substRows (c body : Expr) :
    Expr.countsIn (c.substRows s) (body.substRows s) = Expr.countsIn c body := by
  simp only [Expr.countsIn, Expr.countings_substRows, Expr.steps_substRows, Expr.writes_substRows s]

end

end Stilt
