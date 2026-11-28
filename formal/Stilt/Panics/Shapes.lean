import Stilt.Panics.Syntax
import Stilt.Generics.Commute

/-!
# Instantiation keeps the shapes the facts read

Instantiating the type parameters of code rewrites its types alone, so it keeps what the code
writes and resizes, the tests and the stores that give facts, and the paths that always jump.
-/

namespace Stilt

section

variable (s : TySubst) {lim : Limited}

theorem indexFree_substPathTys (x : Name) : ∀ p : List Projection,
    Place.indexFree ⟨x, substPathTys s p⟩ = Place.indexFree ⟨x, p⟩
  | [] => rfl
  | .field _ :: p => by
    simpa [substPathTys, Place.indexFree, Projection.fieldName?] using indexFree_substPathTys x p
  | .index _ :: p => by simp [substPathTys, Place.indexFree, Projection.fieldName?]

mutual

theorem Expr.writes_substTys : ∀ e : Expr, (e.substTys s).writes = e.writes
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .closure .. => rfl
  | .record _ _ fs => by simp [Expr.substTys, Expr.writes, fieldsWrites_substTys fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by simp [Expr.substTys, Expr.writes, exprsWrites_substTys es]
  | .field e _ | .raise e | .perform _ e | .try e | .form _ e | .loop e | .return e => by
    simp [Expr.substTys, Expr.writes, Expr.writes_substTys e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b | .while a b
  | .tryCatch a _ _ b _ => by simp [Expr.substTys, Expr.writes, Expr.writes_substTys a, Expr.writes_substTys b]
  | .call f args _ => by simp [Expr.substTys, Expr.writes, Expr.writes_substTys f, argsWrites_substTys args]
  | .assign ⟨_, p⟩ v => by simp [Expr.substTys, Expr.writes, pathWrites_substTys p, Expr.writes_substTys v]
  | .if c _ a b => by
    simp [Expr.substTys, Expr.writes, Expr.writes_substTys c, Expr.writes_substTys a, Expr.writes_substTys b]
  | .match e _ arms => by simp [Expr.substTys, Expr.writes, Expr.writes_substTys e, armsWrites_substTys arms]
  | .held _ hs b => by simp [Expr.substTys, Expr.writes, exprsWrites_substTys hs, Expr.writes_substTys b]

theorem exprsWrites_substTys : ∀ es : List Expr, exprsWrites (substExprTys s es) = exprsWrites es
  | [] => rfl
  | e :: es => by simp [substExprTys, exprsWrites, Expr.writes_substTys e, exprsWrites_substTys es]

theorem fieldsWrites_substTys : ∀ fs : List (Name × Expr), fieldsWrites (substFieldTys s fs) = fieldsWrites fs
  | [] => rfl
  | (_, e) :: fs => by simp [substFieldTys, fieldsWrites, Expr.writes_substTys e, fieldsWrites_substTys fs]

theorem argsWrites_substTys : ∀ args : List Arg, argsWrites (substArgTys s args) = argsWrites args
  | [] => rfl
  | .value e :: args => by simp [substArgTys, argsWrites, Expr.writes_substTys e, argsWrites_substTys args]
  | .inout ⟨_, p⟩ :: args => by simp [substArgTys, argsWrites, pathWrites_substTys p, argsWrites_substTys args]

theorem pathWrites_substTys : ∀ p : List Projection, pathWrites (substPathTys s p) = pathWrites p
  | [] => rfl
  | .field _ :: p => by simpa [substPathTys, pathWrites] using pathWrites_substTys p
  | .index i :: p => by simp [substPathTys, pathWrites, Expr.writes_substTys i, pathWrites_substTys p]

theorem armsWrites_substTys : ∀ arms : List Arm, armsWrites (substArmTys s arms) = armsWrites arms
  | [] => rfl
  | ⟨_, _, g, b⟩ :: arms => by
    simp [substArmTys, armsWrites, guardWrites_substTys g, Expr.writes_substTys b,
      armsWrites_substTys arms]

theorem guardWrites_substTys : ∀ g : Option Expr, guardWrites (substGuardTys s g) = guardWrites g
  | none => rfl
  | some g => by simp [substGuardTys, guardWrites, Expr.writes_substTys g]

end

theorem substPathTys_eq_nil (p : List Projection) : substPathTys s p = [] ↔ p = [] := by
  cases p with
  | nil => simp [substPathTys]
  | cons q _ => cases q <;> simp [substPathTys]

mutual

theorem Expr.resizes_substTys : ∀ e : Expr, (e.substTys s).resizes = e.resizes
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .closure .. => rfl
  | .record _ _ fs => by simp [Expr.substTys, Expr.resizes, fieldsResizes_substTys fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by simp [Expr.substTys, Expr.resizes, exprsResizes_substTys es]
  | .field e _ | .raise e | .perform _ e | .try e | .form _ e | .loop e | .return e => by
    simp [Expr.substTys, Expr.resizes, Expr.resizes_substTys e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b | .while a b
  | .tryCatch a _ _ b _ => by simp [Expr.substTys, Expr.resizes, Expr.resizes_substTys a, Expr.resizes_substTys b]
  | .call f args _ => by simp [Expr.substTys, Expr.resizes, Expr.resizes_substTys f, argsResizes_substTys args]
  | .assign ⟨_, p⟩ v => by simp [Expr.substTys, Expr.resizes, substPathTys_eq_nil, pathResizes_substTys p, Expr.resizes_substTys v]
  | .if c _ a b => by
    simp [Expr.substTys, Expr.resizes, Expr.resizes_substTys c, Expr.resizes_substTys a, Expr.resizes_substTys b]
  | .match e _ arms => by simp [Expr.substTys, Expr.resizes, Expr.resizes_substTys e, armsResizes_substTys arms]
  | .held _ hs b => by simp [Expr.substTys, Expr.resizes, exprsResizes_substTys hs, Expr.resizes_substTys b]

theorem exprsResizes_substTys : ∀ es : List Expr, exprsResizes (substExprTys s es) = exprsResizes es
  | [] => rfl
  | e :: es => by simp [substExprTys, exprsResizes, Expr.resizes_substTys e, exprsResizes_substTys es]

theorem fieldsResizes_substTys : ∀ fs : List (Name × Expr), fieldsResizes (substFieldTys s fs) = fieldsResizes fs
  | [] => rfl
  | (_, e) :: fs => by simp [substFieldTys, fieldsResizes, Expr.resizes_substTys e, fieldsResizes_substTys fs]

theorem argsResizes_substTys : ∀ args : List Arg, argsResizes (substArgTys s args) = argsResizes args
  | [] => rfl
  | .value e :: args => by simp [substArgTys, argsResizes, Expr.resizes_substTys e, argsResizes_substTys args]
  | .inout ⟨_, p⟩ :: args => by simp [substArgTys, argsResizes, substPathTys_eq_nil, pathResizes_substTys p, argsResizes_substTys args]

theorem pathResizes_substTys : ∀ p : List Projection, pathResizes (substPathTys s p) = pathResizes p
  | [] => rfl
  | .field _ :: p => by simpa [substPathTys, pathResizes] using pathResizes_substTys p
  | .index i :: p => by simp [substPathTys, pathResizes, Expr.resizes_substTys i, pathResizes_substTys p]

theorem armsResizes_substTys : ∀ arms : List Arm, armsResizes (substArmTys s arms) = armsResizes arms
  | [] => rfl
  | ⟨_, _, g, b⟩ :: arms => by
    simp [substArmTys, armsResizes, guardResizes_substTys g, Expr.resizes_substTys b,
      armsResizes_substTys arms]

theorem guardResizes_substTys : ∀ g : Option Expr, guardResizes (substGuardTys s g) = guardResizes g
  | none => rfl
  | some g => by simp [substGuardTys, guardResizes, Expr.resizes_substTys g]

end

theorem Expr.isVar_substTys (e : Expr) : (e.substTys s).isVar = e.isVar := by
  cases e
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

theorem byVar_substPathTys : ∀ p : List Projection,
    (substPathTys s p).all Projection.byVar = p.all Projection.byVar
  | [] => rfl
  | .field _ :: p => by simp [substPathTys, Projection.byVar, byVar_substPathTys p]
  | .index i :: p => by simp [substPathTys, Projection.byVar, Expr.isVar_substTys, byVar_substPathTys p]

theorem Expr.readVar?_substTys (e : Expr) : (e.substTys s).readVar? = e.readVar? := by
  cases e
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

theorem Expr.isZero_substTys (e : Expr) : (e.substTys s).isZero = e.isZero := by
  cases e
  case int n => rfl
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

theorem Expr.keyTerm?_substTys (e : Expr) : (e.substTys s).keyTerm? = e.keyTerm? := by
  cases e
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

theorem containsFacts_substTys (a k : Expr) :
    containsFacts (a.substTys s) (k.substTys s) = containsFacts a k := by
  simp [containsFacts, Expr.readVar?_substTys, Expr.keyTerm?_substTys]

theorem Expr.lenOf?_substTys (e : Expr) : (e.substTys s).lenOf? = e.lenOf? := by
  cases e
  case op o es =>
    rcases es with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> cases o <;> try rfl
    all_goals (rename_i l; cases l <;> simp [Expr.substTys, substExprTys, Expr.lenOf?, Expr.readVar?_substTys])
  case view es => rfl
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

theorem Expr.intLit?_substTys (e : Expr) : (e.substTys s).intLit? = e.intLit? := by
  cases e
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

theorem Expr.arithOf?_substTys (e : Expr) :
    (e.substTys s).arithOf? = e.arithOf?.map fun (o, a, b) => (o, a.substTys s, b.substTys s) := by
  cases e
  case op o es =>
    cases o <;> try rfl
    rename_i o t
    cases t <;> try rfl
    rcases es with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> rfl
  case view es => rfl
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

theorem Expr.lenLess?_substTys (e : Expr) : (e.substTys s).lenLess? = e.lenLess? := by
  unfold Expr.lenLess?
  rw [Expr.arithOf?_substTys]
  cases e.arithOf? with
  | none => simp only [Option.map_none, Expr.lenOf?_substTys]
  | some t =>
    obtain ⟨o, a, b⟩ := t
    cases o <;> simp only [Option.map_some, Expr.lenOf?_substTys, Expr.intLit?_substTys]

theorem Expr.offset?_substTys (e : Expr) : (e.substTys s).offset? = e.offset? := by
  unfold Expr.offset?
  rw [Expr.readVar?_substTys, Expr.arithOf?_substTys]
  cases e.readVar? with
  | some _ => rfl
  | none =>
    cases e.arithOf? with
    | none => rfl
    | some t =>
      obtain ⟨o, a, b⟩ := t
      simp only [Option.map_some, Expr.readVar?_substTys, Expr.intLit?_substTys]

theorem Expr.test?_substTys (e : Expr) : (e.substTys s).test? = e.test? := by
  cases e
  case op o es =>
    rcases es with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> cases o <;>
      simp [Expr.substTys, substExprTys, Expr.test?, Expr.readVar?_substTys, Expr.isZero_substTys,
        Expr.lenOf?_substTys]
  case view es => rfl
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

theorem Expr.rangeFacts_substTys (G : List Known) (x : Name) (body e : Expr) :
    (e.substTys s).rangeFacts G x (body.substTys s) = e.rangeFacts G x body := by
  cases e
  case op o es =>
    rcases es with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> cases o <;> try rfl
    all_goals (rename_i l; cases l <;> try rfl)
    cases a
    case int k =>
      simp [Expr.substTys, substExprTys, Expr.rangeFacts, Expr.lenLess?_substTys, Expr.resizes_substTys s]
    case var y =>
      simp [Expr.substTys, substExprTys, Expr.rangeFacts, Expr.lenLess?_substTys, Expr.resizes_substTys s]
    case assign t _ => obtain ⟨_, _⟩ := t; rfl
    all_goals rfl
  case view es => rfl
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

mutual

theorem Expr.alwaysJumps_substTys : ∀ e : Expr, (e.substTys s).alwaysJumps = e.alwaysJumps
  | .seq _ b | .letIn _ _ _ b | .varIn _ _ _ b => by
    simp [Expr.substTys, Expr.alwaysJumps, Expr.alwaysJumps_substTys b]
  | .if _ _ a b => by
    simp [Expr.substTys, Expr.alwaysJumps, Expr.alwaysJumps_substTys a, Expr.alwaysJumps_substTys b]
  | .match _ _ arms => by simp [Expr.substTys, Expr.alwaysJumps, armsAlwaysJump_substTys arms]
  | .assign ⟨_, _⟩ _ => rfl
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .record .. | .variant .. | .list .. | .op .. | .view _ | .field .. | .index .. | .closure .. | .call ..
  | .for .. | .raise .. | .perform _ .. | .withH .. | .try .. | .form .. | .tryCatch ..
  | .while .. | .loop .. | .return .. | .held .. => rfl

theorem armsAlwaysJump_substTys : ∀ arms : List Arm, armsAlwaysJump (substArmTys s arms) = armsAlwaysJump arms
  | [] => rfl
  | ⟨_, _, _, b⟩ :: arms => by
    simp [substArmTys, armsAlwaysJump, Expr.alwaysJumps_substTys b, armsAlwaysJump_substTys arms]

end

theorem Expr.isBool_substTys (b : Bool) (e : Expr) : (e.substTys s).isBool b = e.isBool b := by
  cases e
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

mutual

theorem Expr.factsAs_substTys : ∀ (b : Bool) (e : Expr), (e.substTys s).factsAs b = e.factsAs b
  | b, .if a _ x y => by
    simp only [Expr.substTys, Expr.factsAs, Expr.isBool_substTys, Expr.writes_substTys s,
      Expr.factsAs_substTys true a, Expr.factsAs_substTys false a, Expr.factsAs_substTys true x,
      Expr.factsAs_substTys false y]
  | b, .op o es => by
    simp only [Expr.substTys, Expr.factsAs]
    rw [Op.substTys_congr (fun o => opFacts b o (substExprTys s es)) fun _ _ => by
      rcases substExprTys s es with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> rfl]
    exact opFacts_substTys b o es
  | _, .assign ⟨_, _⟩ _ => rfl
  | _, .var _ | _, .move _ | _, .int _ | _, .bool _ | _, .unit | _, .break | _, .continue
  | _, .fnRef .. | _, .method .. | _, .record .. | _, .variant .. | _, .list .. | _, .field ..
  | _, .index .. | _, .closure .. | _, .call .. | _, .letIn .. | _, .varIn .. | _, .seq ..
  | _, .match .. | _, .for .. | _, .raise .. | _, .try .. | _, .form .. | _, .tryCatch .. | _, .while ..
  | _, .loop .. | _, .return .. | _, .perform .. | _, .withH .. | _, .view .. | _, .held .. => rfl

theorem opFacts_substTys : ∀ (b : Bool) (o : Op) (es : List Expr),
    opFacts b o (substExprTys s es) = opFacts b o es
  | _, o, [] => by
    cases o
    case map mo => cases mo <;> rfl
    all_goals rfl
  | b, o, [a] => by
    cases o
    case not => simp only [substExprTys, opFacts, Expr.factsAs_substTys (!b) a]
    case map mo => cases mo <;> rfl
    all_goals rfl
  | b, o, [l, r] => by
    cases o
    case compare cmp k =>
      have h := Expr.test?_substTys s (.op (.compare cmp k) [l, r])
      simp only [Expr.substTys, substExprTys, Op.substTys] at h
      simp only [substExprTys, opFacts, h]
    case map mo =>
      cases mo <;> try rfl
      simp only [substExprTys, opFacts, containsFacts_substTys]
    all_goals rfl
  | _, o, _ :: _ :: _ :: _ => by
    cases o
    case map mo => cases mo <;> rfl
    all_goals rfl

end

theorem Expr.facts_substTys (e : Expr) : (e.substTys s).facts = e.facts := Expr.factsAs_substTys s true e

theorem Expr.negFacts_substTys (e : Expr) : (e.substTys s).negFacts = e.negFacts :=
  Expr.factsAs_substTys s false e

theorem Expr.storedKey?_substTys (e : Expr) : (e.substTys s).storedKey? = e.storedKey? := by
  cases e
  case assign t v =>
    obtain ⟨m, p⟩ := t
    rcases p with _ | ⟨q, _⟩
    · cases v
      case op o es =>
        rcases es with _ | ⟨a, _ | ⟨k, _ | ⟨x, _ | _⟩⟩⟩ <;> cases o <;> try rfl
        all_goals rename_i mo; cases mo <;> try rfl
        simp only [Expr.substTys, substExprTys, substPathTys]
        simp [Expr.storedKey?, Expr.readVar?_substTys, Expr.keyTerm?_substTys, Expr.writes_substTys]
      case assign t _ => obtain ⟨_, _⟩ := t; rfl
      all_goals rfl
    · cases q <;> rfl
  all_goals rfl

theorem Expr.after_substTys (e : Expr) : (e.substTys s).after = e.after := by
  unfold Expr.after
  rw [Expr.storedKey?_substTys]
  congr 1
  cases e
  case «if» c τ t e =>
    simp [Expr.substTys, Expr.alwaysJumps_substTys s t, Expr.negFacts_substTys s c,
      Expr.writes_substTys s e, Expr.after_substTys t, Expr.after_substTys e]
  case seq a b => simp [Expr.substTys, Expr.writes_substTys s b, Expr.after_substTys a, Expr.after_substTys b]
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl
termination_by e

end

end Stilt
