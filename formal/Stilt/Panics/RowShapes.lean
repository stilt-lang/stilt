import Stilt.Panics.Instances

/-!
# Instantiation keeps the shapes the facts read

Instantiating the row variables of code rewrites its types alone, so it keeps what the code
writes and resizes, the tests and the stores that give facts, and the paths that always jump.
-/

namespace Stilt

section

variable (s : RowSubst) {lim : Limited}

theorem indexFree_substPathRows (x : Name) : ∀ p : List Projection,
    Place.indexFree ⟨x, substPathRows s p⟩ = Place.indexFree ⟨x, p⟩
  | [] => rfl
  | .field _ :: p => by
    simpa [substPathRows, Place.indexFree, Projection.fieldName?] using indexFree_substPathRows x p
  | .index _ :: p => by simp [substPathRows, Place.indexFree, Projection.fieldName?]

mutual

theorem Expr.writes_substRows : ∀ e : Expr, (e.substRows s).writes = e.writes
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .closure .. => rfl
  | .record _ _ fs => by simp [Expr.substRows, Expr.writes, fieldsWrites_substRows fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by simp [Expr.substRows, Expr.writes, exprsWrites_substRows es]
  | .field e _ | .raise e | .perform _ e | .try e | .form _ e | .loop e | .return e => by
    simp [Expr.substRows, Expr.writes, Expr.writes_substRows e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b | .while a b
  | .tryCatch a _ _ b _ => by simp [Expr.substRows, Expr.writes, Expr.writes_substRows a, Expr.writes_substRows b]
  | .call f args _ => by simp [Expr.substRows, Expr.writes, Expr.writes_substRows f, argsWrites_substRows args]
  | .assign ⟨_, p⟩ v => by simp [Expr.substRows, Expr.writes, pathWrites_substRows p, Expr.writes_substRows v]
  | .if c _ a b => by
    simp [Expr.substRows, Expr.writes, Expr.writes_substRows c, Expr.writes_substRows a, Expr.writes_substRows b]
  | .match e _ arms => by simp [Expr.substRows, Expr.writes, Expr.writes_substRows e, armsWrites_substRows arms]
  | .held _ hs b => by simp [Expr.substRows, Expr.writes, exprsWrites_substRows hs, Expr.writes_substRows b]

theorem exprsWrites_substRows : ∀ es : List Expr, exprsWrites (substExprRows s es) = exprsWrites es
  | [] => rfl
  | e :: es => by simp [substExprRows, exprsWrites, Expr.writes_substRows e, exprsWrites_substRows es]

theorem fieldsWrites_substRows : ∀ fs : List (Name × Expr), fieldsWrites (substFieldRows s fs) = fieldsWrites fs
  | [] => rfl
  | (_, e) :: fs => by simp [substFieldRows, fieldsWrites, Expr.writes_substRows e, fieldsWrites_substRows fs]

theorem argsWrites_substRows : ∀ args : List Arg, argsWrites (substArgRows s args) = argsWrites args
  | [] => rfl
  | .value e :: args => by simp [substArgRows, argsWrites, Expr.writes_substRows e, argsWrites_substRows args]
  | .inout ⟨_, p⟩ :: args => by simp [substArgRows, argsWrites, pathWrites_substRows p, argsWrites_substRows args]

theorem pathWrites_substRows : ∀ p : List Projection, pathWrites (substPathRows s p) = pathWrites p
  | [] => rfl
  | .field _ :: p => by simpa [substPathRows, pathWrites] using pathWrites_substRows p
  | .index i :: p => by simp [substPathRows, pathWrites, Expr.writes_substRows i, pathWrites_substRows p]

theorem armsWrites_substRows : ∀ arms : List Arm, armsWrites (substArmRows s arms) = armsWrites arms
  | [] => rfl
  | ⟨_, _, g, b⟩ :: arms => by
    simp [substArmRows, armsWrites, guardWrites_substRows g, Expr.writes_substRows b,
      armsWrites_substRows arms]

theorem guardWrites_substRows : ∀ g : Option Expr, guardWrites (substGuardRows s g) = guardWrites g
  | none => rfl
  | some g => by simp [substGuardRows, guardWrites, Expr.writes_substRows g]

end

theorem substPathRows_eq_nil (p : List Projection) : substPathRows s p = [] ↔ p = [] := by
  cases p with
  | nil => simp [substPathRows]
  | cons q _ => cases q <;> simp [substPathRows]

mutual

theorem Expr.resizes_substRows : ∀ e : Expr, (e.substRows s).resizes = e.resizes
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .closure .. => rfl
  | .record _ _ fs => by simp [Expr.substRows, Expr.resizes, fieldsResizes_substRows fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by simp [Expr.substRows, Expr.resizes, exprsResizes_substRows es]
  | .field e _ | .raise e | .perform _ e | .try e | .form _ e | .loop e | .return e => by
    simp [Expr.substRows, Expr.resizes, Expr.resizes_substRows e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b | .while a b
  | .tryCatch a _ _ b _ => by simp [Expr.substRows, Expr.resizes, Expr.resizes_substRows a, Expr.resizes_substRows b]
  | .call f args _ => by simp [Expr.substRows, Expr.resizes, Expr.resizes_substRows f, argsResizes_substRows args]
  | .assign ⟨_, p⟩ v => by simp [Expr.substRows, Expr.resizes, substPathRows_eq_nil, pathResizes_substRows p, Expr.resizes_substRows v]
  | .if c _ a b => by
    simp [Expr.substRows, Expr.resizes, Expr.resizes_substRows c, Expr.resizes_substRows a, Expr.resizes_substRows b]
  | .match e _ arms => by simp [Expr.substRows, Expr.resizes, Expr.resizes_substRows e, armsResizes_substRows arms]
  | .held _ hs b => by simp [Expr.substRows, Expr.resizes, exprsResizes_substRows hs, Expr.resizes_substRows b]

theorem exprsResizes_substRows : ∀ es : List Expr, exprsResizes (substExprRows s es) = exprsResizes es
  | [] => rfl
  | e :: es => by simp [substExprRows, exprsResizes, Expr.resizes_substRows e, exprsResizes_substRows es]

theorem fieldsResizes_substRows : ∀ fs : List (Name × Expr), fieldsResizes (substFieldRows s fs) = fieldsResizes fs
  | [] => rfl
  | (_, e) :: fs => by simp [substFieldRows, fieldsResizes, Expr.resizes_substRows e, fieldsResizes_substRows fs]

theorem argsResizes_substRows : ∀ args : List Arg, argsResizes (substArgRows s args) = argsResizes args
  | [] => rfl
  | .value e :: args => by simp [substArgRows, argsResizes, Expr.resizes_substRows e, argsResizes_substRows args]
  | .inout ⟨_, p⟩ :: args => by simp [substArgRows, argsResizes, substPathRows_eq_nil, pathResizes_substRows p, argsResizes_substRows args]

theorem pathResizes_substRows : ∀ p : List Projection, pathResizes (substPathRows s p) = pathResizes p
  | [] => rfl
  | .field _ :: p => by simpa [substPathRows, pathResizes] using pathResizes_substRows p
  | .index i :: p => by simp [substPathRows, pathResizes, Expr.resizes_substRows i, pathResizes_substRows p]

theorem armsResizes_substRows : ∀ arms : List Arm, armsResizes (substArmRows s arms) = armsResizes arms
  | [] => rfl
  | ⟨_, _, g, b⟩ :: arms => by
    simp [substArmRows, armsResizes, guardResizes_substRows g, Expr.resizes_substRows b,
      armsResizes_substRows arms]

theorem guardResizes_substRows : ∀ g : Option Expr,
    guardResizes (substGuardRows s g) = guardResizes g
  | none => rfl
  | some g => by simp [substGuardRows, guardResizes, Expr.resizes_substRows g]

end

theorem Expr.isVar_substRows (e : Expr) : (e.substRows s).isVar = e.isVar := by
  cases e
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

theorem byVar_substPathRows : ∀ p : List Projection,
    (substPathRows s p).all Projection.byVar = p.all Projection.byVar
  | [] => rfl
  | .field _ :: p => by simp [substPathRows, Projection.byVar, byVar_substPathRows p]
  | .index i :: p => by simp [substPathRows, Projection.byVar, Expr.isVar_substRows, byVar_substPathRows p]

theorem Expr.readVar?_substRows (e : Expr) : (e.substRows s).readVar? = e.readVar? := by
  cases e
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

theorem Expr.isZero_substRows (e : Expr) : (e.substRows s).isZero = e.isZero := by
  cases e
  case int n => rfl
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

theorem Expr.keyTerm?_substRows (e : Expr) : (e.substRows s).keyTerm? = e.keyTerm? := by
  cases e
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

theorem containsFacts_substRows (a k : Expr) :
    containsFacts (a.substRows s) (k.substRows s) = containsFacts a k := by
  simp [containsFacts, Expr.readVar?_substRows, Expr.keyTerm?_substRows]

theorem Expr.lenOf?_substRows (e : Expr) : (e.substRows s).lenOf? = e.lenOf? := by
  cases e
  case op o es =>
    rcases es with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> cases o <;> try rfl
    all_goals (rename_i l; cases l <;> simp [Expr.substRows, substExprRows, Expr.lenOf?, Expr.readVar?_substRows])
  case view es => rfl
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

theorem Expr.intLit?_substRows (e : Expr) : (e.substRows s).intLit? = e.intLit? := by
  cases e
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

theorem Expr.arithOf?_substRows (e : Expr) :
    (e.substRows s).arithOf? = e.arithOf?.map fun (o, a, b) => (o, a.substRows s, b.substRows s) := by
  cases e
  case op o es =>
    cases o <;> try rfl
    rename_i o t
    cases t <;> try rfl
    rcases es with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> rfl
  case view es => rfl
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

theorem Expr.lenLess?_substRows (e : Expr) : (e.substRows s).lenLess? = e.lenLess? := by
  unfold Expr.lenLess?
  rw [Expr.arithOf?_substRows]
  cases e.arithOf? with
  | none => simp only [Option.map_none, Expr.lenOf?_substRows]
  | some t =>
    obtain ⟨o, a, b⟩ := t
    cases o <;> simp only [Option.map_some, Expr.lenOf?_substRows, Expr.intLit?_substRows]

theorem Expr.offset?_substRows (e : Expr) : (e.substRows s).offset? = e.offset? := by
  unfold Expr.offset?
  rw [Expr.readVar?_substRows, Expr.arithOf?_substRows]
  cases e.readVar? with
  | some _ => rfl
  | none =>
    cases e.arithOf? with
    | none => rfl
    | some t =>
      obtain ⟨o, a, b⟩ := t
      simp only [Option.map_some, Expr.readVar?_substRows, Expr.intLit?_substRows]

theorem Expr.test?_substRows (e : Expr) : (e.substRows s).test? = e.test? := by
  cases e
  case op o es =>
    rcases es with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> cases o <;>
      simp [Expr.substRows, substExprRows, Expr.test?, Expr.readVar?_substRows, Expr.isZero_substRows,
        Expr.lenOf?_substRows]
  case view es => rfl
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

theorem Expr.rangeFacts_substRows (G : List Known) (x : Name) (body e : Expr) :
    (e.substRows s).rangeFacts G x (body.substRows s) = e.rangeFacts G x body := by
  cases e
  case op o es =>
    rcases es with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> cases o <;> try rfl
    all_goals (rename_i l; cases l <;> try rfl)
    cases a
    case int k =>
      simp [Expr.substRows, substExprRows, Expr.rangeFacts, Expr.lenLess?_substRows, Expr.resizes_substRows s]
    case var y =>
      simp [Expr.substRows, substExprRows, Expr.rangeFacts, Expr.lenLess?_substRows, Expr.resizes_substRows s]
    case assign t _ => obtain ⟨_, _⟩ := t; rfl
    all_goals rfl
  case view es => rfl
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

mutual

theorem Expr.alwaysJumps_substRows : ∀ e : Expr, (e.substRows s).alwaysJumps = e.alwaysJumps
  | .seq _ b | .letIn _ _ _ b | .varIn _ _ _ b => by
    simp [Expr.substRows, Expr.alwaysJumps, Expr.alwaysJumps_substRows b]
  | .if _ _ a b => by
    simp [Expr.substRows, Expr.alwaysJumps, Expr.alwaysJumps_substRows a, Expr.alwaysJumps_substRows b]
  | .match _ _ arms => by simp [Expr.substRows, Expr.alwaysJumps, armsAlwaysJump_substRows arms]
  | .assign ⟨_, _⟩ _ => rfl
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method ..
  | .record .. | .variant .. | .list .. | .op .. | .view _ | .field .. | .index .. | .closure .. | .call ..
  | .for .. | .raise .. | .perform _ .. | .withH .. | .try .. | .form .. | .tryCatch ..
  | .while .. | .loop .. | .return .. | .held .. => rfl

theorem armsAlwaysJump_substRows : ∀ arms : List Arm, armsAlwaysJump (substArmRows s arms) = armsAlwaysJump arms
  | [] => rfl
  | ⟨_, _, _, b⟩ :: arms => by
    simp [substArmRows, armsAlwaysJump, Expr.alwaysJumps_substRows b, armsAlwaysJump_substRows arms]

end

theorem Expr.isBool_substRows (b : Bool) (e : Expr) : (e.substRows s).isBool b = e.isBool b := by
  cases e
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl

mutual

theorem Expr.factsAs_substRows : ∀ (b : Bool) (e : Expr), (e.substRows s).factsAs b = e.factsAs b
  | b, .if a _ x y => by
    simp only [Expr.substRows, Expr.factsAs, Expr.isBool_substRows, Expr.writes_substRows s,
      Expr.factsAs_substRows true a, Expr.factsAs_substRows false a, Expr.factsAs_substRows true x,
      Expr.factsAs_substRows false y]
  | b, .op o es => by
    simp only [Expr.substRows, Expr.factsAs]
    exact opFacts_substRows b o es
  | _, .assign ⟨_, _⟩ _ => rfl
  | _, .var _ | _, .move _ | _, .int _ | _, .bool _ | _, .unit | _, .break | _, .continue
  | _, .fnRef .. | _, .method .. | _, .record .. | _, .variant .. | _, .list .. | _, .field ..
  | _, .index .. | _, .closure .. | _, .call .. | _, .letIn .. | _, .varIn .. | _, .seq ..
  | _, .match .. | _, .for .. | _, .raise .. | _, .try .. | _, .form .. | _, .tryCatch .. | _, .while ..
  | _, .loop .. | _, .return .. | _, .perform .. | _, .withH .. | _, .view .. | _, .held .. => rfl

theorem opFacts_substRows : ∀ (b : Bool) (o : Op) (es : List Expr),
    opFacts b o (substExprRows s es) = opFacts b o es
  | _, o, [] => by
    cases o
    case map mo => cases mo <;> rfl
    all_goals rfl
  | b, o, [a] => by
    cases o
    case not => simp only [substExprRows, opFacts, Expr.factsAs_substRows (!b) a]
    case map mo => cases mo <;> rfl
    all_goals rfl
  | b, o, [l, r] => by
    cases o
    case compare cmp k =>
      have h := Expr.test?_substRows s (.op (.compare cmp k) [l, r])
      simp only [Expr.substRows, substExprRows] at h
      simp only [substExprRows, opFacts, h]
    case map mo =>
      cases mo <;> try rfl
      simp only [substExprRows, opFacts, containsFacts_substRows]
    all_goals rfl
  | _, o, _ :: _ :: _ :: _ => by
    cases o
    case map mo => cases mo <;> rfl
    all_goals rfl

end

theorem Expr.facts_substRows (e : Expr) : (e.substRows s).facts = e.facts := Expr.factsAs_substRows s true e

theorem Expr.negFacts_substRows (e : Expr) : (e.substRows s).negFacts = e.negFacts :=
  Expr.factsAs_substRows s false e

theorem Expr.storedKey?_substRows (e : Expr) : (e.substRows s).storedKey? = e.storedKey? := by
  cases e
  case assign t v =>
    obtain ⟨m, p⟩ := t
    rcases p with _ | ⟨q, _⟩
    · cases v
      case op o es =>
        rcases es with _ | ⟨a, _ | ⟨k, _ | ⟨x, _ | _⟩⟩⟩ <;> cases o <;> try rfl
        all_goals rename_i mo; cases mo <;> try rfl
        simp only [Expr.substRows, substExprRows, substPathRows]
        simp [Expr.storedKey?, Expr.readVar?_substRows, Expr.keyTerm?_substRows, Expr.writes_substRows]
      case assign t _ => obtain ⟨_, _⟩ := t; rfl
      all_goals rfl
    · cases q <;> rfl
  all_goals rfl

theorem Expr.after_substRows (e : Expr) : (e.substRows s).after = e.after := by
  unfold Expr.after
  rw [Expr.storedKey?_substRows]
  congr 1
  cases e
  case «if» c τ t e =>
    simp [Expr.substRows, Expr.alwaysJumps_substRows s t, Expr.negFacts_substRows s c,
      Expr.writes_substRows s e, Expr.after_substRows t, Expr.after_substRows e]
  case seq a b => simp [Expr.substRows, Expr.writes_substRows s b, Expr.after_substRows a, Expr.after_substRows b]
  case assign t _ => obtain ⟨_, _⟩ := t; rfl
  all_goals rfl
termination_by e

end

end Stilt
