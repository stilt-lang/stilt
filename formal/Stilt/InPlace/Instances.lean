import Stilt.InPlace.Bodies
import Stilt.Generics.Commute

/-!
# Instances of bodies

A call instantiates the type parameters of the body it runs (types.no-type-arguments),
and what in-place agreement needs of a body survives that, as it survives an
instantiation of row variables (`Stilt.InPlace.Bodies`): exclusivity and
distinct parameter names look at places, calls and parameter names, never at
the types an instantiation rewrites.
-/

namespace Stilt

section Instantiation

variable (s : TySubst)

theorem fields_substPathTys (path : List Projection) :
    (substPathTys s path).filterMap Projection.fieldName? =
      path.filterMap Projection.fieldName? := by
  induction path with
  | nil => rfl
  | cons p path ih =>
    cases p <;> simp [substPathTys, Projection.fieldName?, ih, List.filterMap_cons]

theorem shape_substPathTys (x : Name) (path : List Projection) :
    (Place.mk x (substPathTys s path)).shape = (Place.mk x path).shape := by
  simp [Place.shape, fields_substPathTys]

theorem inoutShapes_substArgTys (args : List Arg) :
    inoutShapes (substArgTys s args) = inoutShapes args := by
  induction args with
  | nil => rfl
  | cons a args ih =>
    cases a with
    | value e => simpa [substArgTys, inoutShapes] using ih
    | inout p =>
      obtain ⟨x, path⟩ := p
      simp [substArgTys, inoutShapes, ih, shape_substPathTys]

theorem placeShape_substTys : ∀ e : Expr, (e.substTys s).placeShape = e.placeShape
  | .var _ | .move _ => rfl
  | .field e f => by
    rw [show (Expr.field e f).substTys s = .field (e.substTys s) f by simp [Expr.substTys],
      placeShape_field, placeShape_field, placeShape_substTys e]
  | .index e i => by
    rw [show (Expr.index e i).substTys s = .index (e.substTys s) (i.substTys s) by
      simp [Expr.substTys], placeShape_index, placeShape_index, placeShape_substTys e]
  | .int _ | .bool _ | .unit | .break | .continue | .record .. | .variant .. | .list .. | .op .. | .view _ | .fnRef .. | .method .. | .closure ..
  | .call .. | .letIn .. | .varIn .. | .assign ⟨_, _⟩ _ | .seq .. | .if .. | .match .. | .for ..
  | .raise _ | .perform _ _ | .try _ | .form _ _ | .loop _ | .return _ | .tryCatch .. | .while .. | .withH ..
  | .held .. => by
    simp [Expr.substTys, Expr.placeShape, Expr.place?]

theorem iterated_substTys (e : Expr) : iterated (e.substTys s) = iterated e := by
  have := placeShape_substTys s e
  simp only [Expr.placeShape] at this
  simp [iterated, this]

mutual

/-- Instantiating a body's type parameters keeps it exclusive. -/
theorem Expr.exclusive_substTys :
    ∀ (e : Expr) (r : List Shape), (e.substTys s).exclusive r = e.exclusive r
  | .var _, _ | .move _, _ | .int _, _ | .bool _, _ | .unit, _ | .fnRef .., _ | .method .., _ => rfl
  | .record _ _ fields, r => fieldsExclusive_substTys fields r
  | .variant _ _ _ es, r => exprsExclusive_substTys es r
  | .list _ es, r => exprsExclusive_substTys es r
  | .op _ es, r | .view es, r => exprsExclusive_substTys es r
  | .field e _, r => by simpa [Expr.substTys, Expr.exclusive] using Expr.exclusive_substTys e r
  | .index e i, r => by
    simp [Expr.substTys, Expr.exclusive, Expr.exclusive_substTys e r,
      Expr.exclusive_substTys i r]
  | .closure _ _ _ body, _ => by
    simpa [Expr.substTys, Expr.exclusive] using Expr.exclusive_substTys body []
  | .call f args _, r => by
    simp [Expr.substTys, Expr.exclusive, Expr.exclusive_substTys f r,
      argsExclusive_substTys args r, inoutShapes_substArgTys]
  | .letIn x _ init body, r => by
    simp [Expr.substTys, Expr.exclusive, Expr.exclusive_substTys init r,
      Expr.exclusive_substTys body (hide r x)]
  | .varIn x _ init body, r => by
    simp [Expr.substTys, Expr.exclusive, Expr.exclusive_substTys init r,
      Expr.exclusive_substTys body (hide r x)]
  | .assign ⟨_, path⟩ v, r => by
    simp [Expr.substTys, Expr.exclusive, pathExclusive_substTys path r,
      Expr.exclusive_substTys v r, shape_substPathTys]
  | .seq a b, r | .withH _ _ a b, r => by
    simp [Expr.substTys, Expr.exclusive, Expr.exclusive_substTys a r,
      Expr.exclusive_substTys b r]
  | .held _ hs body, r => by
    simp [Expr.substTys, Expr.exclusive, exprsExclusive_substTys hs r,
      Expr.exclusive_substTys body, Function.comp_def]
  | .if c _ a b, r => by
    simp [Expr.substTys, Expr.exclusive, Expr.exclusive_substTys c r,
      Expr.exclusive_substTys a r, Expr.exclusive_substTys b r]
  | .match e _ arms, r => by
    simp [Expr.substTys, Expr.exclusive, Expr.exclusive_substTys e r,
      armsExclusive_substTys arms r]
  | .for x _ e body, r => by
    simp [Expr.substTys, Expr.exclusive, Expr.exclusive_substTys e r, iterated_substTys,
      Expr.exclusive_substTys body (hide (iterated e ++ r) x)]
  | .raise e, r => by simpa [Expr.substTys, Expr.exclusive] using Expr.exclusive_substTys e r
  | .try e, r | .form _ e, r => by simpa [Expr.substTys, Expr.exclusive] using Expr.exclusive_substTys e r
  | .tryCatch e _ x h _, r => by
    simp [Expr.substTys, Expr.exclusive, Expr.exclusive_substTys e r,
      Expr.exclusive_substTys h (hide r x)]
  | .break, _ | .continue, _ => rfl
  | .loop e, r | .return e, r | .perform _ e, r => by
    simpa [Expr.substTys, Expr.exclusive] using Expr.exclusive_substTys e r
  | .while c body, r => by
    simp [Expr.substTys, Expr.exclusive, Expr.exclusive_substTys c r,
      Expr.exclusive_substTys body r]

theorem exprsExclusive_substTys :
    ∀ (es : List Expr) (r : List Shape), exprsExclusive r (substExprTys s es) = exprsExclusive r es
  | [], _ => rfl
  | e :: es, r => by
    simp [substExprTys, exprsExclusive, Expr.exclusive_substTys e r,
      exprsExclusive_substTys es r]

theorem fieldsExclusive_substTys :
    ∀ (fields : List (Name × Expr)) (r : List Shape),
      fieldsExclusive r (substFieldTys s fields) = fieldsExclusive r fields
  | [], _ => rfl
  | (_, e) :: fields, r => by
    simp [substFieldTys, fieldsExclusive, Expr.exclusive_substTys e r,
      fieldsExclusive_substTys fields r]

theorem argsExclusive_substTys :
    ∀ (args : List Arg) (r : List Shape),
      argsExclusive r (substArgTys s args) = argsExclusive r args
  | [], _ => rfl
  | .value e :: args, r => by
    simp [substArgTys, argsExclusive, Expr.exclusive_substTys e r,
      argsExclusive_substTys args r]
  | .inout ⟨_, path⟩ :: args, r => by
    simp [substArgTys, argsExclusive, pathExclusive_substTys path r,
      argsExclusive_substTys args r]

theorem pathExclusive_substTys :
    ∀ (path : List Projection) (r : List Shape),
      pathExclusive r (substPathTys s path) = pathExclusive r path
  | [], _ => rfl
  | .field _ :: path, r => by
    simpa [substPathTys, pathExclusive] using pathExclusive_substTys path r
  | .index i :: path, r => by
    simp [substPathTys, pathExclusive, Expr.exclusive_substTys i r,
      pathExclusive_substTys path r]

theorem armsExclusive_substTys :
    ∀ (arms : List Arm) (r : List Shape),
      armsExclusive r (substArmTys s arms) = armsExclusive r arms
  | [], _ => rfl
  | ⟨_, binders, g, body⟩ :: arms, r => by
    simp [substArmTys, armsExclusive, guardExclusive_substTys g (binders.foldl hide r),
      Expr.exclusive_substTys body (binders.foldl hide r), armsExclusive_substTys arms r]

theorem guardExclusive_substTys :
    ∀ (g : Option Expr) (r : List Shape), guardExclusive r (substGuardTys s g) = guardExclusive r g
  | none, _ => rfl
  | some g, r => by simp [substGuardTys, guardExclusive, Expr.exclusive_substTys g r]

end

mutual

/-- Instantiating a body's type parameters keeps its parameter names. -/
theorem Expr.distinctParams_substTys :
    ∀ e : Expr, (e.substTys s).distinctParams = e.distinctParams
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method .. => rfl
  | .record _ _ fields => fieldsDistinctParams_substTys fields
  | .variant _ _ _ es => exprsDistinctParams_substTys es
  | .list _ es => exprsDistinctParams_substTys es
  | .op _ es | .view es => exprsDistinctParams_substTys es
  | .field e _ => by
    simpa [Expr.substTys, Expr.distinctParams] using Expr.distinctParams_substTys e
  | .index e i => by
    simp [Expr.substTys, Expr.distinctParams, Expr.distinctParams_substTys e,
      Expr.distinctParams_substTys i]
  | .closure ps _ _ body => by
    simp [Expr.substTys, Expr.distinctParams, Expr.distinctParams_substTys body,
      Param.substTys, Function.comp_def]
  | .call f args _ => by
    simp [Expr.substTys, Expr.distinctParams, Expr.distinctParams_substTys f,
      argsDistinctParams_substTys args]
  | .letIn _ _ init body => by
    simp [Expr.substTys, Expr.distinctParams, Expr.distinctParams_substTys init,
      Expr.distinctParams_substTys body]
  | .varIn _ _ init body => by
    simp [Expr.substTys, Expr.distinctParams, Expr.distinctParams_substTys init,
      Expr.distinctParams_substTys body]
  | .assign ⟨_, path⟩ v => by
    simp [Expr.substTys, Expr.distinctParams, pathDistinctParams_substTys path,
      Expr.distinctParams_substTys v]
  | .seq a b | .withH _ _ a b => by
    simp [Expr.substTys, Expr.distinctParams, Expr.distinctParams_substTys a,
      Expr.distinctParams_substTys b]
  | .held _ hs body => by
    simp [Expr.substTys, Expr.distinctParams, exprsDistinctParams_substTys hs,
      Expr.distinctParams_substTys body]
  | .if c _ a b => by
    simp [Expr.substTys, Expr.distinctParams, Expr.distinctParams_substTys c,
      Expr.distinctParams_substTys a, Expr.distinctParams_substTys b]
  | .match e _ arms => by
    simp [Expr.substTys, Expr.distinctParams, Expr.distinctParams_substTys e,
      armsDistinctParams_substTys arms]
  | .for _ _ e body => by
    simp [Expr.substTys, Expr.distinctParams, Expr.distinctParams_substTys e,
      Expr.distinctParams_substTys body]
  | .raise e => by
    simpa [Expr.substTys, Expr.distinctParams] using Expr.distinctParams_substTys e
  | .try e | .form _ e => by
    simpa [Expr.substTys, Expr.distinctParams] using Expr.distinctParams_substTys e
  | .tryCatch e _ _ h _ => by
    simp [Expr.substTys, Expr.distinctParams, Expr.distinctParams_substTys e,
      Expr.distinctParams_substTys h]
  | .loop e | .return e | .perform _ e => by
    simpa [Expr.substTys, Expr.distinctParams] using Expr.distinctParams_substTys e
  | .while c body => by
    simp [Expr.substTys, Expr.distinctParams, Expr.distinctParams_substTys c,
      Expr.distinctParams_substTys body]

theorem exprsDistinctParams_substTys :
    ∀ es : List Expr, exprsDistinctParams (substExprTys s es) = exprsDistinctParams es
  | [] => rfl
  | e :: es => by
    simp [substExprTys, exprsDistinctParams, Expr.distinctParams_substTys e,
      exprsDistinctParams_substTys es]

theorem fieldsDistinctParams_substTys :
    ∀ fields : List (Name × Expr),
      fieldsDistinctParams (substFieldTys s fields) = fieldsDistinctParams fields
  | [] => rfl
  | (_, e) :: fields => by
    simp [substFieldTys, fieldsDistinctParams, Expr.distinctParams_substTys e,
      fieldsDistinctParams_substTys fields]

theorem argsDistinctParams_substTys :
    ∀ args : List Arg, argsDistinctParams (substArgTys s args) = argsDistinctParams args
  | [] => rfl
  | .value e :: args => by
    simp [substArgTys, argsDistinctParams, Expr.distinctParams_substTys e,
      argsDistinctParams_substTys args]
  | .inout ⟨_, path⟩ :: args => by
    simp [substArgTys, argsDistinctParams, pathDistinctParams_substTys path,
      argsDistinctParams_substTys args]

theorem pathDistinctParams_substTys :
    ∀ path : List Projection, pathDistinctParams (substPathTys s path) = pathDistinctParams path
  | [] => rfl
  | .field _ :: path => by
    simpa [substPathTys, pathDistinctParams] using pathDistinctParams_substTys path
  | .index i :: path => by
    simp [substPathTys, pathDistinctParams, Expr.distinctParams_substTys i,
      pathDistinctParams_substTys path]

theorem armsDistinctParams_substTys :
    ∀ arms : List Arm, armsDistinctParams (substArmTys s arms) = armsDistinctParams arms
  | [] => rfl
  | ⟨_, _, g, body⟩ :: arms => by
    simp [substArmTys, armsDistinctParams, guardDistinctParams_substTys g,
      Expr.distinctParams_substTys body, armsDistinctParams_substTys arms]

theorem guardDistinctParams_substTys :
    ∀ g : Option Expr, guardDistinctParams (substGuardTys s g) = guardDistinctParams g
  | none => rfl
  | some g => by simp [substGuardTys, guardDistinctParams, Expr.distinctParams_substTys g]

end

end Instantiation

end Stilt
